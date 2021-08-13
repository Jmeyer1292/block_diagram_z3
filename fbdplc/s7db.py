from typing import Dict
import lark

import logging
logger = logging.getLogger(__name__)

GRAMMAR = r'''

    start: type_block | data_block

    type_block: "TYPE" ESCAPED_STRING property? section+ "END_TYPE" 

    data_block: "DATA_BLOCK" ESCAPED_STRING property? section+ "END_DATA_BLOCK"

    property: "{" assignment+ "}"

    ?section:   struct_block
        |       version
        |       interface
        |       init_block
        |       name_block  // ???

    init_block: "BEGIN" assignment*
    
    interface:  "NON_RETAIN" (var_block | TYPE)

    var_block: "VAR" var_decl* "END_VAR"

    version: "VERSION :" NUMBER

    name_block: "NAME" ":" NAME

    struct_block: "STRUCT"i var_decl* "END_STRUCT"i ";"?

    var_decl: NAME property? ":" sort inline_assign? ";"

    ?sort: TYPE | struct_block | array_block

    array_block: "Array[" INTEGER ".." INTEGER "]" "of" TYPE

    INTEGER: DIGIT+

    inline_assign: ":=" literal
    
    TYPE: NAME
        | ESCAPED_STRING

    assignment: ASSIGNMENT_NAME ":=" literal ";"?

    SINGLE_QUOTE_STR: "'" NAME "'"
    COMMENT: "//" /[^\n]*/ "\n"
    %ignore COMMENT
    
    ?literal: ESCAPED_STRING
           | NUMBER
           | SINGLE_QUOTE_STR
           | inline_array
           | NAME

    inline_array: "[" (literal ","?)+ "]"

    ASSIGNMENT_NAME: ("_"|LETTER) ("."|"_"|LETTER| DIGIT | SUBSCRIPT)*

    SUBSCRIPT: "[" DIGIT+ "]"

    %import common.ESCAPED_STRING
    %import common.CNAME -> NAME
    %import common.LETTER
    %import common.DIGIT
    %import common.NUMBER
    %import common.WS
    %ignore WS
'''

db_parser = lark.Lark(GRAMMAR)


def iter_children_pred(predicate, iter: lark.Tree):
    for x in iter.children:
        if predicate(x):
            yield x


def _parse_array(node: lark.Tree):
    # Pull out data from an 'array_block'
    return {
        'index_begin': node.children[0].value,
        'index_end': node.children[1].value,
        'type': node.children[2].value,
    }


def _parse_decl(decl: lark.Tree):
    '''
    Parses declerations in DBs or UDTs of the "name : type" variety
    '''
    assert decl.data == 'var_decl'

    # A type is one of the following kinds:
    #   | A named "sort" (a primitive or UDT)
    SORT_NAMED = "named"
    #   | An inline structure (a UDT but declared inline)
    SORT_INLINE_STRUCT = "inline_struct"
    #   | An array of named "sorts"
    SORT_ARRAY = "array"

    entry = {'name': None, 'type': None, 'kind': None}

    def pred_names(x): return isinstance(x, lark.Token) and x.type == 'NAME'
    def pred_types(x): return isinstance(x, lark.Token) and x.type == 'TYPE'

    def pred_array(x): return isinstance(
        x, lark.Tree) and x.data == 'array_block'
    def pred_struct(x): return isinstance(
        x, lark.Tree) and x.data == 'struct_block'

    names = list(iter_children_pred(pred_names, decl))
    types = list(iter_children_pred(pred_types, decl))
    arrays = list(iter_children_pred(pred_array, decl))
    structs = list(iter_children_pred(pred_struct, decl))

    if len(names) == 1 and len(types) == 1:
        # It's a named sort and is terminal
        entry['kind'] = SORT_NAMED
        entry['name'] = names[0].value
        entry['type'] = types[0].value
        # We may also have an inline initializer
        # TODO
    elif len(names) == 1 and len(arrays) == 1:
        # It's an array
        entry['kind'] = SORT_ARRAY
        entry['name'] = names[0].value
        entry['type'] = _parse_array(arrays[0])
    elif len(names) == 1 and len(structs) == 1:
        entry['kind'] = SORT_INLINE_STRUCT
        entry['name'] = names[0].value
        struct = {}
        for cc in structs[0].children:
            x = _parse_decl(cc)
            struct[x['name']] = x
        entry['type'] = struct
        # Inline initializer TODO
    else:
        logger.debug(
            f'names {names}\ntypes {types}\narrys {arrays}\nstructs{structs}')
        raise NotImplementedError(f'Cant parse line {decl}')

    assert entry['name'] is not None
    assert entry['type'] is not None
    assert entry['kind'] is not None

    return entry


def _walk_db(tree: lark.Tree):
    logger.debug(tree.pretty())
    assert len(tree.children) == 1
    block_root = tree.children[0]
    assert block_root.data == "data_block"

    # first child is the name
    block_name = block_root.children[0].value

    variables = {}
    interfaces = list(tree.find_data('interface'))
    assert len(interfaces) == 1

    # Each interface is either a type name (TOKEN) or another tree
    # defininig an adhoc data type.
    iface_description = interfaces[0].children[0]
    if isinstance(iface_description, lark.Token):
        # A token means its a named type
        variables = iface_description.value
    elif isinstance(iface_description, lark.Tree):
        for vars in iface_description.find_data('var_block'):
            for decl in vars.children:
                x = _parse_decl(decl)
                variables[x['name']] = x
    else:
        raise RuntimeError(
            f'Unrecognized iface description type {type(iface_description)}')

    initializers = {}
    for inits in tree.find_data('init_block'):
        for assignment in inits.children:
            name = assignment.children[0].value
            value = assignment.children[1].value
            initializers[name] = value

    return {
        'name': block_name,
        'symbols': variables,
        'initializers': initializers
    }


def _walk_udt(tree: lark.Tree):
    assert len(tree.children) == 1
    block_root = tree.children[0]
    assert block_root.data == "type_block"
    # first child is the name
    block_name = block_root.children[0].value

    variables = {}

    for vars in tree.find_data('struct_block'):
        for decl in vars.children:
            x = _parse_decl(decl)
            variables[x['name']] = x

    initializers = {}
    for inits in tree.find_data('init_block'):
        for assignment in inits.children:
            name = assignment.children[0].value
            value = assignment.children[1].children[0].value
            initializers[name] = value

    return {
        'name': block_name,
        'symbols': variables,
        'initializers': initializers
    }


def _parse_file(path: str, parser: lark.Lark, transformer):
    text = ''

    with open(path, 'r', encoding='utf-8-sig') as fh:
        text = fh.read()
    return transformer(parser.parse(text))


def parse_db_file(path: str) -> Dict:
    '''
    Returns a dictionary with the following fields:
        'name' : The name of this DB
        'symbols': ONE OF
            dict: A dictionary of name -> Symbol Entry representing an adhoc data type
            str: A named type derived from a UDT or FB static instance
        'initializers': A dictionary of name to initial values

    If the type of the block is ad-hoc, then each symbol entry in 'symbols' is itself a dict:
        'name' : The symbol name
        'type': The type or "sort" of the symbol
    '''
    return _parse_file(path, db_parser, _walk_db)


def parse_udt_file(path: str):
    '''
    See ~parse_db_file() documentation; Called on a user-defined-datatype, or UDT.
    '''
    return _parse_file(path, db_parser, _walk_udt)
