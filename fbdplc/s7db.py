from typing import Dict
import lark

DB_GRAMMAR = '''

    start: data_block

    data_block: "DATA_BLOCK" ESCAPED_STRING property? section+ "END_DATA_BLOCK" 

    property: "{" assignment+ "}"

    ?section: var_block
        |    init_block
        |    version
    
    version: "VERSION :" NUMBER

    var_block: "NON_RETAIN" "VAR" var_decl* "END_VAR"

    var_decl: NAME property? ":" TYPE ";"

    TYPE: NAME
        | ESCAPED_STRING



    init_block: "BEGIN" assignment*

    assignment: ASSIGNMENT_NAME ":=" literal ";"?

    SINGLE_QUOTE_STR: "\'" NAME "\'"

    literal: ESCAPED_STRING
           | NUMBER
           | SINGLE_QUOTE_STR




    ASSIGNMENT_NAME: ("_"|LETTER) ("."|"_"|LETTER|DIGIT)*

    %import common.ESCAPED_STRING
    %import common.CNAME -> NAME
    %import common.LETTER
    %import common.DIGIT
    %import common.NUMBER
    %import common.WS
    %ignore WS
'''

db_parser = lark.Lark(DB_GRAMMAR)


def _parse_decl(decl: lark.Tree):
    assert decl.data == 'var_decl'
    # print(decl)
    entry = {'name': None, 'type': None}
    for child in decl.children:
        if isinstance(child, lark.Token):
            entry[child.type.lower()] = child.value
    return entry


def _walk(tree: lark.Tree):
    assert len(tree.children) == 1
    block_root = tree.children[0]
    assert block_root.data == "data_block"

    # first child is the name
    block_name = block_root.children[0].value

    variables = {}

    for vars in tree.find_data('var_block'):
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


def parse_db_file(path: str) -> Dict:
    '''
    Returns a dictionary with the following fields:
        'name' : The name of this DB
        'symbols': A dictionary of name -> Symbol Entry
        'initializers': A dictionary of name to initial values

    Each Symbol Entry is itself a dict:
        'name' : The symbol name
        'type': The type or "sort" of the symbol
    '''
    text = ''

    with open(path, 'r', encoding='utf-8-sig') as fh:
        text = fh.read()
    tree = db_parser.parse(text)
    symbols = _walk(tree)
    return symbols


def parse_udt_file(path: str):
    raise NotImplementedError("UDT files not yet implemented")
