import lark

db_grammar = '''

    start: data_block

    data_block: "DATA_BLOCK" ESCAPED_STRING property? section+ "END_DATA_BLOCK" 

    property: "{" assignment+ "}"

    ?section: var_block
        |    init_block
        |    version
    
    version: "VERSION:" NUMBER

    var_block: "NON_RETAIN" "VAR" var_decl* "END_VAR"

    var_decl: NAME property? ":" TYPE ";"

    TYPE: NAME
        | ESCAPED_STRING



    init_block: "BEGIN" assignment*

    assignment: NAME ":=" literal ";"?

    SINGLE_QUOTE_STR: "\'" NAME "\'"

    literal: ESCAPED_STRING
           | NUMBER
           | SINGLE_QUOTE_STR

    %import common.ESCAPED_STRING
    %import common.CNAME -> NAME
    %import common.NUMBER
    %import common.WS
    %ignore WS
'''

parser = lark.Lark(db_grammar)

def parse_decl(decl: lark.Tree):
    assert decl.data == 'var_decl'
    # print(decl)
    entry = {'name': None, 'type': None}
    for child in decl.children:
        if isinstance(child, lark.Token):
            entry[child.type.lower()] = child.value
    return entry

def walk(tree: lark.Tree):
    assert len(tree.children) == 1
    block_root = tree.children[0]
    assert block_root.data == "data_block"

    # first child is the name
    block_name = block_root.children[0].value

    variables = {}

    for vars in tree.find_data('var_block'):
        for decl in vars.children:
            x = parse_decl(decl)
            variables[x['name']] = x
    
    for inits in tree.find_data('init_block'):
        for assignment in inits.children:
            name = assignment.children[0].value
            value = assignment.children[1].children[0].value
            print(f'{name} == {value}')
            variables.get(name)['init'] = value 

    print(variables)
    return variables

with open('testdata/test_data.db', 'r') as fh:
    txt = fh.read()
    tree = parser.parse(txt)
    print(tree.pretty())

    walk(tree)
        
