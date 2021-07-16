

from fbdplc.functions import Call
from fbdplc.s7xml import parse_function_from_file

import z3


def test_parse():
    block = parse_function_from_file('testdata/blocks/UserAnd.xml')
    assert block.name == 'UserAnd'
    assert len(block.variables.input) == 2
    assert len(block.variables.output) == 1
    assert len(block.variables.inout) == 0


def test_call():
    ctx = z3.Context()
    block = parse_function_from_file('testdata/blocks/UserAnd.xml')

    call0 = Call('UserAnd#0')
    model0 = call0.instantiate('', ctx, block)
    assert len(model0.ports) == 3
    print(model0.ports)
    for k in model0.ports:
        print(model0.ports[k].name)


# TODO(Jmeyer): Test scopes