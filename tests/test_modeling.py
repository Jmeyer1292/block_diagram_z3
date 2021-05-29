from fbdplc.s7xml import parse_from_file
import fbdplc.modeling as modeling

def test():
    net = parse_from_file('testdata/simple_or.xml')[0]
    program, ssa = modeling.program_model(net)
    # This program has 3 named variables (i.e. not temporaries)
    assert(len(ssa.list_variables()) == 3)
    print(program)
