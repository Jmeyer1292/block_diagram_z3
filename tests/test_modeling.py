from fbdplc.s7xml import parse_from_file
import fbdplc.modeling as modeling

def test():
    net = parse_from_file('testdata/simple_or.xml')[0]
    program, ssa = modeling.program_model(net)
