import fbdplc.s7xml as s7mxl

def test_simple_or():
    '''
    fdb that computes "a_or_b" := Or(ToSafety.a, ToSafety.b)
    stored in testdata/simple_or.xml
    cut from a larger programs
    '''
    networks = s7mxl.parse_from_file('testdata/simple_or.xml')
    print(networks)



