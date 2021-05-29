import fbdplc.s7xml as s7mxl


def _simple_or(networks):
    assert(len(networks) == 1)


def test_simple_or_file():
    '''
    fdb that computes "a_or_b" := Or(ToSafety.a, ToSafety.b)
    stored in testdata/simple_or.xml
    cut from a larger programs
    '''
    networks = s7mxl.parse_from_file('testdata/simple_or.xml')
    _simple_or(networks)


def test_simple_or_string():
    text = ''
    with open('testdata/simple_or.xml', 'r') as fh:
        text = fh.read()

    networks = s7mxl.parse_from_string(text)
    _simple_or(networks)
