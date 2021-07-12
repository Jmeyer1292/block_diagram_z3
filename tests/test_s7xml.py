import fbdplc.s7xml as s7mxl
from lxml import etree


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


UDT_PARSE_TEST_DATA = '''
    <Member Name="status_a" Datatype="&quot;FooBar&quot;" Accessibility="Public">
      <Sections>
        <Section Name="None">
          <Member Name="a" Datatype="Bool"/>
          <Member Name="b" Datatype="Bool"/>
          <Member Name="c" Datatype="Bool"/>
          <Member Name="d" Datatype="Bool"/>
        </Section>
      </Sections>
    </Member>
'''


def test_udt_parse():
    tree = etree.fromstring(UDT_PARSE_TEST_DATA)
    udt = s7mxl.parse_udt(tree)
    assert udt.name == '"FooBar"'
    assert len(udt.fields) == 4


def test_time_parse():
  assert s7mxl.parse_time_string('T#2S') == 2000
  assert s7mxl.parse_time_string('T#2000MS') == 2000

def test_tags0():
  tags = s7mxl.parse_tags_from_file('testdata/tags/tags0.xml')
  print(tags)