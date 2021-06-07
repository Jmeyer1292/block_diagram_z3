

from fbdplc.s7xml import parse_block, parse_from_file, _remove_namespaces
from lxml import etree

def test():
    root = etree.parse('testdata/UserAnd.xml')
    root = _remove_namespaces(root)
    block = parse_block(root)

    print(block.name)
    print(block.variables)
    print(block.networks)