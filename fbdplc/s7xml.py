'''
Parse an exported TIA Portal XML file representing a function block diagram
program and parse it into its constituent graphs composed of parts and wires.
'''

from typing import List
from lxml import etree

from fbdplc.modeling import ScopeContext
from fbdplc.parts import OrPart, AndPart, CoilPart, PTriggerPart
from fbdplc.wires import NamedConnection, IdentConnection, Wire


def _remove_namespaces(root):
    for elem in root.getiterator():
        elem.tag = etree.QName(elem).localname
    etree.cleanup_namespaces(root)
    return root


def parse_network(root: etree._ElementTree) -> ScopeContext:
    ns = root.get('ID')
    wires = list(root.iter('Wires'))[0]
    parts = list(root.iter('Parts'))[0]

    context = ScopeContext()

    # PARTS = Access | Part
    # Access := A ID'd reference to an external variable
    # Part = A logical block, it has typed "ports" with given names
    for p in parts:
        p: etree._Element = p
        if p.tag == 'Access':
            uid = p.get('UId')
            access = '.'.join([s.get('Name') for s in p[0]])
            context.accesses[uid] = access
        elif p.tag == 'Part':
            uid, part = parse_part(ns, p)
            context.parts[uid] = part
        else:
            raise ValueError()

    # WIRES = Wire
    # Wire = (Con, Con, ...)
    # Con = IdentCon | NameCon
    # IdentCon = An identity connection? References an access directly.
    # NameCon = A named port of a part
    for w in wires:
        assert(w.tag == 'Wire')
        conns = []
        assert(len(w) >= 2)
        for conn in w:
            uid = conn.get('UId')
            c = None
            if conn.tag == 'NameCon':
                c = NamedConnection(uid, conn.get('Name'))
            elif conn.tag == 'IdentCon':
                c = IdentConnection(uid)
            else:
                raise ValueError(f'Unknown wire tag {conn.tag}')
            conns.append(c)

        # If there are more than 2 endpoints, break it down into
        # 2-point pairs.
        uid = w.get('UId')
        for i in range(1, len(conns)):
            new_uid = f'{uid}:{i}'
            context.wires[new_uid] = Wire(conns[0], conns[i])
    return context


def discover_networks(tree):
    networks = tree.iter('SW.Blocks.CompileUnit')

    result = []
    for r in networks:
        try:
            result.append(parse_network(r))
        finally:
            pass
    return result


def parse_or(ns, node):
    n = int(node[0].text)
    return OrPart(ns, n)


def parse_and(ns, node):
    n = int(node[0].text)
    return AndPart(ns, n)


def parse_coil(ns, node):
    return CoilPart(ns, bool, node.get('Name'))


def parse_part(ns, node):
    part_type = node.get('Name')
    uid = node.get('UId')

    dispatch = {
        'O': parse_or,
        'A': parse_and,
        'Coil': parse_coil,
        'SCoil': parse_coil,
        'RCoil': parse_coil,
        'PBox': lambda ns, _: PTriggerPart(ns)
    }

    prefix = ':'.join([ns, part_type + uid])

    return uid, dispatch[part_type](prefix, node)


def _extract_networks(tree: etree.ElementTree):
    return discover_networks(_remove_namespaces(tree))


def parse_from_file(path: str) -> List[ScopeContext]:
    tree: etree._ElementTree = etree.parse(path)
    return _extract_networks(tree)


def parse_from_string(text: str) -> List[ScopeContext]:
    tree: etree._ElementTree = etree.fromstring(text)
    return _extract_networks(tree)
