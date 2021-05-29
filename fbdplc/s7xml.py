'''
Parse an exported TIA Portal XML file representing a function block diagram
program and parse it into its constituent graphs composed of parts and wires.
'''

from lxml import etree

def _remove_namespaces(root):
    for elem in root.getiterator():
        elem.tag = etree.QName(elem).localname
    etree.cleanup_namespaces(root)
    return root

def parse_network(root):
    print('Eval: ', root)
    ns = root.get('ID')
    print('ns',ns)
    wires = list(root.iter('Wires'))[0]
    parts = list(root.iter('Parts'))[0]

    context = ScopeContext()

    # PARTS = Access | Part
    # Access := A ID'd reference to an external variable
    # Part = A logical block, it has typed "ports" with given names
    for p in parts:
        p : etree._Element = p
        if p.tag == 'Access':
            uid = p.get('UId')
            access = '.'.join([s.get('Name') for s in p[0]])
            context.accesses[uid] = access
        elif p.tag == 'Part':
            uid, part = parse_part(ns,p)
            context.parts[uid] = part
        else:
            raise ValueError()

    # WIRES = Wire
    # Wire = (Con, Con)
    # Con = IdentCon | NameCon
    # IdentCon = An identity connection? References an access directly. 
    # NameCon = A named port of a part
    for w in wires:
        assert(w.tag == 'Wire')
        conns = []
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
        assert(len(conns) == 2)
        context.wires[w.get('UId')] = Wire(conns[0], conns[1]) 
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
        'O' : parse_or,
        'A' : parse_and,
        'Coil' : parse_coil,
        'SCoil' : parse_coil,
        'RCoil' : parse_coil,
        # 'PBox': lambda node: PBoxPart(),
    }

    prefix = ':'.join([ns, part_type + uid])

    return uid, dispatch[part_type](prefix, node)

tree : etree._ElementTree = etree.parse('Main_Safety_RTG1.xml')
networks = discover_networks(remove_namespaces(tree))
stuff(networks[0])
