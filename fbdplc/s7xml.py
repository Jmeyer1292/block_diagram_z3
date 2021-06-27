'''
Parse an exported TIA Portal XML file representing a function block diagram
program and parse it into its constituent graphs composed of parts and wires.
'''

from fbdplc.sorts import Boolean, Integer, SORT_MAP, Time, make_schema
from fbdplc.functions import Block, Call, Section
from fbdplc.utils import namespace
from typing import List, Tuple
from lxml import etree
import re

from fbdplc.modeling import ScopeContext
from fbdplc.parts import AckGlobalPart, AddPart, BitsToWordPart, GreaterThanOrEqualPart, GreaterThanPart, LessThanOrEqualPart, LessThanPart, MovePart, NTriggerPart, OrPart, AndPart, PTriggerPart, PartTemplate, CoilPart, TOfPart, TOnPart, WordToBitsPart
from fbdplc.wires import NamedConnection, IdentConnection, Wire
from fbdplc.access import *

MATCH_TIME = re.compile(r'T#(\d+)(\w+)')


def parse_time_string(text: str) -> int:
    ''' Parses a time string, ala "T#2S", and returns the equivalent number of milliseconds '''
    m = MATCH_TIME.match(text)
    count = int(m.group(1))
    interval = m.group(2)
    INTERVALS = {
        'S': 1000,
        'MS': 1
    }

    return count * INTERVALS[interval]


def _remove_namespaces(root):
    for elem in root.getiterator():
        elem.tag = etree.QName(elem).localname
    etree.cleanup_namespaces(root)
    return root


def parse_access(node, ns: str):
    assert(node.tag == 'Access')
    scope = node.get('Scope')

    if scope == 'LocalVariable' or scope == 'GlobalVariable':
        child = node[0]
        assert(child.tag == 'Symbol')
        varname = '.'.join([s.get('Name') for s in child])
        return SymbolAccess(scope, varname)
    elif scope == 'LocalConstant':
        child = node[0]
        assert(child.tag == 'Constant')
        varname = child.get('Name')
        return SymbolConstantAccess(scope, varname)
    elif scope == 'LiteralConstant':
        child = node[0]
        assert(child.tag == 'Constant')
        type_node = child[0]
        assert(type_node.tag == 'ConstantType')
        value_node = child[1]
        assert(value_node.tag == 'ConstantValue')

        if type_node.text == 'Bool':
            v = value_node.text.lower()
            if v == 'true':
                return LiteralConstantAccess(True, Boolean)
            elif v == 'false' or v == '0':
                return LiteralConstantAccess(False, Boolean)
            else:
                raise ValueError(
                    f'Unsupported literal value {value_node.text}')
        elif type_node.text == 'Int':
            value = int(value_node.text)
            return LiteralConstantAccess(value, Integer)
        else:
            raise ValueError(
                f'Unsupported literal type {type_node.text} with value {value_node.value}')
    elif scope == 'TypedConstant':
        child = node[0]
        assert child.tag == 'Constant'
        value_node = child[0]
        assert value_node.tag == 'ConstantValue'
        # Only supporting Time values here so far
        assert value_node.text.startswith('T#')
        ms = parse_time_string(value_node.text)
        return LiteralConstantAccess(ms, Time)

    else:
        raise ValueError(f'Unimplemented scope for Access, "{scope}"')


def parse_block(tree: etree._ElementTree) -> Block:
    root = tree.getroot()
    assert(root.tag == 'Document')
    BLOCK_TAGS = ['SW.Blocks.FC', 'SW.Blocks.FB']
    block_node = [b for b in root if b.tag in BLOCK_TAGS]
    assert(len(block_node) == 1)
    return parse_function_block(block_node[0])



def parse_udt(member_node: etree._Element):
    '''
    Recurse over a data structure as declared in the Members section of a
    data blocks' variable interface.
    '''
    root_datatype = member_node.get('Datatype')

    assert root_datatype.startswith('"')  # udt
    assert len(member_node) == 1

    # TODO(Jmeyer): I need examples of deep structs to reverse engineer the format
    fields = {}
    for m in member_node[0][0]:
        assert m.tag == 'Member'
        sort = SORT_MAP[m.get('Datatype')]
        n = m.get('Name')
        fields[n] = sort
    
    return make_schema(root_datatype, fields)


def parse_function_block(root: etree._Element):
    name_node = root.iter('Name')
    block_name = list(name_node)[0].text
    # print(f'PARSING {name_node}, {block_name}')
    block = Block(block_name)
    # Variables
    iface_node = [l for l in root.iter('Interface')]
    assert(len(iface_node) == 1)
    iface_node = iface_node[0]

    TAG_MAP = {
        'Input': Section.INPUT,
        'Output': Section.OUTPUT,
        'InOut': Section.INOUT,
        'Temp': Section.TEMP,
        'Constant': Section.CONSTANT,
        'Return': Section.RETURN,
        'Static': Section.STATIC,
    }

    for section in iface_node[0]:
        section_name = section.get('Name')
        section_enum = TAG_MAP[section_name]

        for member in section:
            n = member.get('Name')
            datatype: str = member.get('Datatype')
            if datatype == 'Void':
                continue

            if datatype.startswith('"'):
                print(f'{n} has a custom data structure of type {datatype}')
                udt = parse_udt(member)
                block.variables.add(section_enum, n, udt)
            else:
                block.variables.add(section_enum, n, SORT_MAP[datatype])

    block.networks = discover_networks(root)
    # print(f'...Finished parsing block {block_name}')
    return block


def parse_call(node: etree._Element, ns: str):
    uid = node.get('UId')
    call_info = node[0]
    target = call_info.get('Name')
    return uid, Call(target)


def parse_network(root: etree._ElementTree) -> ScopeContext:
    ns = root.get('ID')
    wires = list(root.iter('Wires'))
    parts = list(root.iter('Parts'))

    # print(f'Considering network at {root}')

    context = ScopeContext(ns)
    if len(wires) == 0:
        print('NO WIRES')
        return context

    wires = wires[0]
    parts = parts[0]

    # PARTS = Access | Part | Call
    # Access := A ID'd reference to an external variable
    # Part := A logical block, it has typed "ports" with given names. A 'primitive' so to speak.
    # Call := Similar to a Part, but the implementation is user defined. Requires linking with the
    #         logic loaded from a different program.
    for p in parts:
        p: etree._Element = p
        if p.tag == 'Access':
            uid = namespace(ns, p.get('UId'))
            access = parse_access(p, ns)
            context.accesses[uid] = access
        elif p.tag == 'Part':
            this_ns = namespace(ns, p.get('UId'))
            uid, part = parse_part(this_ns, p)
            context.parts[this_ns] = part
        elif p.tag == 'Call':
            uid, call = parse_call(p, ns)
            context.calls[namespace(ns, uid)] = call
        else:
            raise ValueError(f'{p.tag}')

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
            uid = namespace(ns, conn.get('UId'))
            c = None
            if conn.tag == 'NameCon':
                c = NamedConnection(uid, conn.get('Name'))
            elif conn.tag == 'IdentCon':
                c = IdentConnection(uid)
            elif conn.tag == 'OpenCon':
                # An explicit no-op con
                continue
            else:
                raise ValueError(f'Unknown wire tag {conn.tag}')
            conns.append(c)

        # If there are more than 2 endpoints, break it down into
        # 2-point pairs.
        uid = namespace(ns, w.get('UId'))
        for i in range(1, len(conns)):
            new_uid = f'{uid}:{i}'
            context.wires[new_uid] = Wire(conns[0], conns[i])
    return context


def discover_networks(tree):
    # print(f'Discover networks: {tree}')
    networks = tree.iter('SW.Blocks.CompileUnit')

    result = []
    for r in networks:
        # print(f'Trying compile unit: {r}')
        result.append(parse_network(r))
    return result


def parse_or(ns, node):
    a = part_attributes(node)
    n = a['dimension']
    part = OrPart(ns, n)
    apply_negations(part, a['negations'])
    return part


def apply_negations(part: PartTemplate, negation_list):
    for n in negation_list:
        part.negations.add(n)


def parse_and(ns, node):
    a = part_attributes(node)
    n = a['dimension']
    part = AndPart(ns, n)
    apply_negations(part, a['negations'])
    return part


def parse_coil(ns, node):
    a = part_attributes(node)
    coil = CoilPart(ns, Boolean, node.get('Name'))
    apply_negations(coil, a['negations'])
    return coil


def parse_add(ns, node):
    a = part_attributes(node)
    add = AddPart(ns, SORT_MAP[a['type']])
    return add


def parse_ge(ns, node):
    a = part_attributes(node)
    ge = GreaterThanOrEqualPart(ns, SORT_MAP[a['type']])
    return ge


def parse_le(ns, node):
    a = part_attributes(node)
    le = LessThanOrEqualPart(ns, SORT_MAP[a['type']])
    return le


def parse_lt(ns, node):
    a = part_attributes(node)
    le = LessThanPart(ns, SORT_MAP[a['type']])
    return le


def parse_gt(ns, node):
    a = part_attributes(node)
    gt = GreaterThanPart(ns, SORT_MAP[a['type']])
    return gt


def parse_w_bo(ns, node):
    return WordToBitsPart(ns, Integer)


def parse_bo_w(ns, node):
    return BitsToWordPart(ns, Integer)


# These all require interacting with 'instance' data which is yet to be supported
def parse_ton(ns, node):
    return TOnPart(ns)


def parse_tof(ns, node):
    return TOfPart(ns)


def parse_ack_gl(ns, node):
    return AckGlobalPart(ns)


def parse_move(ns, node):
    return MovePart(ns)


def parse_part(ns, node):
    part_type = node.get('Name')
    uid = node.get('UId')

    dispatch = {
        'O': parse_or,
        'A': parse_and,
        'Coil': parse_coil,
        'SCoil': parse_coil,
        'RCoil': parse_coil,
        'Add': parse_add,
        'Ge': parse_ge,
        'Le': parse_le,
        'Lt': parse_lt,
        'W_BO': parse_w_bo,
        'BO_W': parse_bo_w,
        'PBox': lambda ns, _: PTriggerPart(ns),
        'NBox': lambda ns, _: NTriggerPart(ns),
        'TON': parse_ton,
        'Gt': parse_gt,
        'TOF': parse_tof,
        'ACK_GL': parse_ack_gl,
        'Move': parse_move,
    }

    prefix = ':'.join([ns, part_type + uid])
    name = f'({ns}){part_type}'

    return uid, dispatch[part_type](name, node)


def _extract_networks(tree: etree.ElementTree):
    return discover_networks(_remove_namespaces(tree))


def parse_from_file(path: str) -> List[ScopeContext]:
    tree: etree._ElementTree = etree.parse(path)
    return _extract_networks(tree)


def parse_from_string(text: str) -> List[ScopeContext]:
    tree: etree._ElementTree = etree.fromstring(text)
    return _extract_networks(tree)


def parse_function_from_file(path: str) -> Block:
    tree: etree._ElementTree = etree.parse(path)
    return parse_block(_remove_namespaces(tree))


def parse_function_from_text(path: str) -> Block:
    tree: etree._ElementTree = etree.fromstring(path)
    return parse_block(_remove_namespaces(tree))


def parse_from_string(text: str) -> List[ScopeContext]:
    tree: etree._ElementTree = etree.fromstring(text)
    return _extract_networks(tree)


def part_attributes(node):
    attrib = {}
    negations = []
    for c in node:
        if c.tag == 'TemplateValue' and c.get('Type') == 'Cardinality':
            attrib['dimension'] = int(c.text)
        if c.tag == 'TemplateValue' and c.get('Type') == 'Type':
            attrib['type'] = c.text
        elif c.tag == 'Negated':
            port = c.get('Name')
            if port is None:
                raise RuntimeError('No "Name" attribute in negated xml tag')
            negations.append(port)
    attrib['negations'] = negations
    return attrib
