from lxml import etree
import z3
from parts import *

def remove_namespaces(root):
    for elem in root.getiterator():
        elem.tag = etree.QName(elem).localname
    # Remove unused namespace declarations
    etree.cleanup_namespaces(root)
    return root

class ScopeContext:
    def __init__(self):
        self.accesses = {}
        self.parts = {}
        self.wires = {}

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

class WireConnection:
    pass

class NamedConnection(WireConnection):
    def __init__(self, target_uid:int , target_port : str):
        self.target_uid = target_uid
        self.target_port = target_port
    
    def resolve(self, context:ScopeContext):
        return context.parts[self.target_uid].resolve(self.target_port)

class IdentConnection(WireConnection):
    def __init__(self, target_uid:int):
        self.target_uid = target_uid
    
    def resolve(self, context : ScopeContext):
        return context.accesses[self.target_uid]

def resolve(conn: WireConnection, context :ScopeContext):
    if type(conn) == NamedConnection:
        return context.parts[conn.target_uid].port(conn.target_port)
    else:
        return context.accesses[conn.target_uid]

class Wire:
    def __init__(self, a, b):
        self.a = a
        self.b = b

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

def program_model(context: ScopeContext):
    print('\n\n\n')
    solver = z3.Solver()

    ssa_resolver = VariableResolver()

    # Iterate over each part:
    #   declare input and output port names,
    #   declare assertions for inner logic
    
    for uid, part in context.parts.items():
        ex = part.model(None)
        # print(part)
        if ex is not None:
            # print(f'Adding {ex}')
            solver.add(ex)
    
    print("AFTER PARTS BEFORE WIRES")
    print(solver.assertions())
    # Iterate over each wire
    for uid, wire in context.wires.items():
        # A variable read needs to be translated to the SSA form

        # A variable write also needs the SSA form translation
        # and we have some special case handling inside the coil object

        a_is_access = type(wire.a) == IdentConnection
        b_is_access = type(wire.b) == IdentConnection
        is_access = a_is_access or b_is_access
        print(f'Wire {uid}:')

        is_write = False
        write_coil : CoilPart = None
        a_is_coil = False
        if is_access and not a_is_access:
            p = context.parts[wire.a.target_uid]
            if type(p) == CoilPart:
                is_write = True
                write_coil = p
                a_is_coil = True
        if is_access and not b_is_access:
            p = context.parts[wire.b.target_uid]
            if type(p) == CoilPart:
                is_write = True
                write_coil = p
        
        if is_write:
            if a_is_coil:
                dst_name = resolve(wire.b, context)
                # src_name = resolve(wire.a, context)
            else:
                dst_name = resolve(wire.a, context)
                # src_name = resolve(wire.b, context)

            # The memory access
            prev = z3.Bool(ssa_resolver.read(dst_name))
            next = z3.Bool(ssa_resolver.write(dst_name))

            ex1 = write_coil.var('operand') == next
            ex2 = write_coil.var('_old_operand') == prev
            print(f'Adding {ex1} and {ex2}')
            solver.add(ex1)
            solver.add(ex2)
        else:
            a = resolve(wire.a, context)
            b = resolve(wire.b, context)

            if type(a) == str:
                a_var = z3.Bool(ssa_resolver.read(a))
            else:
                a_var = a.var
            
            if type(b) == str:
                b_var = z3.Bool(ssa_resolver.read(b))
            else:
                b_var = b.var
            print('Adding ', a_var == b_var)
            solver.add(a_var == b_var)
        
    return solver, ssa_resolver

def add_assumes():
    assumes = []
    assumes.append(z3.Bool('ToSafety.a') == False)
    assumes.append(z3.Bool('ToSafety.b') == False)
    return assumes


def add_covers():
    covers = []
    cover0 = z3.Bool('a_or_b')
    covers.append(cover0)
    return covers


def add_asserts(ssa):
    print(ssa.data)
    asserts = []
    a = z3.Bool(ssa.read('ToSafety.reset'))
    b = z3.Bool(ssa.read('fault_clear'))
    # result = z3.Bool('a_or_b')
    
    # If a is not true, then b can never be true
    assert0 = z3.Implies(z3.Not(a), z3.Not(b))
    print('ASSERT THAT', assert0)
    asserts.append(assert0)
    
    return z3.Or([z3.Not(a) for a in asserts]) 

def run_assertions(program, ssa):
    program.push()
    try:
        asserts = add_asserts(ssa)
        program.add(asserts)
        result = program.check()
        if result == z3.sat:
            print('FAILURE: an assertion has been violated')
            print(program.model())
        elif result == z3.unsat:
            print("SUCCESS: no paths to failing assertions")
        else:
            print('UNKNOWN: unabe to exhaustively test')
    finally:
        program.pop()

def run_covers(program):
    program.push()
    try:
        covers = add_covers()
        program.add(covers)
        result = program.check()
        if result == z3.sat:
            print('SUCCESS: covers are reachable')
            print(program.model())
        elif result == z3.unsat:
            print("FAILURE: no paths to covers")
        else:
            print('UNKNOWN: unabe to exhaustively test')
    finally:
        program.pop()

def stuff(context: ScopeContext):
    program, ssa = program_model(context)
    print(program)
    run_assertions(program, ssa)
    # run_covers(program)



def discover_networks(tree):
    networks = tree.iter('SW.Blocks.CompileUnit')

    result = []
    for r in networks:
        try:
            result.append(parse_network(r))
        finally:
            pass
    return result

tree : etree._ElementTree = etree.parse('Main_Safety_RTG1.xml')
networks = discover_networks(remove_namespaces(tree))
stuff(networks[0])
