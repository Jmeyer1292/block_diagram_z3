from lxml import etree
import z3

tree : etree._ElementTree = etree.parse('Main_Safety_RTG1.xml')
print(tree)
print(type(tree))


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

class Part:
    def __init__():
        pass

    def declare_vars(self):
        pass

class OrPart(Part):
    def __init__(self, n):
        self.n = n
    
    def resolve(self, port):
        return f'or_{port}'

    def declare_vars(self):
        self._inputs = [z3.Bool(f'or_in{i}') for i in range(1, self.n + 1)]
        self._output = z3.Bool('or_out')
        return z3.Or(self._inputs) == self._output

class AndPart(Part):
    def __init__(self, n):
        self.n = n
    
    def declare_vars(self):
        self._inputs = [z3.Bool(f'and_{i}') for i in range(self.n)]
        self._output = z3.Bool('and_out')
        return z3.And(self._inputs) == self._output

class CoilPart(Part):
    def __init__(self):
        pass
    
    def declare_vars(self):
        self.input = z3.Bool('coil_in')
        self.operand = z3.Bool('coil_operand')
        return self.input == self.operand
    
    def resolve(self, port):
        return f'coil_{port}'

class PBoxPart(Part):
    def __init__(self):
        pass

def parse_or(node):
    n = int(node[0].text)
    return OrPart(n)

def parse_and(node):
    n = int(node[0].text)
    return AndPart(n)

def parse_coil(node):
    return CoilPart()

def parse_part(node):
    part_type = node.get('Name')
    uid = node.get('UId')

    dispatch = {
        'O' : parse_or,
        'A' : parse_and,
        'Coil' : parse_coil,
        'PBox': lambda node: PBoxPart(),
    }

    return uid, dispatch[part_type](node)

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



class Wire:
    def __init__(self, a, b):
        self.a = a
        self.b = b

def parse_network(root):
    print('Eval: ', root)
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
            uid, part = parse_part(p)
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
    solver = z3.Solver()

    # Iterate over each part:
    #   declare input and output port names,
    #   declare assertions for inner logic
    
    for uid, part in context.parts.items():
        ex = part.declare_vars()
        # print(part)
        if ex is not None:
            # print(f'Adding {ex}')
            solver.add(ex)
    
    # Iterate over each wire
    for uid, wire in context.wires.items():
        # add an assertian that wire.a == wire.b
        a_name = wire.a.resolve(context)
        b_name = wire.b.resolve(context)
        a = z3.Bool(a_name)
        b = z3.Bool(b_name)

        solver.add(a == b)
    return solver

def add_covers():
    pass

def add_asserts():
    pass

def stuff(context: ScopeContext):
    program: z3.Solver = program_model(context)

    program.push()
    program.add([z3.Bool('a_or_b') == True, z3.Bool('or_in1') == False, z3.Bool('or_in2') == False])
    print(program)
    result = program.check()
    print('Simplify,', z3.simplify(z3.And(program.assertions()), som=True))
    if result == z3.sat:
        print(program.model())
        print('SAT')
    elif result == z3.unsat:
        print('UNSAT, BRO')
    else:
        print('IDK')
    


def discover_networks(tree):
    networks = tree.iter('NetworkSource')

    result = []
    for r in networks:
        try:
            result.append(parse_network(r))
        except Exception as e:
            print(f'Failed parsing {r}', e)
            continue
        finally:
            pass
    return result

networks = discover_networks(remove_namespaces(tree))
stuff(networks[1])
