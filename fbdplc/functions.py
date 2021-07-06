from fbdplc.parts import PartModel, PartPort, PartTemplate, PortDirection
from typing import Dict
from fbdplc.graph import MemoryProxy
import enum
import z3


class Program:
    def __init__(self, title: str):
        self.title = title
        self.blocks = {}
        self.entry = 'main'


class Section(enum.Enum):
    INPUT = 0
    OUTPUT = 1
    INOUT = 2
    TEMP = 3
    CONSTANT = 4
    RETURN = 5
    STATIC = 6


class BlockVariables:
    def __init__(self):
        self.input = []
        self.output = []
        self.inout = []
        self.temp = []
        self.constant = []
        self.ret = []
        # Only valid for FB block types
        self.statics = []
        self.__types = {}

    def __str__(self):
        input = ','.join([f'({s[0]}, {s[1]})' for s in self.input])
        output = ','.join([f'({s[0]}, {s[1]})' for s in self.output])
        inout = ','.join([f'({s[0]}, {s[1]})' for s in self.inout])
        temp = ','.join([f'({s[0]}, {s[1]})' for s in self.temp])
        constant = ','.join([f'({s[0]}, {s[1]})' for s in self.constant])
        ret = ','.join([f'({s[0]}, {s[1]})' for s in self.ret])

        return f'VarBlock(\n\tinputs={input}\n\toutput={output}\n\tinout={inout}\n\ttemp={temp}\n\tconstant={constant}\n\tret={ret}\n)'

    def add(self, section: Section, name: str, datatype: type):
        data_section = None
        if section == Section.INPUT:
            data_section = self.input
        elif section == Section.OUTPUT:
            data_section = self.output
        elif section == Section.INOUT:
            data_section = self.inout
        elif section == Section.TEMP:
            data_section = self.temp
        elif section == Section.CONSTANT:
            data_section == self.constant
        elif section == Section.RETURN:
            data_section = self.ret
            assert(len(self.ret) == 0)
        elif section == Section.STATIC:
            data_section = self.statics
        else:
            raise RuntimeError(f'Unrecognized section enum {section}')
        data_section.append((name, datatype))
        self.__types[name] = datatype

    def interface_variables(self):
        v = self.input + self.output + self.inout
        return v

    def all_variables(self):
        return self.input + self.output + self.inout + self.temp + self.constant + self.ret + self.statics

    def type_of(self, name):
        return self.__types.get(name)


class Block:
    '''
    In Siemens land, a block is sort of akin to a class.
    FB blocks have state associated with them.
    FC blocks are stateless; a sort of general function call.
    '''

    def __init__(self, name: str):
        pass
        # A function block has a name
        # It has an interface which tracks what variables we have.
        #  Section = Input | Output | InOut | Temp | Constant | Return | Static
        #
        # where each section is composed of 0+ "Members"
        #  Member = (Name, Datatype)
        self.name = name
        self.variables = BlockVariables()  # includes constants
        self.networks = []


class Scope:
    def __init__(self, ns: str, uid: str, ctx: z3.Context, block: Block):
        self.ns = f'{ns}$({uid}){block.name}'
        # A unique identifier for *this* call within the given namespace, 'ns'
        self.uid = uid
        self.name = block.name
        self.variable_iface = block.variables
        self.ctx = ctx

        self.mem = MemoryProxy(self.ns, ctx)
        self._make_variables(ctx)

    def list_variables(self):
        return self.mem.list_variables()

    def _make_variables(self, ctx: z3.Context):
        for name, vtype in self.variable_iface.all_variables():
            self.mem.create(name, vtype)

    def link_call(self, part: PartModel):
        assertions = []

        # Each input is linked to the $0 instance of the variable
        # Each output is linked to the last instance
        for name, vtype in self.variable_iface.input:
            # Read the port variable(s)
            x = part.ivar(name)
            y = self.mem.read(name, 0, vtype)
            assertions.append(x == y)

        for name, vtype in self.variable_iface.output:
            x = part.ivar(name)
            n = self.mem.read(name, None, vtype)
            assertions.append(x == n)

        for name, vtype in self.variable_iface.inout:
            # TODO(Jmeyer): For reference types we can either:
            #   1. Transform the function into something with no side effects
            #
            #      F(param := variable)
            #      F(__old_param := prev(variable), param => variable)
            #
            #
            #   2. Or we do the dereferencing here:
            #       f(param := variable)
            #
            #       scope.resolve(param) => variable
            #       if is_addressable(variable):   HALT
            #       else: scope.parent.resolve(variable)

            # Attempt at (1)
            next_port = part.ivar(name)
            prev_port = part.ivar(f'_old_{name}')
            # this memory interface:
            prev_instance = self.mem.read(name, 0, vtype)
            next_instance = self.mem.read(name, None, vtype)
            assertions.append(prev_port == prev_instance)
            assertions.append(next_port == next_instance)

        return assertions

    def read(self, name: str, index=None):
        return self.mem.read(name, index, sort=self.variable_iface.type_of(name))

    def write(self, name: str):
        return self.mem.write(name, sort=self.variable_iface.type_of(name))


class Call(PartTemplate):
    def __init__(self, target: str):
        super().__init__(target)
        self.target = target
        # The data structure also has info about the block type
        # and each of the parameters. Is this redundant with the
        # info in the associated call?
        self.ports: Dict[str, PartPort] = {}
        # A unique identifer for this particularly call. Needs to be statically determinable. No recursion.
        # self._block = block

        # # Need to allocate ports

    def instantiate(self, ns: str, context: z3.Context, block: Block) -> PartModel:
        instance_name = f'{ns}__call_{self.name}'
        model = PartModel(instance_name)
        for v in block.variables.input:
            model.add_port(v[0], v[1], PortDirection.IN)
        for v in block.variables.output:
            model.add_port(v[0], v[1], PortDirection.OUT)
        for v in block.variables.inout:
            model.add_port(v[0], v[1], PortDirection.OUT)
            model.add_port(f'_old_{v[0]}', v[1], PortDirection.OUT)

        for p in self.negations:
            model.ports[p].set_negated()
        model.instantiate_ports(context)

        return model
