from fbdplc.utils import namespace
from fbdplc.parts import PartModel, PartPort, PartTemplate, PortDirection
from typing import Dict
from fbdplc.graph import ScopeContext, VariableResolver
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


class BlockVariables:
    def __init__(self):
        self.input = []
        self.output = []
        self.inout = []
        self.temp = []
        self.constant = []
        self.ret = []

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
        else:
            raise RuntimeError(f'Unrecognized section enum {section}')
        data_section.append((name, datatype))

    def interface_variables(self):
        v = self.input + self.output + self.inout
        return v

    def all_variables(self):
        return self.input + self.output + self.inout + self.temp + self.constant + self.ret


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
        #  Section = Input | Output | InOut | Temp | Constant | Return
        #
        # where each section is composed of 0+ "Members"
        #  Member = (Name, Datatype)
        self.name = name
        self.variables = BlockVariables()  # includes constants
        self.networks = []


class GlobalMemory:
    def __init__(self, ctx: z3.Context):
        self.ctx = ctx
        self.ssa = VariableResolver()


class Scope:
    def __init__(self, ns: str, ctx: z3.Context, block: Block):
        self.ns = namespace(ns, block.name)
        self.name = block.name
        self.variable_iface = block.variables
        self.ctx = ctx
        # Instantiate variables for this scope
        self._variables = {}
        self.ssa = VariableResolver()

        self._make_variables(ctx)

    def _make_variables(self, ctx: z3.Context):
        for name, vtype in self.variable_iface.all_variables():
            assert(vtype == bool)
            # v = z3.Bool(namespace(self.ns, name), ctx=ctx)
            # self._variables[name] = v
            uname = self.ssa.read(name)
            handle = namespace(self.ns, uname)
            self._variables[uname] = z3.Bool(handle, ctx=ctx)

    def var(self, name):
        return self._variables[name]

    def link_call(self, part: PartModel):
        assertions = []

        # Each input is linked to the $0 instance of the variable
        # Each output is linked to the last instance
        for name, vtype in self.variable_iface.input:
            x = part.ivar(name)
            n = self.ssa.read(name, 0)
            y = self._variables[n]
            assertions.append(x == y)

        for name, vtype in self.variable_iface.output:
            x = part.ivar(name)
            n = self.read(name)
            assertions.append(x == y)

        for name, vtype in self.variable_iface.inout:
            raise NotImplementedError(
                'in-out variables in a called block interface')

        return assertions

    def read(self, name: str):
        # Read the latest intermediate variable name
        # Make sure the base name exists
        unique_name = self.ssa.read(name)
        return self._variables[unique_name]

    def write(self, name: str):
        assert name in self.ssa.list_variables()
        uname = self.ssa.write(name)
        handle = namespace(self.ns, uname)
        v = z3.Bool(handle, ctx=self.ctx)
        self._variables[uname] = v
        return v


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
        instance_name = namespace(ns, 'call_' + self.name)
        model = PartModel(instance_name)
        for v in block.variables.input:
            model.add_port(v[0], v[1], PortDirection.IN)
        for v in block.variables.output:
            model.add_port(v[0], v[1], PortDirection.OUT)
        for v in block.variables.inout:
            model.add_port(v[0], v[1], PortDirection.OUT)

        for p in self.negations:
            model.ports[p].set_negated()
        model.instantiate_ports(context)

        return model
