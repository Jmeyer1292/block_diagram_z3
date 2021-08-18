from fbdplc.parts import PartModel, PartPort, PartTemplate, PortDirection
from typing import Dict
from fbdplc.graph import MemoryProxy
import enum
import z3


import logging
logger = logging.getLogger(__name__)


class Program:
    def __init__(self, title: str):
        self.title = title
        self.blocks = {}
        self.entry = 'main'
        self.entry_point_db = None


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
        statics = ','.join([f'({s[0]}, {s[1]})' for s in self.statics])

        return f'VarBlock(\n\tinputs={input}\n\toutput={output}\n\tinout={inout}\n\ttemp={temp}\n\tconstant={constant}\n\tret={ret}\n\tstatics={statics}\n)'

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
            assert len(self.ret) == 0
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

    def all_local_variables(self):
        '''
        inout probably shouldn't be in here; does not include statics
        '''
        return self.input + self.output + self.inout + self.temp + self.constant + self.ret

    def type_of(self, name):
        return self.__types.get(name)

    def symbol_is_static(self, name):
        return any([name == x[0] for x in self.statics])


class Block:
    '''
    In Siemens land, a block is sort of akin to a class.
    FB blocks have state associated with them.
    FC blocks are stateless; a sort of general function call.
    '''
    BLOCK_TYPE_FC = 'FC'
    BLOCK_TYPE_FB = 'FB'
    BLOCK_TYPE_OB = 'OB'

    def __init__(self, name: str, block_type: str = BLOCK_TYPE_FC):
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
        self.block_type = block_type


class Scope:
    def __init__(self, ns: str, uid: str, ctx: z3.Context, block: Block, parent=None):
        self.ns = f'{ns}$({uid}){block.name}'
        # A unique identifier for *this* call within the given namespace, 'ns'
        self.uid = uid
        self.name = block.name
        self.variable_iface = block.variables
        self.ctx = ctx
        self.parent: Scope = parent
        self.static_access_info = None  # TODO(Jmeyer)
        self.global_mem = None  # TODO(Jmeyer)

        self.mem = MemoryProxy(self.ns, ctx)
        self._make_variables()

    def list_variables(self):
        return self.mem.list_variables()

    def _make_variables(self):
        for name, vtype in self.variable_iface.all_local_variables():
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

    def _resolver_helper(self, name: str, index, accesses, is_read):
        scope = self.static_access_info.scope
        symbol = self.static_access_info.symbol
        if self.static_access_info:

            if scope == 'LocalVariable':
                logger.debug(
                    f'LocalVariable scope detected. Deferring resolution to parent scope.')
                assert self.parent
                # Our symbol is called something different in the parent scope:
                return self.parent._resolver_helper(symbol, index, [name, ] + accesses, is_read)
            elif scope == 'GlobalVariable':
                global_symbol = '.'.join([symbol, ] + [name, ] + accesses)
                logger.debug(
                    f'Global variable found! Search for resolution has terminated! {global_symbol}')
                if self.global_mem:
                    if is_read:
                        v = self.global_mem.read(global_symbol, index)
                    else:
                        v = self.global_mem.write(global_symbol)
                    return v
                else:
                    # TODO(Jmeyer): Arrange memory scopes into trees!
                    raise NotImplementedError(
                        f'Static access to global memory {name}')
            else:
                raise NotImplementedError(
                    f'Static access info with unhandled scope {self.static_access_info}')
        else:
            logger.debug(
                f'We have no static access info for this scope and symbol "{name}". This probably means that main is a FB call')

    def read(self, name: str, index=None):
        if self.variable_iface.symbol_is_static(name):
            # When this scope was created, the parent knew where the static variables were stored (or at least the next hop).
            # We need to recursively search up the call stack until we hit the global context at which point we will have
            # reconstructed the name of the symbol in the global symbol table. *This* symbol is the one we need to return so
            # that single static assignment and other such tracking continues to function correctly.
            return self._resolver_helper(name, index, [], is_read=True)

        return self.mem.read(name, index, sort=self.variable_iface.type_of(name))

    def write(self, name: str):
        if self.variable_iface.symbol_is_static(name):
            return self._resolver_helper(name, None, [], is_read=False)

        return self.mem.write(name, sort=self.variable_iface.type_of(name))


class Call(PartTemplate):
    def __init__(self, target: str, static_memory_access=None):
        super().__init__(target)
        self.target = target
        self.static_memory_access = static_memory_access
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
