from fbdplc.utils import namespace
from fbdplc.functions import Block, Call, Program, Scope
from typing import List, Union
import z3
from fbdplc.parts import CoilPart, PartModel, PartPort, PortDirection
from fbdplc.wires import IdentConnection, NamedConnection, WireConnection
from fbdplc.graph import ScopeContext, VariableResolver, merge_nets
from fbdplc.access import Access, LiteralConstantAccess, SymbolAccess, SymbolConstantAccess


class GlobalMemory:
    def __init__(self, ctx: z3.Context):
        self.ctx = ctx
        self.ssa = VariableResolver()
        self.variables = {}

    def _make(self, ir, sort: type):
        assert sort == bool
        self.variables[ir] = z3.Bool(ir, ctx=self.ctx)

    def alloc(self, name: str, sort: type):
        # assert name not in self.ssa.list_variables()
        print(f'Allocating {name} to global mem')
        ir = self.ssa.read(name)
        if ir in self.ssa.list_variables():
            print('...Already exists')
            return
        self._make(ir, sort)

    def read(self, name: str, idx=None):
        assert name in self.ssa.list_variables()
        return self.variables[self.ssa.read(name, idx=idx)]

    def write(self, name: str):
        assert name in self.ssa.list_variables()
        ir = self.ssa.write(name)
        self._make(ir, bool)
        return self.variables[ir]


class ProgramModel:
    def __init__(self):
        self.assertions = []
        self.ctx = z3.Context()
        # We need some kind of static call graph for users to write assertions against
        # or we need to accumulate annotations from the code itself.
        self.root: Scope = None
        self.global_mem = GlobalMemory(self.ctx)


class MemoryAccessProxy:
    def __init__(self, name, scope):
        self.name, self.scope = name, scope

    def __str__(self):
        return f'MemoryAccessProxy({self.name} from {self.scope})'


def _model_block(program: Program, program_model: ProgramModel, block: Block, call_stack: List):
    ns = call_stack[-1].ns
    print(f'Considering block {block.name} w/ call_stack {call_stack}')
    print(f'This block has the following scope/namespace: {ns}')

    # A block consists of an ordered sequence of networks.
    # Each network could potentially call into other blocks, in which case the translator
    # recursively descends into them and generates a model.
    #
    # Each entity within a scope has a 'uid' associated with it. This uid is unique only to
    # the scope it is contained within.
    code = merge_nets(block.networks)

    for uid, access in code.accesses.items():
        if isinstance(access, SymbolAccess) and access.scope == 'GlobalVariable':
            program_model.global_mem.alloc(access.symbol, bool)

    # Build a dictionary of instantiated parts
    callables = {}
    # So the algorithm is loop over the parts and instantiate them from our block template:
    print('--Parts--')
    for uid, part_template in code.parts.items():
        model: PartModel = part_template.instantiate(ns, program_model.ctx)
        callables[uid] = model
        program_model.assertions.extend(model.assertions)

    # We can generate the logic for all of the primitives first
    # We can generate function call instances now too.
    print('--Calls--')
    for uid, call in code.calls.items():
        next_block = program.blocks[call.target]

        # The interface to a function call in THIS scope.
        # Acts as a sort of user defined "part" that can be connected to via ports like any of
        # the primitives.
        model = call.instantiate(
            f'{ns}:({uid})', program_model.ctx, next_block)
        callables[uid] = model

        # The act of calling a function creates a new scope in which the block variables
        # associated with that scope are available in the eval of the block and are also
        # connected to the input/output variables.
        new_scope = Scope(ns, uid, program_model.ctx, next_block)
        _model_block(program, program_model, next_block,
                     call_stack + [new_scope])
        link_assertions = new_scope.link_call(model)
        program_model.assertions.extend(link_assertions)

    # Then wire it all up.
    # The wires define the program execution order, so translation to something akin to SSA
    # should be a matter of following this though.
    print('--Wires--')
    for uid, wire in code.wires.items():
        a_is_access = type(wire.a) == IdentConnection
        b_is_access = type(wire.b) == IdentConnection
        assert(not(a_is_access and b_is_access))

        # The general idea is that every endpoint is resolved to a model variable
        # When we're connecting ports, all we have to do is assert equality: The signal on the wire is the same at each end
        # When we connect to symbolic memory, however, things get more complicated:
        #   1. A symbol may be read from or written to multiple times.
        #   2. This program translates the input into a new program where each write creates a new variable
        def _resolve3(conn):
            assert(isinstance(conn, WireConnection))
            if isinstance(conn, IdentConnection):
                access = code.accesses[conn.target_uid]
                # print(f'Connection {conn} is a memory access: {access}')
                # 3 types of memory access right now:
                if isinstance(access, SymbolConstantAccess):
                    assert(False)
                elif isinstance(access, LiteralConstantAccess):
                    return access.value
                elif isinstance(access, SymbolAccess):
                    if access.scope == 'LocalVariable':
                        local: Scope = call_stack[-1]
                        # assert(access.symbol in local._variables)
                        # print(f'{local._variables}')
                        # print(f'{access.symbol}')
                        return MemoryAccessProxy(access.symbol, local)
                    elif access.scope == 'GlobalVariable':
                        return MemoryAccessProxy(access.symbol, program_model.global_mem)
                    else:
                        raise RuntimeError(
                            f'Unhandled access scope: {access.scope}')
                else:
                    raise RuntimeError(
                        f'Unhandled access type: {type(access)}')
            else:
                assert(isinstance(conn, NamedConnection))
                part_iface: PartModel = callables[conn.target_uid]
                # print(f'Connection {conn} is a part connection: {part_iface}::{conn.target_port}')
                port = part_iface.ports[conn.target_port]
                return port

        a = _resolve3(wire.a)
        # print(f'a = {a}')

        b = _resolve3(wire.b)
        # print(f'b = {b}')

        write_to_a = a_is_access and b.direction == PortDirection.OUT
        write_to_b = b_is_access and a.direction == PortDirection.OUT
        has_write_to_mem = write_to_a or write_to_b

        def get_var(resolvable):
            if isinstance(resolvable, MemoryAccessProxy):
                scope: Scope = resolvable.scope
                return scope.read(resolvable.name)
            elif isinstance(resolvable, PartPort):
                return resolvable.external_var()
            else:
                return resolvable

        def get_writeable(resolvable):
            if isinstance(resolvable, MemoryAccessProxy):
                scope: Scope = resolvable.scope
                return scope.write(resolvable.name)
            else:
                return get_var(resolvable)

        if not has_write_to_mem:
            a_var = get_var(a)
            b_var = get_var(b)
            program_model.assertions.append(a_var == b_var)
        else:
            the_access = None
            the_port = None
            the_part = None
            if a_is_access:
                the_access = a
                the_port = b
                the_part: PartModel = callables[wire.b.target_uid]
                the_port_name = wire.b.target_port
            else:
                the_access = b
                the_port = a
                the_part: PartModel = callables[wire.a.target_uid]
                the_port_name = wire.a.target_port

            _prev = get_var(the_access)
            _next = get_writeable(the_access)

            other = get_var(the_port)
            print(_next, _next.sort())
            print(other, other.sort())
            program_model.assertions.append(_next == other)

            old = f'_old_{the_port_name}'
            if old in the_part.ports:
                old_port = the_part.evar(old)
                a = _prev == old_port
                print(f'Adding {a}')
                program_model.assertions.append(a)
            else:
                print(
                    f'Mem write does not have associated old part {old}, part: {the_part}')

            # we want to connect to the port name and the special
            # _old_port_name ports.
    print('Done w/ Block')


def program_model(program: Program):
    assert isinstance(program, Program)
    # Need to load the "main" entry point and start symbolically translating the program.
    main = program.blocks[program.entry]

    program_model = ProgramModel()
    call_stack = [Scope('', '', program_model.ctx, main)]
    program_model.root = call_stack[0]
    _model_block(program, program_model, main, call_stack)
    return program_model
