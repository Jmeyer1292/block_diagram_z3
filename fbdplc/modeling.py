from fbdplc.utils import namespace
from fbdplc.functions import Block, Call, Program, Scope
from typing import List, Union
import z3
from fbdplc.parts import CoilPart, PartModel, PartPort, PortDirection
from fbdplc.wires import IdentConnection, NamedConnection, Wire, WireConnection
from fbdplc.graph import ScopeContext, VariableResolver, merge_nets, merge_scopes
from fbdplc.access import Access, LiteralConstantAccess, SymbolAccess, SymbolConstantAccess

class ProgramModel:
    def __init__(self):
        self.assertions = []
        self.ctx = z3.Context()

def resolve(endpoint: WireConnection, context: ScopeContext) -> Union[PartPort, Access]:
    if type(endpoint) == IdentConnection:
        return context.accesses[endpoint.target_uid]
    else:
        return context.parts[endpoint.target_uid].port(endpoint.target_port)


def resolve2(endpoint: WireConnection, context: ScopeContext) -> Union[PartPort, Access]:
    if type(endpoint) == IdentConnection:
        return context.accesses[endpoint.target_uid]
    elif type(endpoint) == NamedConnection:
        # We're connecting to a port on a Part or Call:
        part = context.parts.get(endpoint.target_uid)
        if part is None:
            part = context.calls.get(endpoint.target_uid)
            if part is None:
                raise RuntimeError(
                    f'Unable to resolve named port reference {endpoint.target_uid}')

        return part.port(endpoint.target_port)

class MemoryAccessProxy:
    def __init__(self, name, scope):
        self.name, self.scope = name, scope
    
    def __str__(self):
        return f'MemoryAccessProxy({self.name} from {self.scope})'

def _model_block(program: Program, program_model: ProgramModel, ssa: VariableResolver, block: Block, call_stack: List):
    print(f'Considering block {block.name} w/ call_stack {call_stack}')
    # TODO(Jmeyer): Reduce the current call_stack to a namespace that makes each variable in this scope unique
    ns = '$'.join([c.name for c in call_stack])
    # A block consists of an ordered sequence of networks.
    # Each network could potentially call into other blocks, in which case the translator
    # recursively descends into them and generates a model.
    #
    # Each entity within a scope has a 'uid' associated with it. This uid is unique only to
    # the scope it is contained within.
    code = merge_nets(block.networks)
    
    # Build a dictionary of instantiated parts
    callables = {}
    # So the algorithm is loop over the parts and instantiate them from our block template:  
    print('--Parts--')
    for uid, part_template in code.parts.items():
        model : PartModel = part_template.instantiate(ns, program_model.ctx)
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
        model = call.instantiate(namespace(ns, uid), program_model.ctx, next_block)
        callables[uid] = model

        # The act of calling a function creates a new scope in which the block variables
        # associated with that scope are available in the eval of the block and are also
        # connected to the input/output variables.
        new_scope = Scope(ns, program_model.ctx, next_block)
        
        # TODO(Jmeyer): Linking is super broken
        # models = new_scope.link_call(model)
        
        _model_block(program, program_model, ssa, next_block, call_stack + [new_scope])

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
                    else:
                        raise RuntimeError(f'Unhandled access scope: {access.scope}')
                else:
                    raise RuntimeError(f'Unhandled access type: {type(access)}')
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

            program_model.assertions.append(_next == other)

            old = f'_old_{the_port_name}'
            if old in the_part.ports:
                old_port = the_part.evar(old)
                a = _prev == old_port
                print(f'Adding {a}')
                program_model.assertions.append(a)
            else:
                print(f'Mem write does not have associated old part {old}, part: {the_part}')

            # we want to connect to the port name and the special
            # _old_port_name ports.
    print('Done w/ Block')


        

def _model_program(program: Program):
    '''
    Walks the program call tree. At each function boundary, it generates a new context.

    The context is used to instantiate models:
        for p in scope.parts:
            # parts are terminal, no need to recurse
            model = p.instantiate(context)

        for c in scope.calls:
            block = program[c]
            next_context = make_new_context(c, block)
            iterate(block, context + next_context) 



        The parts in the scope are unique to that scope. When we combine scopes with a single
        function, they will also be unique.

    The context is used to verify accesses:

    The context is used to check for recursion:



    '''
    print('Model program')
    solver = z3.Solver()
    ssa_resolver = VariableResolver()

    # Need to load the "main" entry point and start symbolically translating the program.
    main = program.blocks[program.entry]

    program_model = ProgramModel()
    ctx = [Scope('', program_model.ctx, main)]
    _model_block(program, program_model, ssa_resolver, main, ctx)

    print('Program Model Finished')
    for a in program_model.assertions:
        print(a)
        print('--')

    return solver, ssa_resolver


def program_model(context):
    if isinstance(context, Program):
        return _model_program(context)

    solver = z3.Solver()
    ssa_resolver = VariableResolver()

    # Iterate over each part:
    #   declare input and output port names,
    #   declare assertions for inner logic

    for uid, part in context.parts.items():
        ex = part.model()
        # print(part)
        if ex is not None:
            # print(f'Adding {ex}')
            solver.add(ex)

    for uid, c in context.calls.items():
        print(f'Adding model for {uid} {c.target}')

    # Iterate over each wire
    for uid, wire in context.wires.items():
        # A variable read needs to be translated to the SSA form

        # A variable write also needs the SSA form translation
        # and we have some special case handling inside the coil object

        a_is_access = type(wire.a) == IdentConnection
        b_is_access = type(wire.b) == IdentConnection
        is_access = a_is_access or b_is_access
        assert(not(a_is_access and b_is_access))

        resolved_a = resolve(wire.a, context)
        resolved_b = resolve(wire.b, context)

        write_t_a = a_is_access and resolved_b.direction == PortDirection.OUT
        write_t_b = b_is_access and resolved_a.direction == PortDirection.OUT
        has_write = write_t_a or write_t_b

        def get_part(conn):
            assert(type(conn) == NamedConnection)
            return context.parts[conn.target_uid]

        if has_write:
            dst_name = resolved_a if a_is_access else resolved_b
            prev = z3.Bool(ssa_resolver.read(dst_name.symbol))
            next = z3.Bool(ssa_resolver.write(dst_name.symbol))

            # we want to connect to the port name and the special
            # _old_port_name ports.
            part = get_part(wire.a) if write_t_b else get_part(wire.b)
            port_name = wire.a.target_port if write_t_b else wire.b.target_port
            prev_var = part.evar(f'_old_{port_name}')
            next_var = part.evar(port_name)

            solver.add(prev_var == prev)
            solver.add(next_var == next)
        else:
            a = resolve(wire.a, context)
            b = resolve(wire.b, context)

            if isinstance(a, Access):
                if isinstance(a, (SymbolAccess, SymbolConstantAccess)):
                    a_var = z3.Bool(ssa_resolver.read(a.symbol))
                elif isinstance(a, LiteralConstantAccess):
                    a_var = a.value
            else:
                a_var = a.external_var()

            if isinstance(b, Access):
                if isinstance(b, (SymbolAccess, SymbolConstantAccess)):
                    b_var = z3.Bool(ssa_resolver.read(b.symbol))
                elif isinstance(b, LiteralConstantAccess):
                    b_var = b.value
            else:
                b_var = b.external_var()

            solver.add(a_var == b_var)

    return solver, ssa_resolver
