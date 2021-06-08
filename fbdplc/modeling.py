from fbdplc.functions import Block, Program
from typing import List, Union
import z3
from fbdplc.parts import CoilPart, PartPort, PortDirection
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

def _model_block(program: Program, program_model: ProgramModel, ssa: VariableResolver, block: Block, call_stack: List):
    print(f'Considering block {block.name} w/ call_stack {call_stack}')
    # TODO(Jmeyer): Reduce the current call_stack to a namespace that makes each variable in this scope unique
    ns = ''
    # A block consists of an ordered sequence of networks.
    # Each network could potentially call into other blocks, in which case the translator
    # recursively descends into them and generates a model.
    #
    # Each entity within a scope has a 'uid' associated with it. This uid is unique only to
    # the scope it is contained within.
    code = merge_nets(block.networks)

    # Build a dictionary of instantiated parts

    # So the algorithm is loop over the parts and instantiate them from our block template:  
    for uid, part_template in code.parts.items():
        model = part_template.instantiate(ns, program_model.ctx)
        program_model.assertions.extend(model)
        ex = part.model()
        if ex is not None:
            solver.add(ex)

    # We can generate the logic for all of the primitives first
    # We can generate function call instances now too.
    for uid, call in code.calls.items():
        next_block = program.blocks[call.target]
        call_iface = instantiate_call_iface(next_block)
        # Create an instance of this block within this context:
        # We need to generate interfaces (e.g. ports) for these just like
        # the primitive parts seen earlier.
        _model_block(program, solver, ssa, next_block, ctx + [call _iface])

    # Then wire it all up.
     # Iterate over each wire
    for uid, wire in code.wires.items():
        # A variable read needs to be translated to the SSA form

        # A variable write also needs the SSA form translation
        # and we have some special case handling inside the coil object

        a_is_access = type(wire.a) == IdentConnection
        b_is_access = type(wire.b) == IdentConnection
        is_access = a_is_access or b_is_access
        assert(not(a_is_access and b_is_access))

        resolved_a = resolve2(wire.a, code)
        resolved_b = resolve2(wire.b, code)

        write_t_a = a_is_access and resolved_b.direction == PortDirection.OUT
        write_t_b = b_is_access and resolved_a.direction == PortDirection.OUT
        has_write = write_t_a or write_t_b

        def get_part(conn):
            assert(type(conn) == NamedConnection)
            return code.parts[conn.target_uid]

        if has_write:
            dst_name = resolved_a if a_is_access else resolved_b
            prev = z3.Bool(ssa.read(dst_name.symbol))
            next = z3.Bool(ssa.write(dst_name.symbol))

            # we want to connect to the port name and the special
            # _old_port_name ports.
            part = get_part(wire.a) if write_t_b else get_part(wire.b)
            port_name = wire.a.target_port if write_t_b else wire.b.target_port
            prev_var = part.evar(f'_old_{port_name}')
            next_var = part.evar(port_name)

            solver.add(prev_var == prev)
            solver.add(next_var == next)
        else:
            a = resolve(wire.a, code)
            b = resolve(wire.b, code)

            if isinstance(a, Access):
                if isinstance(a, (SymbolAccess, SymbolConstantAccess)):
                    a_var = z3.Bool(ssa.read(a.symbol))
                elif isinstance(a, LiteralConstantAccess):
                    a_var = a.value
            else:
                a_var = a.external_var()

            if isinstance(b, Access):
                if isinstance(b, (SymbolAccess, SymbolConstantAccess)):
                    b_var = z3.Bool(ssa.read(b.symbol))
                elif isinstance(b, LiteralConstantAccess):
                    b_var = b.value
            else:
                b_var = b.external_var()

            solver.add(a_var == b_var)


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

    ctx = []
    _model_block(program, solver, ssa_resolver, main, ctx)

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
