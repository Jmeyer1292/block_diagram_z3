from typing import Union
import z3
from fbdplc.parts import CoilPart, PartPort, PortDirection
from fbdplc.wires import IdentConnection, NamedConnection, Wire, WireConnection
from fbdplc.graph import ScopeContext, VariableResolver


def resolve(endpoint: WireConnection, context: ScopeContext) -> Union[PartPort, str]:
    if type(endpoint) == IdentConnection:
        return context.accesses[endpoint.target_uid]
    else:
        return context.parts[endpoint.target_uid].port(endpoint.target_port)


def program_model(context: ScopeContext):
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
            prev = z3.Bool(ssa_resolver.read(dst_name))
            next = z3.Bool(ssa_resolver.write(dst_name))

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

            if type(a) == str:
                a_var = z3.Bool(ssa_resolver.read(a))
            else:
                a_var = a.external_var()

            if type(b) == str:
                b_var = z3.Bool(ssa_resolver.read(b))
            else:
                b_var = b.external_var()
            solver.add(a_var == b_var)

    return solver, ssa_resolver
