from typing import Union
import z3
from fbdplc.parts import CoilPart, PartPort
from fbdplc.wires import IdentConnection, WireConnection


class ScopeContext:
    def __init__(self):
        self.accesses = {}
        self.parts = {}
        self.wires = {}


class VariableResolver:
    def __init__(self):
        self.data = {}

    def write(self, name):
        if name in self.data:
            self.data[name] += 1
            return f'{name}_${self.data[name]}'
        else:
            self.data[name] = 0
            return f'{name}_$0'

    def read(self, name):
        data = self.data.get(name, None)
        if data is None:
            self.data[name] = 0
            data = 0
        return f'{name}_${data}'


def resolve(endpoint: WireConnection, context: ScopeContext) -> Union[PartPort, str]:
    if type(endpoint) == IdentConnection:
        return context.accesses[endpoint.target_uid]
    else:
        return context.parts[endpoint.target_uid].port(endpoint.target_port)


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
        write_coil: CoilPart = None
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
