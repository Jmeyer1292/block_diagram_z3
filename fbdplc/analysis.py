import fbdplc.modeling as modeling
from fbdplc.functions import Scope
from typing import Tuple

import z3


def symbolic_execution(program: modeling.ProgramModel, inputs) -> Tuple[z3.Solver, z3.ModelRef]:
    solver = z3.Solver(ctx=program.ctx)
    solver.add(program.assertions)

    input_constraints = []
    for key, value in inputs.items():
        # Is this variable in the local scope or global memory?
        if key in program.root.ssa.list_variables():
            # local scope
            v = program.root.read(key, 0)
            
        else:
            # global
            v = program.global_mem.read(key, 0)
        input_constraints.append(v == value)

    solver.push()
    solver.add(z3.And(input_constraints))
    assert(solver.check() == z3.sat)
    return solver, solver.model()


def exec_and_compare(program_model: modeling.ProgramModel, inputs, expected_outputs):
    _, model = symbolic_execution(program_model, inputs)
    mem = _memory_dict(model, program_model.root)

    for o in expected_outputs:
        if not (mem[o] == expected_outputs[o]):
            msg = f'EXEC error: expected var {o} to be {expected_outputs[o]} but got {mem[o]}\n'
            msg += f'Context: {mem}\n{model}\nModel: {_}'
            raise AssertionError(msg)


def _memory_dict(model: z3.ModelRef, scope: Scope):
    mem = {}
    for k in scope.ssa.list_variables():
        v = scope.read(k)
        b: bool = model.eval(v)
        mem[k] = b
    return mem
