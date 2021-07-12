from z3.z3 import ExprRef
import fbdplc.modeling as modeling
from fbdplc.functions import Scope
from typing import List, Tuple

import z3


def symbolic_execution(program: modeling.ProgramModel, inputs) -> Tuple[z3.Solver, z3.ModelRef]:
    solver = z3.Solver(ctx=program.ctx)
    solver.add(program.assertions)

    input_constraints = []
    for key, value in inputs.items():
        # Is this variable in the local scope or global memory?
        v = None
        if key in program.root.mem.list_variables():
            # local scope:
            v = program.root.read(key, 0)
        else:
            # global: will assert if key is not in global_mem
            v = program.global_mem.read(key, 0)
        input_constraints.append(v == value)

    solver.push()
    solver.add(z3.And(input_constraints))
    assert(solver.check() == z3.sat)
    return solver, solver.model()


def exec_and_compare(program_model: modeling.ProgramModel, inputs, expected_outputs):
    _, model = symbolic_execution(program_model, inputs)

    mem = _memory_dict(model, program_model.root)
    mem.update(_memory_dict(model, program_model.global_mem))

    for o in expected_outputs:
        if not (mem[o] == expected_outputs[o]):
            msg = f'EXEC error: expected var {o} to be {expected_outputs[o]} but got {mem[o]}\n'
            msg += f'Context: {mem}\n{model}\nModel: {_}'
            raise AssertionError(msg)
    return model


def _memory_dict(model: z3.ModelRef, scope):
    mem = {}
    for k in scope.list_variables():
        v = scope.read(k)
        b: bool = model.eval(v)
        mem[k] = b
    return mem


def run_assertions(program_model: modeling.ProgramModel,
                   assumptions: List[ExprRef],
                   assertions: List[ExprRef]):
    solver = z3.Solver(ctx=program_model.ctx)
    solver.add(program_model.assertions)

    assertion_logic = z3.Or([z3.Not(a) for a in assertions])
    solver.add(assertion_logic)

    result = solver.check(assumptions)
    if result == z3.unsat:
        print('PASS: No assertions could be reached')
        return (True, None)
    elif result == z3.unknown:
        print('FAIL [UKNOWN]: z3 could not prove the assertions were unreachable')
        return (False, None)
    else:
        # sat
        print('FAIL [Proven]: One or more assertions were untrue')
        model = solver.model()

        print(f'Counter-Example: {model}')
        for a in assertions:
            r = model.evaluate(a)
            print(f'  Assertion {a} ==> {r}')

        return (False, model)


def run_covers(program_model: modeling.ProgramModel,
               assumptions: List[ExprRef],
               covers: List[ExprRef]):
    solver = z3.Solver(ctx=program_model.ctx)
    solver.add(program_model.assertions)

    cover_logic = z3.And([z3.Not(a) for a in covers])
    solver.add(cover_logic)

    result = solver.check(assumptions)
    if result == z3.sat:
        print('PASS: All covers reachable')
        return (True, solver.model())
    elif result == z3.unknown:
        print('FAIL [UKNOWN]: z3 could not prove the covers were reachable')
        return (False, None)
    else:
        # unsat
        print('FAIL [Proven]: One of the covers is not satisfiable')
        return (True, None)
