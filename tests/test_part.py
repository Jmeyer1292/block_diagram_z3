import z3
import fbdplc.parts as parts


def _test_case(part: parts.Part, inputs, outputs):
    solver = z3.Solver()
    model = part.model()
    # First model the internal logic:
    solver.add(model)
    # Then set the user inputs and evaluate the outputs
    input_constraints = _set_inputs(part, inputs)
    solver.add(input_constraints)
    assert(solver.check() == z3.sat)
    # Then pull the model and assert that the outputs match expectations
    model = solver.model()
    assert(model.eval(z3.And(_set_inputs(part, outputs))))


def _set_inputs(part: parts.Part, args):
    return [part.var(name) == args[name] for name in args]


def test_or():
    orgate = parts.OrPart("or", 2)
    _test_case(orgate, {'in1': False, 'in2': False}, {'out': False})
    _test_case(orgate, {'in1': False, 'in2': True}, {'out': True})
    _test_case(orgate, {'in1': True, 'in2': False}, {'out': True})
    _test_case(orgate, {'in1': True, 'in2': True}, {'out': True})
