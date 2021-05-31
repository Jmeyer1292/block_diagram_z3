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
    return [part.evar(name) == args[name] for name in args]


def test_or():
    orgate = parts.OrPart("or", 2)
    _test_case(orgate, {'in1': False, 'in2': False}, {'out': False})
    _test_case(orgate, {'in1': False, 'in2': True}, {'out': True})
    _test_case(orgate, {'in1': True, 'in2': False}, {'out': True})
    _test_case(orgate, {'in1': True, 'in2': True}, {'out': True})


def test_or_with_not():
    orgate = parts.OrPart("or", 2)
    orgate.port('out').set_negated()
    _test_case(orgate, {'in1': False, 'in2': False}, {'out': not False})
    _test_case(orgate, {'in1': False, 'in2': True}, {'out': not True})
    _test_case(orgate, {'in1': True, 'in2': False}, {'out': not True})
    _test_case(orgate, {'in1': True, 'in2': True}, {'out': not True})


def test_ptrig():
    ptrig = parts.PTriggerPart("ptrig")
    _test_case(ptrig, {'in': False, '_old_bit': False},
               {'out': False, 'bit': False})
    _test_case(ptrig, {'in': False, '_old_bit': True},
               {'out': False, 'bit': False})
    _test_case(ptrig, {'in': True, '_old_bit': False},
               {'out': True, 'bit': True})
    _test_case(ptrig, {'in': True, '_old_bit': True},
               {'out': False, 'bit': True})
