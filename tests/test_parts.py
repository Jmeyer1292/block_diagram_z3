from fbdplc.parts import AndPart, CoilPart, OrPart, PartModel
import z3


def _set_variables(part: PartModel, args):
    return [part.evar(name) == args[name] for name in args]


def _test_case(part, inputs, outputs):
    ctx = z3.Context()
    solver = z3.Solver(ctx=ctx)
    part_model = part.instantiate('', ctx)
    # First model the internal logic:
    for a in part_model.assertions:
        solver.add(a)

    # Then set the user inputs and evaluate the outputs
    input_constraints = _set_variables(part_model, inputs)
    solver.add(input_constraints)
    assert(solver.check() == z3.sat)

    # Then pull the model and assert that the outputs match expectations
    model = solver.model()
    assert(model.eval(z3.And(_set_variables(part_model, outputs))))


def test_bad_model():
    or_part = OrPart('or0', 2)
    try:
        _test_case(or_part, {'in1': True, 'in2': True}, {'out': False})
    except AssertionError as e:
        # Expected
        return True
    else:
        raise RuntimeError('Expected an exception but did not get one')


def prev(name: str) -> str:
    return f'_old_{name}'


def test_or():
    or_part = OrPart('or0', 2)
    _test_case(or_part, {'in1': True, 'in2': True}, {'out': True})
    _test_case(or_part, {'in1': False, 'in2': True}, {'out': True})
    _test_case(or_part, {'in1': True, 'in2': False}, {'out': True})
    _test_case(or_part, {'in1': False, 'in2': False}, {'out': False})


def test_and():
    part = AndPart('and0', 2)
    _test_case(part, {'in1': True, 'in2': True}, {'out': True})
    _test_case(part, {'in1': False, 'in2': True}, {'out': False})
    _test_case(part, {'in1': True, 'in2': False}, {'out': False})
    _test_case(part, {'in1': False, 'in2': False}, {'out': False})


def test_coil():
    part = CoilPart('coil')
    _test_case(part, {'in': True}, {'out': True, 'operand': True})
    _test_case(part, {'in': False}, {'out': False, 'operand': False})


def test_scoil():
    part = CoilPart('coil', bool, 'SCoil')
    _test_case(part, {'in': True, prev('operand'): False},
               {'out': True, 'operand': True})
    _test_case(part, {'in': True, prev('operand'): True},
               {'out': True, 'operand': True})
    _test_case(part, {'in': False, prev('operand'): False},
               {'out': False, 'operand': False})
    _test_case(part, {'in': False, prev('operand'): True},
               {'out': False, 'operand': True})


def test_rcoil():
    part = CoilPart('coil', bool, 'RCoil')
    _test_case(part, {'in': True, prev('operand'): False},
               {'out': True, 'operand': False})
    _test_case(part, {'in': True, prev('operand'): True},
               {'out': True, 'operand': False})
    _test_case(part, {'in': False, prev('operand'): False},
               {'out': False, 'operand': False})
    _test_case(part, {'in': False, prev('operand'): True},
               {'out': False, 'operand': True})
