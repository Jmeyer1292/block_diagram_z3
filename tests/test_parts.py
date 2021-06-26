from fbdplc.sorts import Boolean, Integer
from fbdplc.parts import AddPart, AndPart, CoilPart, GreaterThanOrEqualPart, LessThanOrEqualPart, NTriggerPart, OrPart, PTriggerPart, PartModel, PartPort, PortDirection, WordToBitsPart
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


def test_port():
    p = PartPort('foo', port_type=Boolean, direction=PortDirection.IN)
    ctx = z3.Context()
    p.instantiate(ctx)
    assert len(p.model()) == 0

    p = PartPort('bar', port_type=Boolean, direction=PortDirection.IN)
    p.set_negated()
    p.instantiate(ctx)
    assert len(p.model()) == 1


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
    part = CoilPart('coil', Boolean, 'SCoil')
    _test_case(part, {'in': True, prev('operand'): False},
               {'out': True, 'operand': True})
    _test_case(part, {'in': True, prev('operand'): True},
               {'out': True, 'operand': True})
    _test_case(part, {'in': False, prev('operand'): False},
               {'out': False, 'operand': False})
    _test_case(part, {'in': False, prev('operand'): True},
               {'out': False, 'operand': True})


def test_rcoil():
    part = CoilPart('coil', Boolean, 'RCoil')
    _test_case(part, {'in': True, prev('operand'): False},
               {'out': True, 'operand': False})
    _test_case(part, {'in': True, prev('operand'): True},
               {'out': True, 'operand': False})
    _test_case(part, {'in': False, prev('operand'): False},
               {'out': False, 'operand': False})
    _test_case(part, {'in': False, prev('operand'): True},
               {'out': False, 'operand': True})


def test_add():
    part = AddPart('add', port_type=Integer)
    _test_case(part, {'in1': 0, 'in2': 0}, {'out': 0})
    _test_case(part, {'in1': 1, 'in2': 0}, {'out': 1})
    _test_case(part, {'in1': 0, 'in2': 1}, {'out': 1})
    _test_case(part, {'in1': -1, 'in2': 1}, {'out': 0})
    _test_case(part, {'in1': -1, 'in2': -1}, {'out': -2})


def test_ptrig():
    part = PTriggerPart('ptrig')
    _test_case(part, {'in': True, prev('bit'): False},
               {'out': True, 'bit': True})
    _test_case(part, {'in': True, prev('bit'): True},
               {'out': False, 'bit': True})
    _test_case(part, {'in': False, prev('bit'): False},
               {'out': False, 'bit': False})
    _test_case(part, {'in': False, prev('bit'): True},
               {'out': False, 'bit': False})


def test_ntrig():
    part = NTriggerPart('ntrig')
    _test_case(part, {'in': True, prev('bit'): False},
               {'out': False, 'bit': True})
    _test_case(part, {'in': True, prev('bit'): True},
               {'out': False, 'bit': True})
    _test_case(part, {'in': False, prev('bit'): False},
               {'out': False, 'bit': False})
    _test_case(part, {'in': False, prev('bit'): True},
               {'out': True, 'bit': False})


def test_ge():
    part = GreaterThanOrEqualPart('ge', port_type=Integer)
    _test_case(part, {'in1': 0, 'in2': 0}, {'out': True})
    _test_case(part, {'in1': 1, 'in2': 0}, {'out': True})
    _test_case(part, {'in1': 0, 'in2': 1}, {'out': False})
    _test_case(part, {'in1': 2, 'in2': 1}, {'out': True})
    _test_case(part, {'in1': -1, 'in2': -1}, {'out': True})
    _test_case(part, {'in1': -1, 'in2': 0}, {'out': False})


def test_le():
    part = LessThanOrEqualPart('le', port_type=Integer)
    _test_case(part, {'in1': 0, 'in2': 0}, {'out': True})
    _test_case(part, {'in1': 1, 'in2': 0}, {'out': False})
    _test_case(part, {'in1': 0, 'in2': 1}, {'out': True})
    _test_case(part, {'in1': 2, 'in2': 1}, {'out': False})
    _test_case(part, {'in1': -1, 'in2': -1}, {'out': True})
    _test_case(part, {'in1': -1, 'in2': 0}, {'out': True})


def test_w_bo():
    def _helper(word: int):
        bits = {}
        for i in range(16):
            mask = 1 << i
            b = bool(word & mask)
            bits[f'OUT{i + 1}'] = b
        return bits

    part = WordToBitsPart('part', port_type=Integer)
    _test_case(part, {'IN': 0}, _helper(0))
    _test_case(part, {'IN': 1}, _helper(1))
    _test_case(part, {'IN': 5}, _helper(5))
