from fbdplc.s7xml import parse_from_file
import fbdplc.modeling as modeling
import z3


def symbolic_execution(program: z3.Solver, ssa: modeling.VariableResolver, inputs):
    input_constraints = []
    for key, value in inputs.items():
        input_constraints.append(z3.Bool(ssa.read(key, 0)) == value)

    try:
        program.push()
        program.add(z3.And(input_constraints))
        assert(program.check() == z3.sat)
        return program.model()
    finally:
        program.pop()


def memory_dict(model: z3.ModelRef, ssa: modeling.VariableResolver):
    mem = {}
    for k in ssa.list_variables():
        b: bool = model.eval(z3.Bool(ssa.read(k)))
        mem[k] = b
    return mem


def exec_and_compare(program: z3.Solver, ssa: modeling.VariableResolver, inputs, expected_outputs):
    model = symbolic_execution(program, ssa, inputs)
    mem = memory_dict(model, ssa)

    for o in expected_outputs:
        if not (mem[o] == expected_outputs[o]):
            msg = f'EXEC error: expected var {o} to be {expected_outputs[o]} but got {mem[o]}'
            raise AssertionError(msg)


def test_or():
    net = parse_from_file('testdata/simple_or.xml')[0]
    program, ssa = modeling.program_model(net)
    # This program has 3 named variables (i.e. not temporaries)
    assert(len(ssa.list_variables()) == 3)

    exec_and_compare(program, ssa,
                     {'ToSafety.a': True, 'ToSafety.b': True},
                     {'a_or_b': True})


def test_set():
    net = parse_from_file('testdata/simple_set.xml')[0]
    program, ssa = modeling.program_model(net)
    # This program has 3 named variables (i.e. not temporaries)
    assert(len(ssa.list_variables()) == 2)
    exec_and_compare(program, ssa,
                     {'ToSafety.reset': True, 'fault_clear': False},
                     {'fault_clear': True})
    exec_and_compare(program, ssa,
                     {'ToSafety.reset': False, 'fault_clear': False},
                     {'fault_clear': False})
    exec_and_compare(program, ssa,
                     {'ToSafety.reset': False, 'fault_clear': True},
                     {'fault_clear': True})
    exec_and_compare(program, ssa,
                     {'ToSafety.reset': True, 'fault_clear': True},
                     {'fault_clear': True})


def test_pbox():
    net = parse_from_file('testdata/simple_pbox.xml')[0]
    program, ssa = modeling.program_model(net)
    # This program has 3 named variables (i.e. not temporaries)
    assert(len(ssa.list_variables()) == 3)
    exec_and_compare(program, ssa,
                     {'a_or_b': True, 'p_trig_state': False},
                     {'rising_a_or_b': True})
    exec_and_compare(program, ssa,
                     {'a_or_b': False, 'p_trig_state': False},
                     {'rising_a_or_b': False})
    exec_and_compare(program, ssa,
                     {'a_or_b': True, 'p_trig_state': True},
                     {'rising_a_or_b': False})


def test_threeway():
    net = parse_from_file('testdata/threeway.xml')[0]
    program, ssa = modeling.program_model(net)
    print(program)
    # This program has 3 named variables (i.e. not temporaries)
    assert(len(ssa.list_variables()) == 4)
    exec_and_compare(program, ssa,
                     {'ToSafety.a': True, 'ToSafety.b': True, 'fault_clear': True},
                     {'a_and_b': True, 'fault_clear': False})
    exec_and_compare(program, ssa,
                     {'ToSafety.a': True, 'ToSafety.b': False, 'fault_clear': True},
                     {'a_and_b': False, 'fault_clear': True})
