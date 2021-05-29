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
        assert(mem[o] == expected_outputs[o])


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
    # print(program)
