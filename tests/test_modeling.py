from typing import Tuple
from fbdplc.functions import Block, Program, Scope
from fbdplc.graph import merge_nets, merge_scopes
from fbdplc.s7xml import parse_from_file, parse_function_from_file
import fbdplc.modeling as modeling
import z3


def symbolic_execution(program: modeling.ProgramModel, inputs) -> Tuple[z3.Solver, z3.ModelRef]:
    solver = z3.Solver(ctx=program.ctx)
    solver.add(program.assertions)

    input_constraints = []
    for key, value in inputs.items():
        v = program.root.read(key)
        input_constraints.append(v == value)

    solver.push()
    solver.add(z3.And(input_constraints))
    assert(solver.check() == z3.sat)
    return solver, solver.model()


def memory_dict(model: z3.ModelRef, scope: Scope):
    mem = {}
    for k in scope.ssa.list_variables():
        v = scope.read(k)
        b: bool = model.eval(v)
        mem[k] = b
    return mem


def exec_and_compare(program_model: modeling.ProgramModel, inputs, expected_outputs):
    _, model = symbolic_execution(program_model, inputs)
    mem = memory_dict(model, program_model.root)

    for o in expected_outputs:
        if not (mem[o] == expected_outputs[o]):
            msg = f'EXEC error: expected var {o} to be {expected_outputs[o]} but got {mem[o]}'
            raise AssertionError(msg)


# def test_or():
#     net = parse_from_file('testdata/simple_or.xml')[0]
#     program, ssa = modeling.program_model(net)
#     # This program has 3 named variables (i.e. not temporaries)
#     assert(len(ssa.list_variables()) == 3)

#     exec_and_compare(program, ssa,
#                      {'ToSafety.a': True, 'ToSafety.b': True},
#                      {'a_or_b': True})


# def test_set():
#     net = parse_from_file('testdata/simple_set.xml')[0]
#     program, ssa = modeling.program_model(net)
#     assert(len(ssa.list_variables()) == 2)
#     exec_and_compare(program, ssa,
#                      {'ToSafety.reset': True, 'fault_clear': False},
#                      {'fault_clear': True})
#     exec_and_compare(program, ssa,
#                      {'ToSafety.reset': False, 'fault_clear': False},
#                      {'fault_clear': False})
#     exec_and_compare(program, ssa,
#                      {'ToSafety.reset': False, 'fault_clear': True},
#                      {'fault_clear': True})
#     exec_and_compare(program, ssa,
#                      {'ToSafety.reset': True, 'fault_clear': True},
#                      {'fault_clear': True})


# def test_pbox():
#     net = parse_from_file('testdata/simple_pbox.xml')[0]
#     program, ssa = modeling.program_model(net)
#     assert(len(ssa.list_variables()) == 3)
#     exec_and_compare(program, ssa,
#                      {'a_or_b': True, 'p_trig_state': False},
#                      {'rising_a_or_b': True})
#     exec_and_compare(program, ssa,
#                      {'a_or_b': False, 'p_trig_state': False},
#                      {'rising_a_or_b': False})
#     exec_and_compare(program, ssa,
#                      {'a_or_b': True, 'p_trig_state': True},
#                      {'rising_a_or_b': False})


# def test_threeway():
#     net = parse_from_file('testdata/threeway.xml')[0]
#     program, ssa = modeling.program_model(net)
#     assert(len(ssa.list_variables()) == 4)
#     exec_and_compare(program, ssa,
#                      {'ToSafety.a': True, 'ToSafety.b': True, 'fault_clear': True},
#                      {'a_and_b': True, 'fault_clear': False})
#     exec_and_compare(program, ssa,
#                      {'ToSafety.a': True, 'ToSafety.b': False, 'fault_clear': True},
#                      {'a_and_b': False, 'fault_clear': True})


# def test_negate():
#     net = parse_from_file('testdata/negate.xml')[0]
#     program, ssa = modeling.program_model(net)
#     assert(len(ssa.list_variables()) == 2)
#     exec_and_compare(program, ssa, {'fault_clear': True}, {
#                      'FromSafety.stop': False})
#     exec_and_compare(program, ssa, {'fault_clear': False}, {
#                      'FromSafety.stop': True})


# def test_two_assignments():
#     ''' Psuedo code:
#     t0 = a
#     t0 = !a
#     '''
#     net = parse_from_file('testdata/two_assignments.xml')[0]
#     program, ssa = modeling.program_model(net)
#     assert(len(ssa.list_variables()) == 2)
#     exec_and_compare(program, ssa, {'a': True}, {'t0': False})
#     exec_and_compare(program, ssa, {'a': False}, {'t0': True})


# def test_two_nets():
#     '''
#     The idea of this test is two test the combining of two nets in sequence:
#     '''
#     nets = parse_from_file('testdata/two_nets.xml')
#     assert(len(nets) == 2)

#     merged = merge_scopes(nets[0], nets[1])
#     program, ssa = modeling.program_model(merged)
#     assert(len(ssa.list_variables()) == 3)
#     exec_and_compare(program, ssa, {'a': True, 'out0': False}, {
#                      't0': False, 'out0': False})
#     exec_and_compare(program, ssa, {'a': False, 'out0': False}, {
#                      't0': True, 'out0': True})


# def test_constants():
#     ''' Psuedo code:
#     ton = False || ALWAYS_FALSE

#     where ALWAYS_FALSE is a constant...
#     '''
#     net = parse_from_file('testdata/constants.xml')[0]
#     program, ssa = modeling.program_model(net)
#     assert(len(ssa.list_variables()) == 2)
#     exec_and_compare(program, ssa, {'ALWAYS_FALSE': True}, {'ton': True})
#     exec_and_compare(program, ssa, {'ALWAYS_FALSE': False}, {'ton': False})


def test_fc_call():
    ''' Psuedo code:
    UserAnd(a=a, b=a, a_and_b => ton)
    '''

    program = Program('test_fc_call')
    main_block = Block('main')
    main_block.networks.append(parse_from_file('testdata/fc_call.xml')[0])
    main_block.variables.temp = [('a', bool), ('b', bool), ('ton', bool)]

    user_and_block = parse_function_from_file('testdata/UserAnd.xml')
    program.blocks[main_block.name] = main_block
    program.blocks[user_and_block.name] = user_and_block

    program_model = modeling.program_model(program)
    exec_and_compare(program_model, {'a': True, 'b': True}, {'ton': True})
    exec_and_compare(program_model, {'a': True, 'b': False}, {'ton': True})
    exec_and_compare(program_model, {'a': False, 'b': True}, {'ton': False})
    exec_and_compare(program_model, {'a': False, 'b': False}, {'ton': False})


def test_user_and():
    program = Program('test_user_and')
    user_and_block = parse_function_from_file('testdata/UserAnd.xml')
    program.blocks[user_and_block.name] = user_and_block
    program.entry = user_and_block.name
    program_model = modeling.program_model(program)

    exec_and_compare(program_model, {'a': True, 'b': True}, {'a_and_b': True})
    exec_and_compare(program_model, {'a': True, 'b': False}, {
                     'a_and_b': False})
    exec_and_compare(program_model, {'a': False, 'b': True}, {
                     'a_and_b': False})
    exec_and_compare(program_model, {'a': False, 'b': False}, {
                     'a_and_b': False})
