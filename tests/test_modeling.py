import z3
from fbdplc.graph import MemoryProxy
from fbdplc.sorts import Boolean
from fbdplc.functions import Block, Program
from fbdplc.s7xml import parse_from_file, parse_function_from_file
import fbdplc.modeling as modeling
from fbdplc.analysis import exec_and_compare, run_assertions


def _load_block(program: Program, target_path: str):
    block = parse_function_from_file(target_path)
    program.blocks[block.name] = block
    return block.name


def test_or():
    program = Program('test_or')
    main_block = Block('main')
    main_block.networks.append(parse_from_file(
        'testdata/blocks/simple_or.xml')[0])
    # ToSafety.a and ToSafety.b are global variables and are, at least currently,
    # dynamically allocated. I don't verify the structure of these.
    main_block.variables.temp = [('a_or_b', Boolean)]
    program.blocks[main_block.name] = main_block
    program.entry = main_block.name

    mem = MemoryProxy('', z3.Context())
    mem.create('ToSafety.a', Boolean)
    mem.create('ToSafety.b', Boolean)

    model = modeling.program_model(program, mem.ctx, mem)
    exec_and_compare(model, {'ToSafety.a': True,
                     'ToSafety.b': True}, {'a_or_b': True})


def test_or_assertions():
    program = Program('test_or')
    main_block = Block('main')
    main_block.networks.append(parse_from_file(
        'testdata/blocks/simple_or.xml')[0])
    # ToSafety.a and ToSafety.b are global variables and are, at least currently,
    # dynamically allocated. I don't verify the structure of these.
    main_block.variables.temp = [('a_or_b', Boolean)]
    program.blocks[main_block.name] = main_block
    program.entry = main_block.name

    mem = MemoryProxy('', z3.Context())
    mem.create('ToSafety.a', Boolean)
    mem.create('ToSafety.b', Boolean)

    model = modeling.program_model(program, mem.ctx, mem)
    assertions = []
    a_or_b = model.root.read('a_or_b')
    run_assertions(model, [], [a_or_b == True])


def test_set():
    program = Program('test_set')
    # The following code builds a full program context around a snippet of XML and
    # is the "old" way of doing things. I should regen all of these tests in their
    # own complete program.
    main_block = Block('main')
    main_block.networks.append(parse_from_file(
        'testdata/blocks/simple_set.xml')[0])
    main_block.variables.temp.append(('fault_clear', Boolean))

    mem = MemoryProxy('', z3.Context())
    mem.create('ToSafety.reset', Boolean)

    program.blocks[main_block.name] = main_block
    model = modeling.program_model(program, mem.ctx, mem)

    exec_and_compare(model,
                     {'ToSafety.reset': True, 'fault_clear': False},
                     {'fault_clear': True})
    exec_and_compare(model,
                     {'ToSafety.reset': False, 'fault_clear': False},
                     {'fault_clear': False})
    exec_and_compare(model,
                     {'ToSafety.reset': False, 'fault_clear': True},
                     {'fault_clear': True})
    exec_and_compare(model,
                     {'ToSafety.reset': True, 'fault_clear': True},
                     {'fault_clear': True})


def test_pbox():
    program = Program('test_pbox')
    # The following code builds a full program context around a snippet of XML and
    # is the "old" way of doing things. I should regen all of these tests in their
    # own complete program.
    main_block = Block('main')
    main_block.networks.append(parse_from_file(
        'testdata/blocks/simple_pbox.xml')[0])
    main_block.variables.temp.extend([
        ('a_or_b', Boolean),
        ('p_trig_state', Boolean),
        ('rising_a_or_b', Boolean)])

    program.blocks[main_block.name] = main_block
    model = modeling.program_model(program)

    exec_and_compare(model,
                     {'a_or_b': True, 'p_trig_state': False},
                     {'rising_a_or_b': True})
    exec_and_compare(model,
                     {'a_or_b': False, 'p_trig_state': False},
                     {'rising_a_or_b': False})
    exec_and_compare(model,
                     {'a_or_b': True, 'p_trig_state': True},
                     {'rising_a_or_b': False})


def test_threeway():
    program = Program('test_threeway')
    # The following code builds a full program context around a snippet of XML and
    # is the "old" way of doing things. I should regen all of these tests in their
    # own complete program.
    main_block = Block('main')
    main_block.networks.append(parse_from_file(
        'testdata/blocks/threeway.xml')[0])
    main_block.variables.temp.extend([
        ('a_and_b', Boolean),
        ('fault_clear', Boolean), ])

    mem = MemoryProxy('', z3.Context())
    mem.create('ToSafety.a', Boolean)
    mem.create('ToSafety.b', Boolean)
    program.blocks[main_block.name] = main_block
    model = modeling.program_model(program, mem.ctx, mem)

    exec_and_compare(model,
                     {'ToSafety.a': True, 'ToSafety.b': True, 'fault_clear': True},
                     {'a_and_b': True, 'fault_clear': False})
    exec_and_compare(model,
                     {'ToSafety.a': True, 'ToSafety.b': False, 'fault_clear': True},
                     {'a_and_b': False, 'fault_clear': True})


def test_negate():
    program = Program('test_negate')
    # The following code builds a full program context around a snippet of XML and
    # is the "old" way of doing things. I should regen all of these tests in their
    # own complete program.
    main_block = Block('main')
    main_block.networks.append(
        parse_from_file('testdata/blocks/negate.xml')[0])
    main_block.variables.temp.extend([
        ('fault_clear', Boolean), ])

    mem = MemoryProxy('', z3.Context())
    mem.create('FromSafety.stop', Boolean)

    program.blocks[main_block.name] = main_block
    model = modeling.program_model(program, mem.ctx, mem)

    exec_and_compare(model, {'fault_clear': True}, {
                     'FromSafety.stop': False})
    exec_and_compare(model, {'fault_clear': False}, {
                     'FromSafety.stop': True})


def test_two_assignments():
    ''' Psuedo code:
    t0 = a
    t0 = !a
    '''
    program = Program('two_assignments')
    # The following code builds a full program context around a snippet of XML and
    # is the "old" way of doing things. I should regen all of these tests in their
    # own complete program.
    main_block = Block('main')
    main_block.networks.append(parse_from_file(
        'testdata/blocks/two_assignments.xml')[0])
    main_block.variables.temp.extend([
        ('a', Boolean), ('t0', Boolean), ])

    program.blocks[main_block.name] = main_block
    model = modeling.program_model(program)

    exec_and_compare(model, {'a': True}, {'t0': False})
    exec_and_compare(model, {'a': False}, {'t0': True})


def test_two_nets():
    '''
    The idea of this test is two test the combining of two nets in sequence:
    '''
    program = Program('two_nets')
    # The following code builds a full program context around a snippet of XML and
    # is the "old" way of doing things. I should regen all of these tests in their
    # own complete program.
    main_block = Block('main')
    main_block.networks.extend(parse_from_file('testdata/blocks/two_nets.xml'))
    main_block.variables.temp.extend([
        ('a', Boolean), ('t0', Boolean), ('out0', Boolean)])

    program.blocks[main_block.name] = main_block
    model = modeling.program_model(program)

    exec_and_compare(model, {'a': True, 'out0': False}, {
                     't0': False, 'out0': False})
    exec_and_compare(model, {'a': False, 'out0': False}, {
                     't0': True, 'out0': True})


# TODO(Jmeyer): After the latest refactor, this function is failing.
def test_constants():
    ''' Psuedo code:
    ton = False || ALWAYS_FALSE

    where ALWAYS_FALSE is a constant...
    '''
    program = Program('two_nets')
    # The following code builds a full program context around a snippet of XML and
    # is the "old" way of doing things. I should regen all of these tests in their
    # own complete program.
    main_block = Block('main')
    main_block.networks.extend(
        parse_from_file('testdata/blocks/constants.xml'))
    main_block.variables.temp.extend([('ton', Boolean), ])
    main_block.variables.constant.extend([('ALWAYS_FALSE', Boolean), ])
    program.blocks[main_block.name] = main_block
    model = modeling.program_model(program)

    exec_and_compare(model, {'ALWAYS_FALSE': True}, {'ton': True})
    exec_and_compare(model, {'ALWAYS_FALSE': False}, {'ton': False})


def test_fc_call():
    ''' Psuedo code:
    UserAnd(a=a, b=a, a_and_b => ton)
    '''

    program = Program('test_fc_call')
    main_block = Block('main')
    main_block.networks.append(parse_from_file(
        'testdata/blocks/fc_call.xml')[0])
    main_block.variables.temp = [
        ('a', Boolean), ('b', Boolean), ('ton', Boolean)]

    user_and_block = parse_function_from_file('testdata/blocks/UserAnd.xml')
    program.blocks[main_block.name] = main_block
    program.blocks[user_and_block.name] = user_and_block

    program_model = modeling.program_model(program)
    exec_and_compare(program_model, {'a': True, 'b': True}, {'ton': True})
    exec_and_compare(program_model, {'a': True, 'b': False}, {'ton': True})
    exec_and_compare(program_model, {'a': False, 'b': True}, {'ton': False})
    exec_and_compare(program_model, {'a': False, 'b': False}, {'ton': False})


def test_user_and():
    program = Program('test_user_and')
    user_and_block = parse_function_from_file('testdata/blocks/UserAnd.xml')
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


def test_double_and():
    def _make_double_and_cases():
        cases = []
        for a in (True, False):
            for b in (True, False):
                for c in (True, False):
                    for d in (True, False):
                        i = a and b
                        j = c and d
                        ins = {}
                        outs = {}
                        ins['a'] = a
                        ins['b'] = b
                        ins['c'] = c
                        ins['d'] = d
                        outs['i'] = i
                        outs['j'] = j
                        cases.append((ins, outs))
        return cases

    program = Program('test_double_and')
    user_and_block = parse_function_from_file('testdata/blocks/UserAnd.xml')
    double_and_block = parse_function_from_file(
        'testdata/blocks/DoubleAnd.xml')
    program.blocks[user_and_block.name] = user_and_block
    program.blocks[double_and_block.name] = double_and_block
    program.entry = double_and_block.name
    program_model = modeling.program_model(program)

    cases = _make_double_and_cases()
    for ins, outs in cases:
        exec_and_compare(program_model, ins, outs)


def test_user_set():
    program = Program('test_user_set')

    block = parse_function_from_file('testdata/blocks/UserSet.xml')
    program.blocks[block.name] = block

    main = parse_function_from_file('testdata/blocks/UserSetTest.xml')
    program.blocks[main.name] = main

    program.entry = main.name
    program_model = modeling.program_model(program)
    exec_and_compare(program_model, {'a': False, 'q': True}, {'a': True})
    exec_and_compare(program_model, {'a': False, 'q': False}, {'a': False})
    exec_and_compare(program_model, {'a': True, 'q': True}, {'a': True})
    exec_and_compare(program_model, {'a': True, 'q': False}, {'a': True})


def test_no_op():
    program = Program('test_no_op')
    _load_block(program, 'testdata/blocks/NoOp.xml')
    program.entry = _load_block(program, 'testdata/blocks/TestSuite.xml')
    model = modeling.program_model(program)
    exec_and_compare(model, {'test_nop_var': True}, {'test_nop_var': True})
    exec_and_compare(model, {'test_nop_var': False}, {'test_nop_var': False})


def test_user_add():
    program = Program('test_user_add')
    program.entry = _load_block(program, 'testdata/blocks/UserAdd.xml')
    model = modeling.program_model(program)
    exec_and_compare(model, {'a': 1, 'b': 5}, {'result': 6})


def test_sensor_examples():
    '''
    See the code in testdata/sensor/
    '''
    program = Program('sensor')
    program.entry = _load_block(program, 'testdata/sensor/RunSensors.xml')
    _load_block(program, 'testdata/sensor/UpdateSensor.xml')
    model = modeling.program_model(program)

    command_a = {
        'command_a.enable': True,
        'command_a.mute': False,
        'command_a.case': 0,
    }
    command_b = {
        'command_b.enable': True,
        'command_b.mute': False,
        'command_b.case': 0,
    }

    inputs = {}
    inputs.update(command_a)
    inputs.update(command_b)

    exec_and_compare(model, inputs, {'all_ok': True})
