
from fbdplc.analysis import _memory_dict, run_assertions
from fbdplc.s7xml import parse_function_from_file
from fbdplc.functions import Program
from fbdplc.modeling import program_model
import z3

import logging
logging.basicConfig()
logging.getLogger('fbdplc').setLevel(logging.INFO)


def _load_block(program: Program, target_path: str):
    block = parse_function_from_file(target_path)
    program.blocks[block.name] = block
    return block.name


def main():
    '''
    See the code in testdata/example1/
    '''
    # First create a program and load various block files into it
    program = Program('example1')
    # Note that you must set one module as the entry point for the analysis
    program.entry = _load_block(program, 'testdata/example1/Demo.xml')
    # The following line translates the XML into a model that z3 can consume
    model = program_model(program)

    # We want to write some tests against this code. You can use the model to
    # "execute" the program by writing to all of the inputs. Then you can check
    # that you got the expected results:
    # TODO

    # You can also try to prove more general things about the program.
    # Lets say we want to prove that the estop being inactive implies a stop is
    # issued:
    estop_clear = model.root.read('estop_clear')
    stop_commanded = model.root.read('stop')
    estop_implies_stop = z3.Implies(z3.Not(estop_clear), stop_commanded)

    success, counter_example = run_assertions(
        model, [], [estop_implies_stop, ])

    print(
        f'"Estop Implies Stop" Assertion Results:\nSuccess := {success}\nCounter-Example := {counter_example}')

    # Great; We've shown that indeed this is true.
    # Let's try something a little more complex: We have safety sensors that sometimes can be
    # muted, or disabled. This muting should only happen when other protective measures are
    # put in place.
    left, right, mute = [model.root.read(
        x) for x in ['left_clear', 'right_clear', 'mute_granted']]
    # The system is safe if muted or both sensors are reporting safe
    sensors_safe = z3.Or(mute, z3.And(left, right))
    sensor_failure_implies_stop = z3.Implies(
        z3.Not(sensors_safe), stop_commanded)

    success, counter_example = run_assertions(
        model, [], [sensor_failure_implies_stop, ])
    print(
        f'"Sensors Safe" Assertion Results:\nSuccess := {success}\nCounter-Example := {counter_example}')

    # Turns out this one fails. There's a typo in the program where one of the
    # sensors is using the mute_requested variable instead of the mute_granted.
    print('top level memory print out:')
    print(_memory_dict(counter_example, model.root))
    # As you can see, the right scanner is breached and the machine is moving quickly
    # so the request for mute is not granted but we still didn't command a stop.
    #   {
    #       'is_slow': False, 'left_clear': True,
    #       'right_clear': False, 'mute_req': True,
    #       'estop_clear': True, 'stop': False,
    #       'mute_granted': False, 'scanners_ok': True
    #   }


if __name__ == '__main__':
    main()
