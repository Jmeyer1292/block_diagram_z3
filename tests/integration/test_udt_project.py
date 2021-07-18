import z3
from fbdplc.modeling import ProgramModel
from fbdplc.analysis import exec_and_compare, run_assertions, run_covers
import fbdplc.project

import glob


def unit_test(program_model: ProgramModel, verbose=True):
    # Symbols here are relative to memory or the entry point.
    # TODO(Jmeyer): No easy way to write inline assertions or reference deeply
    # nested variables. Consider an "in-the-comments" based approach for annotating
    # the actual program.
    exec_and_compare(program_model,
                     # Given
                     {'ToSafety.sensor_ctrl_a.request_mode': 2,
                      'ToSafety.sensor_ctrl_b.request_mode': 1,
                      'ToSafety.app.start':  True,
                      'ToSafety.app.stop':  True,
                      'faults_clear': True},
                     # Expect
                     {'FromSafety.state.running': False})

    # Attempt to prove assertions:
    # Stop => Not(running); Note that the 0 in the read of stop indicates we are asking
    # for the initial state. The final state is given by default.
    stop = program_model.global_mem.read('ToSafety.app.stop', 0)
    running = program_model.root.read('running')
    my_assertion = z3.Implies(stop, z3.Not(running))

    proved, counter_example = run_assertions(
        program_model, [], [my_assertion, ])
    assert proved, f'Counter example: {counter_example}'

    # Run a "cover" to prove a liveness property. Here we try to show that, assuming we
    # are not already running, that "running" is a reachable state.
    initial_running = program_model.root.read('running', 0)
    proved, example = run_covers(program_model,
                                 # Assume
                                 [initial_running == False],
                                 # Show that
                                 [running == True, ])
    assert proved

    if verbose and proved:
        print(f'Our cover passed with the following example:\n{example}')


def main():
    project = fbdplc.project.ProjectContext()

    # The source files:
    project.udt_srcs = glob.glob('testdata/udt_project/PLC_1/**/*.udt')
    project.db_srcs = glob.glob('testdata/udt_project/PLC_1/**/*.db')
    project.tag_srcs = []
    project.fb_srcs = glob.glob('testdata/udt_project/PLC_1/**/*.xml')

    # Execution options:
    project.entry_point = 'Main_Safety_RTG1'

    model = fbdplc.project.build_program_model(project)

    unit_test(model)


def test():
    main()
