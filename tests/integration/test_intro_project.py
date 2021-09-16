import glob
import pprint
import z3

import fbdplc.analysis
from fbdplc.modeling import ProgramModel
import fbdplc.project


def unit_test_step1(model: ProgramModel):
    # Test a case where all is well:
    fbdplc.analysis.exec_and_compare(
        model,
        # inputs
        {'DataToSafety.run': True, 'estop_clear': True},
        # outputs
        {'DataFromSafety.running': True, 'interlock': True}
    )
    # Test a case where the estop is pressed
    fbdplc.analysis.exec_and_compare(
        model,
        # inputs
        {'DataToSafety.run': True, 'estop_clear': False},
        # outputs
        {'DataFromSafety.running': False, 'interlock': False}
    )
    # Whoops... this won't work but it shows you what happens:
    # fbdplc.analysis.exec_and_compare(
    #     model,
    #     # inputs
    #     {'DataToSafety.run': False, 'estop_clear': True},
    #     # outputs
    #     {'DataFromSafety.running': False, 'interlock': True}
    # )


def assertion_step1(model: ProgramModel):
    # The optional second argument specifies whether you want the value of
    # the symbol at the start of the program (index == 0) or at the end (the default).

    # Read the initial value of estop_clear. These are just Z3 variables.
    estop_clear = model.global_mem.read('estop_clear', 0)
    # Read the final value of interlock
    interlock = model.global_mem.read('interlock')
    print(type(estop_clear), type(interlock))

    # Form your own assertion: !estop_clear -> !interlock
    estop_assertion = z3.Implies(z3.Not(estop_clear), z3.Not(interlock))

    success, counter_example = fbdplc.analysis.run_assertions(model,
                                                              [],
                                                              [estop_assertion, ])
    assert success, f"Assertion failed. Counter example: {counter_example}"

    # This assertion is expected to fail:
    # bad_assertion = z3.Implies(estop_clear, interlock)
    # success, counter_example = fbdplc.analysis.run_assertions(model,
    #                                                           [],
    #                                                           [bad_assertion, ])
    # assert success, f"Assertion failed. Counter example: {counter_example}"


def step1():
    project = fbdplc.project.ProjectContext()

    # You'll need to fill this our for your project. When possible, limit it to
    # just the files you need because we may not be able to handle anything that
    # can come out of TIA Portal. For the example, though, I use glob().
    project.udt_srcs = []
    project.db_srcs = glob.glob('testdata/intro/PLC_1/Program blocks/*.db')
    project.tag_srcs = glob.glob('testdata/intro/PLC_1/PLC tags/*.xml')
    project.fb_srcs = glob.glob('testdata/intro/PLC_1/Program blocks/*.xml')

    # In this case, we just want to look at the FB routine called 'Step1'
    # that corresponds with the picture in intro:
    project.entry_point = 'Step1'

    model = fbdplc.project.build_program_model(project)
    pprint.pprint(model.assertions)

    unit_test_step1(model)
    assertion_step1(model)


def test():
    step1()


if __name__ == '__main__':
    step1()
