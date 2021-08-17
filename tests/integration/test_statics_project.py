import z3
from fbdplc.modeling import ProgramModel
from fbdplc.analysis import exec_and_compare
import fbdplc.project

import glob


def unit_test(program_model: ProgramModel):
    inputs = {}
    outputs = {}

    # Test Case #1: invoking MyCounter_DB directly!
    #   Invoke MyCounter_DB0 twice with 1 and 2 respectively
    #   Invoke MyCounter_DB1 once with 3
    inputs['MyCounter_DB0.counter'] = 0
    inputs['MyCounter_DB1.counter'] = 0
    outputs['MyCounter_DB0.counter'] = 3
    outputs['MyCounter_DB1.counter'] = 3

    # Test Case #2: BlockIncrementer_DB invoked twice in a row
    #   Each invocation: .a += 1 + 2, .b += 1 + 3
    inputs['BlockIncrementer_DB.a.counter'] = 0
    inputs['BlockIncrementer_DB.b.counter'] = 0
    outputs['BlockIncrementer_DB.a.counter'] = 6
    outputs['BlockIncrementer_DB.b.counter'] = 8

    exec_and_compare(program_model, inputs, outputs)


def main():
    project = fbdplc.project.ProjectContext()

    # The source files:
    project.udt_srcs = glob.glob('testdata/statics_project/PLC_1/**/*.udt')
    project.db_srcs = glob.glob(
        'testdata/statics_project/PLC_1/Program blocks/*.db')
    project.tag_srcs = glob.glob(
        'testdata/statics_project/PLC_1/PLC tags/*.xml')
    project.fb_srcs = glob.glob(
        'testdata/statics_project/PLC_1/Program blocks/*.xml')

    print(project.udt_srcs)
    print(project.db_srcs)
    print(project.tag_srcs)
    print(project.fb_srcs)

    # Execution options:
    project.entry_point = 'Main_Safety_RTG1'

    model = fbdplc.project.build_program_model(project)

    unit_test(model)


def test():
    main()
