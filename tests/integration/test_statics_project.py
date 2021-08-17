import z3
from fbdplc.modeling import ProgramModel
from fbdplc.analysis import exec_and_compare, run_assertions, run_covers, symbolic_execution
import fbdplc.project

import glob


def unit_test(program_model: ProgramModel, verbose=True):
    solver, model = symbolic_execution(
        program_model, {'MyCounter_DB0.counter': 0, 'MyCounter_DB1.counter': 0})
    print(model)

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
