from glob import glob
from fbdplc.project import build_program_model

def main():
    # TODO(Jmeyer):
    # Pass in project build data
    #   1. Pass list of User Data Type files
    #   2. Pass list of Datablock files
    #   3. Pass list of Tag Table files
    #   4. Pass list of Function Block files
    
    # Pass meta-data about test configurations:
    #   1. Entry point for a given test
    #   2. Test name
    #   3. Test actions
    udt_srcs = glob('testdata/udt_project/PLC_1/PLC data types/*.udt')
    db_srcs = glob('testdata/udt_project/PLC_1/Program blocks/*.db')
    tag_srcs = []
    fb_srcs = glob('testdata/udt_project/PLC_1/Program blocks/*.xml')

    program = build_program_model(udt_srcs, db_srcs, tag_srcs, fb_srcs)
    print(program)

if __name__ == '__main__':
    main()
