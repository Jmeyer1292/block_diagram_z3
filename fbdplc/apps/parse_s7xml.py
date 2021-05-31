import sys
from fbdplc.s7xml import parse_from_file
from fbdplc.modeling import program_model

if __name__ == '__main__':
    if len(sys.argv) < 2:
        print('usage: python parse_s7xml.py <PATH>')
    else:
        path = sys.argv[1]
        print(f'Attempting to load s7xml file "{path}"')
        contexts = parse_from_file(sys.argv[1])
        print(f'Parsed {len(contexts)} networks')
        solver, ssa = program_model(contexts[0])
        print(f'Program uses the following variables: {ssa.list_variables()}')
        print(f'Program Model:\n{solver.assertions()}')
