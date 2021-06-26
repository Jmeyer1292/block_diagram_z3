from fbdplc.functions import Program
from fbdplc.s7xml import parse_function_from_file
from fbdplc.modeling import program_model
import argparse


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument('paths', nargs='*')
    parser.add_argument('--verbose', action='store_true')
    return parser.parse_args()


if __name__ == '__main__':
    args = parse_args()

    program = Program('main')

    main = None
    for path in args.paths:
        print(f'Attempting to load s7xml file "{path}"')
        block = parse_function_from_file(path)
        program.blocks[block.name] = block

        if main is None:
            print(f'Setting entry point to {block.name}')
            main = block
    program.entry = main.name

    model = program_model(program)
    if args.verbose:
        print('Program Model\n----------')
        for a in model.assertions:
            print(f'{a},')
