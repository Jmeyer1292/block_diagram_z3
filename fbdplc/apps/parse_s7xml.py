from fbdplc.functions import Program
from fbdplc.s7xml import parse_function_from_file, parse_tags_from_file
from fbdplc.modeling import program_model
import fbdplc.apps.loggers as loggers

import argparse
import sys


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument('paths', nargs='*')
    parser.add_argument('--show_model', action='store_true')
    parser.add_argument('--tags', action='store_true')
    loggers.add_log_arguments(parser)
    return parser.parse_args()


if __name__ == '__main__':
    args = parse_args()
    loggers.configure_logger(args)

    if args.tags:
        for p in args.paths:
            tags = parse_tags_from_file(p)
            print(p)
            print(tags)
        sys.exit(0)
    elif not args.paths:
        print('No inputs specified. Run with --help.')
        sys.exit(0)

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
    if args.show_model:
        print('Program Model\n----------')
        for a in model.assertions:
            print(f'{a},')
