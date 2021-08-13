import argparse
import fbdplc.s7db
import pprint

import logging


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument('paths', nargs='*')
    parser.add_argument('--v', type=str, default='')
    parser.add_argument(
        '--parser', choices=['guess', 'db', 'udt'], default='guess')
    return parser.parse_args()


def configure_logger(args):
    if not args.v:
        return
    logger = logging.getLogger('fbdplc')
    logger.setLevel(args.v)
    handler = logging.StreamHandler()
    FORMAT = '%(asctime)s:%(filename)s:%(lineno)d:%(levelname)s: %(message)s'
    handler.setFormatter(logging.Formatter(FORMAT))
    handler.setLevel(args.v)
    logger.addHandler(handler)


if __name__ == '__main__':
    args = parse_args()
    configure_logger(args)

    ACTIONS = {
        'db': fbdplc.s7db.parse_db_file,
        'udt': fbdplc.s7db.parse_udt_file,
    }

    for path in args.paths:
        print(f'Attempting to load s7db file "{path}"')
        action = args.parser
        if action == 'guess':
            if path.endswith('db'):
                action = 'db'
            elif path.endswith('udt'):
                action = 'udt'
            else:
                raise RuntimeError(
                    f'Unable to guess type of file w/ path {path}')

        parser = ACTIONS[action]
        result = parser(path)
        pprint.pprint(result)
