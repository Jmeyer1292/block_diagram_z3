'''
Utility functions for configuring logging with the applications and tests
in this apps/ module.
'''
import logging
import argparse
import datetime


def _file_handler():
    datestr = datetime.datetime.now().strftime("%Y%m%d-%H%M%S")
    handler = logging.FileHandler(f'log_{datestr}.log')
    FORMAT = '%(asctime)s:%(filename)s:%(lineno)d:%(levelname)s: %(message)s'
    handler.setFormatter(logging.Formatter(FORMAT))
    return handler


def _stream_handler():
    handler = logging.StreamHandler()
    FORMAT = '%(asctime)s:%(filename)s:%(lineno)d:%(levelname)s: %(message)s'
    handler.setFormatter(logging.Formatter(FORMAT))
    return handler


def configure_logger(args):
    logger = logging.getLogger('fbdplc')
    # The file handler logs everything, always
    file_handler = _file_handler()
    file_handler.setLevel(logging.DEBUG)
    logger.addHandler(file_handler)

    if args.v:
        stream_handler = _stream_handler()
        stream_handler.setLevel(args.v)
        logger.addHandler(stream_handler)
    logger.setLevel(logging.DEBUG)


def add_log_arguments(parser: argparse.ArgumentParser):
    parser.add_argument(
        '--v', type=str, default='', help='Console logging level; One of [DEBUG, INFO, WARNING, ERROR]')
    return parser.parse_args()
