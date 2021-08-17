'''
A library for bringing together various components to interface with and analyze a "real" exported
safety project.

The function build_program_model() is the primary entry point to this module. 
'''

from fbdplc.s7xml import parse_static_interface_from_file, parse_tags_from_file
from fbdplc.modeling import ProgramModel, program_model
from fbdplc.apps import parse_s7xml
from fbdplc.functions import Block, Program
from z3 import z3
from fbdplc.graph import MemoryProxy
from fbdplc import sorts
from fbdplc.sorts import UDTInstance, UDTSchema, get_sort_factory, register_udt
from fbdplc import s7db

import logging

logger = logging.getLogger(__name__)


def _build_udt(outline, outlines):
    name = outline['name']
    if name in sorts.g_udt_archive:
        return sorts.g_udt_archive[name]

    schema = UDTSchema(name)
    symbols = outline['symbols']
    for s in symbols.values():
        sort = s['type']
        name = s['name']
        if sort in sorts.SORT_MAP:
            # Primitive
            schema.fields[name] = sorts.SORT_MAP[sort]
        else:
            # is a UDT, but do we know about it yet?
            if sort not in sorts.g_udt_archive:
                _build_udt(outlines[sort], outlines)
            schema.fields[name] = sorts.g_udt_archive[sort]

    register_udt(schema.name, schema)
    return schema


g_counter = 0


def alloc_anonymous():
    global g_counter
    n = f'__anon_struct{g_counter}'
    g_counter += 1
    return n


def _process_dbs(db_files, ctx):
    mem = MemoryProxy('', ctx)
    for p in db_files:
        logger.debug(f'Processing {p}')
        outline = s7db.parse_db_file(p)
        root_name: str = outline['name']
        if root_name[0] == '"':
            root_name = root_name[1:-1]

        symbols = outline['symbols']

        # Is the variable interface an ad-hoc data type or a named type?
        if type(symbols) == dict:
            # Ad-hoc
            for name, entry in symbols.items():
                outlined_sort = entry['type']
                if isinstance(outlined_sort, str):
                    sort = get_sort_factory(outlined_sort)
                elif isinstance(outlined_sort, dict):
                    # This is an anonymous struct
                    assert 'name' not in outlined_sort
                    udt_proto = {
                        'name': alloc_anonymous(), 'symbols': outlined_sort}
                    udt = _build_udt(udt_proto, {})
                    register_udt(udt.name, udt)
                    sort = udt
                else:
                    raise RuntimeError(
                        f'Unrecognized type in db outline {outlined_sort} {type(outlined_sort)}')

                resolved_name = '.'.join([root_name, name])
                mem.create(resolved_name, sort)
        elif type(symbols) == str:
            # Named
            logger.debug(f'Allocating a named type {type(symbols)} {symbols}')
            sort_factory = get_sort_factory(symbols)
            mem.create(root_name, sort_factory)
        else:
            raise AssertionError(
                f'Bruh, the symbols variable needs to be either a str or dict, not {type(symbols)}')

    return mem

DEBUG_CONTINUE = True
def _build_udts(udt_files):
    outlines = {}
    for f in udt_files:
        logger.debug(f'Considering UDT file {f}')
        try:
            udt_outline = s7db.parse_udt_file(f)
            outlines[udt_outline['name']] = udt_outline
        except Exception as e:
            logger.exception(e)
            if not DEBUG_CONTINUE:
                raise
    # Transform these outlines into UDTSchemas, make sure we have definitions for everything,
    # and register them.
    for _, outline in outlines.items():
        _build_udt(outline, outlines)


def _build_fb_udts(function_files):
    '''
    Some function blocks, those labeled as "FB", may contain static data that implicitly forms a UDT with
    the name of the block.
    '''
    outlines = {}
    for f in function_files:
        logger.debug(f'Considering block file {f}')
        static_iface = parse_static_interface_from_file(f)
        if static_iface:
            outlines[static_iface['name']] = static_iface

    for iface in outlines.values():
        _build_udt(iface, outlines)


def process_tags(tag_files, mem: MemoryProxy):
    symbols = []
    for f in tag_files:
        logger.debug(f'Considering tag file {f}')
        tag_table_name, tag_table_symbols = parse_tags_from_file(f)
        symbols.extend(tag_table_symbols)

    for entry in symbols:
        name = entry[0]
        sort_text = entry[1]
        sort = get_sort_factory(sort_text)
        mem.create(name, sort)


class ProjectContext:
    '''
    Container for project data. See __init__ for details: Be sure to specify an
    entry point for the analysis.
    '''

    def __init__(self):
        # 'user data types': Be sure to export with the *.udt type
        self.udt_srcs = []
        # 'data block' files. Define global memory stores. Export with *.db type.
        self.db_srcs = []
        # 'tag files': Memory mapped IO points. Just more global memory to this
        # analysis. Has a *.xml extension.
        self.tag_srcs = []
        # 'Function block' sources: XML describing the computational graphs that you
        # draw inside TIA portal.
        self.fb_srcs = []
        # Where do we start analysis? A string corresponding to the function block
        # where we want to start.
        # The default here is the the name of the automatically generated TIA portal
        # safety task entry point.
        self.entry_point = 'Main_Safety_RTG1'
        # If your entry point routine is a block of type FB, meaning it has static data
        # associated with it, then you can additionally specify the name of the global
        # DB that backs it. If its not specified, then:
        #   1. The project will look for a db with the name f'{entry_point}_DB' and use
        #      that if it exists. Otherwise,
        #   2. A global symbol, '__main' with the type of your FB will be allocated.
        self.entry_point_db = None


def build_program_model(project: ProjectContext) -> ProgramModel:
    '''
    Given a project description, this function generates a program model which can be
    used for analysis by incorporating global symbols with executable code and returning
    a ProgramModel.

    Currently there are some global memory accesses (in z3 and in this library) so do not
    call this from multiple threads.

    TODO(JMeyer): See about creating a user data type store and making all of this thread safe.
    '''

    # First look at the data types because they may be used in all subsequent steps. Note that this
    # step populates the g_udt_archive in the sorts module and is therefore not threadsafe. It is a
    # TODO(Jmeyer) to clean this up.
    _build_udts(project.udt_srcs)

    _build_fb_udts(project.fb_srcs)

    # Loop through the data blocks (global variables) and build up the symbol table:
    ctx = z3.Context()
    mem = _process_dbs(project.db_srcs, ctx)

    # Add on the 'tags', or io mapped memory
    process_tags(project.tag_srcs, mem)

    # ... then start parsing the executable code:
    program = Program('')
    for f in project.fb_srcs:
        block = parse_s7xml.parse_function_from_file(f)
        program.blocks[block.name] = block

    program.entry = project.entry_point
    program.entry_point_db = project.entry_point_db

    program.entry_point_db = resolve_entry_point_db(mem, program)

    return program_model(program, context=ctx, global_memory=mem)


def resolve_entry_point_db(mem: MemoryProxy, program: Program) -> str:
    entry_block = program.blocks[program.entry]
    entry_is_fb = entry_block.block_type == Block.BLOCK_TYPE_FB

    if not entry_is_fb:
        return ''

    fb_udt_name = f'"{entry_block.name}"'
    # If the user did not specify an entry_db, then first try to locate a suitable one,
    # and, failing that, use a special new one.
    if program.entry_point_db:
        logger.debug(
            f'User specified entry = {program.entry} and entry db = {program.entry_point_db}')
        # Force an assert
        mem.read(program.program_entry_db)
        return program.entry_point_db
    else:
        logger.debug(
            f'User did not specify an entry DB for entry = {program.entry}')
        # Rule #1: Is there a global memory object with the name and sort of the entry point?
        expected = f'{entry_block.name}_DB'
        try:
            r = mem.read(expected)
        except AssertionError as e:
            r = None

        if isinstance(r, UDTInstance) and r.schema.name == fb_udt_name:
            logger.warning(
                f'An entry point with static data did not have a "entry_point_db" specified. Automatically assuming global memory db "{expected}" backs this entry point.')
            return expected
        # Rule #2: Create a special entry point variable
        fb_sort = get_sort_factory(fb_udt_name)
        mem.create('__main', fb_sort)
        logger.warning(
            f'An entry point with static data did not have a "entry_point_db" specified and no similarly named DB could be located. Creating "__main" to back these statics.')
        return '__main'
