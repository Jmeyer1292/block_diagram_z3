'''
A library for bringing together various components to interface with and analyze a "real" exported
safety project.

The function build_program_model() is the primary entry point to this module. 
'''

from fbdplc.s7xml import parse_static_interface_from_file, parse_tags_from_file
from fbdplc.modeling import ProgramModel, program_model
from fbdplc.apps import parse_s7xml
from fbdplc.functions import Program
from z3 import z3
from fbdplc.graph import MemoryProxy
from fbdplc import sorts
from fbdplc.sorts import UDTSchema, get_sort_factory, register_udt
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


def _build_udts(udt_files):
    outlines = {}
    for f in udt_files:
        udt_outline = s7db.parse_udt_file(f)
        outlines[udt_outline['name']] = udt_outline

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
    return program_model(program, context=ctx, global_memory=mem)
