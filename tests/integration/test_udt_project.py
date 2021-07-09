from fbdplc.analysis import exec_and_compare
from fbdplc.modeling import program_model
from fbdplc.apps import parse_s7xml
from fbdplc.functions import Program
from z3 import z3
from fbdplc.graph import MemoryProxy
from fbdplc import sorts
from fbdplc.sorts import UDTSchema, get_sort_factory, is_primitive, register_udt
from fbdplc import s7db
import glob
import pprint


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


def _process_dbs(db_files, ctx):
    # {'"Example1_DB"': {'initializers': {},
    #                'name': '"Example1_DB"',
    #                'symbols': {'box0': {'name': 'box0', 'type': '"Box"'},
    #                            'box1': {'name': 'box1', 'type': '"Box"'}}},
    mem = MemoryProxy('', ctx)
    for p in db_files:
        outline = s7db.parse_db_file(p)
        root_name: str = outline['name']
        if root_name[0] == '"':
            root_name = root_name[1:-1]

        for name, entry in outline['symbols'].items():
            sort = get_sort_factory(entry['type'])
            resolved_name = '.'.join([root_name, name])
            mem.create(resolved_name, sort)

    return mem


def _build_udts(udt_files):
    outlines = {}
    for f in udt_files:
        udt_outline = s7db.parse_udt_file(f)
        outlines[udt_outline['name']] = udt_outline

    # Transform these outlines into UDTSchemas, make sure we have definitions for everything,
    # and register them.
    for name, outline in outlines.items():
        print(f'Parsing {name}')
        _build_udt(outline, outlines)


def build_program_model(udt_files, db_files, xml_files):
    # Build the data types first:
    #   This step populates the g_udt_archive in the sorts module
    _build_udts(udt_files)
    # Then build the DBs up
    ctx = z3.Context()
    dbs = _process_dbs(db_files, ctx)
    pprint.pprint(dbs._variables)
    # Then build the actual program logic
    program = Program('udt_project')
    for f in xml_files:
        block = parse_s7xml.parse_function_from_file(f)
        program.blocks[block.name] = block
    program.entry = 'Main_Safety_RTG1'

    model = program_model(program, context=ctx, global_memory=dbs)
    exec_and_compare(model,
                     {'ToSafety.sensor_ctrl_a.request_mode': 2,
                      'ToSafety.sensor_ctrl_b.request_mode': 1,
                      'ToSafety.app.start':  True,
                      'ToSafety.app.stop':  True,
                      'faults_clear': True},
                      {'FromSafety.state.running': False})


def main():
    udt_files = glob.glob('testdata/udt_project/PLC_1/**/*.udt')
    db_files = glob.glob('testdata/udt_project/PLC_1/**/*.db')
    xml_files = glob.glob('testdata/udt_project/PLC_1/**/*.xml')

    build_program_model(udt_files, db_files, xml_files)


def test():
    main()
