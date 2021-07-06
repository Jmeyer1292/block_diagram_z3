from fbdplc import sorts
from fbdplc.sorts import UDTSchema, is_primitive, register_udt
from fbdplc import s7db
import glob


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


def _build_udts(udt_files):
    outlines = {}
    for f in udt_files:
        udt_outline = s7db.parse_udt_file(f)
        outlines[udt_outline['name']] = udt_outline

    # Transform these outlines into UDTSchemas, make sure we have definitions for everything,
    # and register them.
    print(outlines)

    for name, outline in outlines.items():
        print(f'Parsing {name}')
        _build_udt(outline, outlines)

    print('UDT Archive\n:', sorts.g_udt_archive)


def build_program_model(udt_files, db_files, xml_files):
    # Build the data types first:
    #   This step populates the g_udt_archive in the sorts module
    _build_udts(udt_files)
    # Then build the DBs up
    
    # Then build the actual program logic


def main():
    udt_files = glob.glob('testdata/udt_project/PLC_1/**/*.udt')
    db_files = glob.glob('testdata/udt_project/PLC_1/**/*.db')
    xml_files = glob.glob('testdata/udt_project/PLC_1/**/*.xml')

    build_program_model(udt_files, db_files, xml_files)


def test():
    main()
