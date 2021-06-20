from fbdplc.functions import Program
import sys
from fbdplc.s7xml import parse_from_file, parse_function_from_file
from fbdplc.modeling import program_model

if __name__ == '__main__':
    if len(sys.argv) < 2:
        print('usage: python parse_s7xml.py <PATH>')
    else:
        program = Program('main')
        
        main = None
        for path in sys.argv[1:]:

            print(f'Attempting to load s7xml file "{path}"')
            block = parse_function_from_file(path)
            program.blocks[block.name] = block

            if main is None:
                main = block    
        program.entry = main.name

        model = program_model(program)