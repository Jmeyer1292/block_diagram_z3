from fbdplc.graph import merge_scopes
from fbdplc.s7xml import parse_from_file
from fbdplc.modeling import program_model
import functools

import z3

def merge_nets(nets):
    return functools.reduce(merge_scopes, nets)


def run_assertion(program: z3.Solver, assertion_list):
    test_asserts = z3.Or([z3.Not(a) for a in assertion_list])

    try:
        program.push()
        program.add(test_asserts)
        print(program)
        check = program.check()
        if check == z3.sat:
            print('Program failed!')
            print(program.model())
        elif check == z3.unsat:
            print('Program PASSED. No path to violated assertion.')
        else:
            print('Solver could not definitely determine an answer')
    finally:
        program.pop()

def main():
    path = 'testdata/example1/Demo.xml'
    print(f'Attempting to load s7xml file "{path}"')
    contexts = parse_from_file(path)
    print(f'Parsed {len(contexts)} networks')
    solver, ssa = program_model(merge_nets(contexts))
    print(f'Program uses the following variables: {ssa.list_variables()}')
    print(f'Program Model:\n{solver.assertions()}')

    # Our core principles:
    # Program uses the following variables: ['is_slow', 'mute_req', 'mute_granted',
    # 'left_clear', 'right_clear', 'scanners_ok', 'estop_clear', 'stop']
    
    # not estop clear => stop
    estop_clear = z3.Bool(ssa.read('estop_clear'))
    stop = z3.Bool(ssa.read('stop'))
    assert_stops_on_estop = z3.Implies(z3.Not(estop_clear), stop) 
    # (not(left_clear) or not(right_clear)) AND not mute_granted => stop
    left_clear = z3.Bool(ssa.read('left_clear'))
    right_clear = z3.Bool(ssa.read('right_clear'))
    mute_granted = z3.Bool(ssa.read('mute_granted'))
    scanner_violated = z3.And(z3.Or(z3.Not(left_clear), z3.Not(right_clear)), z3.Not(mute_granted))
    print(scanner_violated)
    assert_stop_on_scanners = z3.Implies(scanner_violated, stop)

    run_assertion(solver, [assert_stops_on_estop, assert_stop_on_scanners])



if __name__ == '__main__':
    main()
