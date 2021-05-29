'''
Libraries for constructing analyses of given program models.
'''

import z3

def add_assumes():
    assumes = []
    assumes.append(z3.Bool('ToSafety.a') == False)
    assumes.append(z3.Bool('ToSafety.b') == False)
    return assumes


def add_covers():
    covers = []
    cover0 = z3.Bool('a_or_b')
    covers.append(cover0)
    return covers


def add_asserts(ssa):
    print(ssa.data)
    asserts = []
    a = z3.Bool(ssa.read('ToSafety.reset'))
    b = z3.Bool(ssa.read('fault_clear'))
    # result = z3.Bool('a_or_b')
    
    # If a is not true, then b can never be true
    assert0 = z3.Implies(z3.Not(a), z3.Not(b))
    print('ASSERT THAT', assert0)
    asserts.append(assert0)
    
    return z3.Or([z3.Not(a) for a in asserts]) 

def run_assertions(program, ssa):
    program.push()
    try:
        asserts = add_asserts(ssa)
        program.add(asserts)
        result = program.check()
        if result == z3.sat:
            print('FAILURE: an assertion has been violated')
            print(program.model())
        elif result == z3.unsat:
            print("SUCCESS: no paths to failing assertions")
        else:
            print('UNKNOWN: unabe to exhaustively test')
    finally:
        program.pop()

def run_covers(program):
    program.push()
    try:
        covers = add_covers()
        program.add(covers)
        result = program.check()
        if result == z3.sat:
            print('SUCCESS: covers are reachable')
            print(program.model())
        elif result == z3.unsat:
            print("FAILURE: no paths to covers")
        else:
            print('UNKNOWN: unabe to exhaustively test')
    finally:
        program.pop()
