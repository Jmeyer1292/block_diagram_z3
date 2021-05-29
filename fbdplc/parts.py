from ctypes import ArgumentError
import z3
from typing import Dict

class VariableResolver:
    def __init__(self):
        self.data = {}
    
    def write(self, name):
        if name in self.data:
            self.data[name] += 1
            return f'{name}_${self.data[name]}'
        else:
            self.data[name] = 0
            return f'{name}_$0'
    
    def read(self, name):
        data = self.data.get(name, None)
        if data is None:
            self.data[name] = 0
            data = 0
        return f'{name}_${data}'

class PartPort:
    def __init__(self, name: str, port_type: type):
        self.name = name
        self.port_type = port_type
        self.var = None
        if port_type == bool:
            self.var = z3.Bool(name)
        assert(self.var is not None)


def namespace(ns : str , name : str):
    return ':'.join([ns, name])

class Part:
    '''
    A Part has a name and a set of typed ports
    '''
    def __init__(self, name):
        self.name = name
        self.ports : Dict[PartPort] = {}

    def models(self):
        pass

    def check_assignments(self):
        pass
    
    def add_port(self, name: str, port_type: type):
        self.ports[name] = PartPort(namespace(self.name, name), port_type)
    
    def port(self, name: str):
        return self.ports[name]
    
    def var(self, name: str):
        return self.port(name).var

class OrPart(Part):
    def __init__(self, name: str, n: int):
        super().__init__(name)
        self.add_port('out', bool)
        self.n = n
        for i in range(n):
            self.add_port( f'in{i + 1}', bool)
    
    def model(self, variable_tracker: VariableResolver):
        or_ex = [self.var(f'in{i}') for i in range(1, self.n + 1)]
        return z3.Or(or_ex) == self.var('out')

class AndPart(Part):
    def __init__(self, name: str, n: int):
        super().__init__(name)
        self.add_port('out', bool)
        self.n = n
        for i in range(n):
            self.add_port( f'in{i + 1}', bool)
    
    def model(self, variable_tracker: VariableResolver):
        or_ex = [self.var(f'in{i}') for i in range(1, self.n + 1)]
        return z3.And(or_ex) == self.var('out')

class CoilPart(Part):
    def __init__(self, name, port_type = bool, coil_type: str = 'Coil'):
        super().__init__(name)
        self.add_port('in', port_type)
        self.add_port('operand', port_type)
        self.add_port('_old_operand', port_type)
        self.coil_type = coil_type
        

    def model(self, resolver : VariableResolver):
        # So a normal coil is just
        #   in == operand
        if self.coil_type == 'Coil':
            return self.var('in') == self.var('operand')
        
        if self.coil_type == 'SCoil':
            return z3.If(self.var('in'), self.var('operand') == True, self.var('operand') == self.var('_old_operand'))
        
        if self.coil_type == 'RCoil':
            return z3.If(self.var('in'), self.var('operand') == False, self.var('operand') == self.var('_old_operand'))
        
        raise ArgumentError('Unknown coil type {}'.format(self.coil_type)) 

# class OrPart(Part):
#     def __init__(self, name, n):
#         super()
#         self.n = n
    
#     def resolve(self, port):
#         return f'or_{port}'

#     def declare_vars(self):
#         self._inputs = [z3.Bool(f'or_in{i}') for i in range(1, self.n + 1)]
#         self._output = z3.Bool('or_out')
#         return z3.Or(self._inputs) == self._output

# class AndPart(Part):
#     def __init__(self, n):
#         self.n = n
    
#     def declare_vars(self):
#         self._inputs = [z3.Bool(f'and_{i}') for i in range(self.n)]
#         self._output = z3.Bool('and_out')
#         return z3.And(self._inputs) == self._output

# class CoilPart(Part):
#     def __init__(self):
#         pass
    
#     def declare_vars(self):
#         self.input = z3.Bool('coil_in')
#         self.operand = z3.Bool('coil_operand')
#         return self.input == self.operand
    
#     def resolve(self, port):
#         return f'coil_{port}'


# class SetCoilPart(Part):
#     def __init__(self):
#         pass
    
#     def declare_vars(self):
#         self.input = z3.Bool('setcoil_in')
#         self.operand = z3.Bool('setcoil_operand')
#         return z3.If(self.input, self.operand == True, self.operand == self.operand)
    
#     def resolve(self, port):
#         return f'setcoil_{port}'


# class ResetCoilPart(Part):
#     def __init__(self):
#         pass
    
#     def declare_vars(self):
#         self.input = z3.Bool('resetcoil_in')
#         self.operand = z3.Bool('resetcoil_operand')
#         return self.input == self.operand
    
#     def resolve(self, port):
#         return f'resetcoil_{port}'

# class PBoxPart(Part):
#     def __init__(self):
#         pass

def _test_or():
    o = OrPart('network0:32', 2)
    assert(len(o.ports) == 3)
    model = o.model(None)
    print(o.ports)
    print(model)


def test():
    _test_or()


if __name__ == '__main__':
    test()
