import z3
from typing import Dict
from fbdplc.utils import namespace
from enum import Enum


class PortDirection(Enum):
    IN = 1
    OUT = 2


class PartPort:
    def __init__(self, name: str, port_type: type, direction: PortDirection):
        self.name = name
        self.port_type = port_type
        self.var = None
        self.direction = direction
        if port_type == bool:
            self.var = z3.Bool(name)
        assert(self.var is not None)


class Part:
    '''
    A Part has a name and a set of typed ports
    '''

    def __init__(self, name):
        self.name = name
        self.ports: Dict[PartPort] = {}

    def model(self):
        pass

    def check_assignments(self):
        pass

    def _add_port(self, name: str, port_type: type, direction: PortDirection):
        self.ports[name] = PartPort(
            namespace(self.name, name), port_type, direction)

    def port(self, name: str):
        return self.ports[name]

    def var(self, name: str):
        return self.port(name).var


class OrPart(Part):
    def __init__(self, name: str, n: int):
        super().__init__(name)
        self._add_port('out', bool, PortDirection.OUT)
        self.n = n
        for i in range(n):
            self._add_port(f'in{i + 1}', bool, PortDirection.IN)

    def model(self):
        or_ex = [self.var(f'in{i}') for i in range(1, self.n + 1)]
        return z3.Or(or_ex) == self.var('out')


class AndPart(Part):
    def __init__(self, name: str, n: int):
        super().__init__(name)
        self._add_port('out', bool, PortDirection.OUT)
        self.n = n
        for i in range(n):
            self._add_port(f'in{i + 1}', bool, PortDirection.IN)

    def model(self):
        or_ex = [self.var(f'in{i}') for i in range(1, self.n + 1)]
        return z3.And(or_ex) == self.var('out')


class CoilPart(Part):
    def __init__(self, name, port_type=bool, coil_type: str = 'Coil'):
        super().__init__(name)
        self._add_port('in', port_type, PortDirection.IN)
        self._add_port('operand', port_type, PortDirection.OUT)
        self._add_port('_old_operand', port_type, PortDirection.IN)
        self.coil_type = coil_type

    def model(self):
        # So a normal coil is just
        #   in == operand
        if self.coil_type == 'Coil':
            return self.var('in') == self.var('operand')

        if self.coil_type == 'SCoil':
            return z3.If(self.var('in'), self.var('operand') == True, self.var('operand') == self.var('_old_operand'))

        if self.coil_type == 'RCoil':
            return z3.If(self.var('in'), self.var('operand') == False, self.var('operand') == self.var('_old_operand'))

        raise RuntimeError('Unknown coil type {}'.format(self.coil_type))
