import z3
from typing import Dict
from fbdplc.utils import namespace
from enum import Enum


class PortDirection(Enum):
    IN = 1
    OUT = 2

# Siemens appears to associate the "negation" of a boolean
# signal not with a separate, NOT gate but instead with a
# given part port.
#
# I'm going to try to stay consistent for the moment, so some
# ports may have 2 variables internally.


class PartPort:
    def __init__(self, name: str, port_type: type, direction: PortDirection):
        self.name = name
        self.port_type = port_type
        self.direction = direction
        self.is_negated = False
        # internal & external variables
        self._var = None
        self._negated = None
    
    def instantiate(self, ctx: z3.Context):
        self._var = z3.Bool(self.name, ctx=ctx)
        if self.is_negated:
            self._negated = z3.Bool(self.name + '__neg', ctx=ctx)

    def set_negated(self):
        if self.port_type != bool:
            raise RuntimeError(f"Can't negate a port of type {self.port_type}")
        if self._negated is not None:
            raise RuntimeError(f'Port {self.name} already negated')

        self.is_negated = True

    def internal_var(self):
        if self._negated is None:
            return self._var
        else:
            return self._negated if self.direction == PortDirection.IN else self._var

    def external_var(self):
        if self._negated is None:
            return self._var
        else:
            return self._var if self.direction == PortDirection.IN else self._negated

    def model(self):
        if self._negated is None:
            return []
        else:
            return [self._negated == z3.Not(self._var)]

class PartModel:
    def __init__(self, name):
        self.name = name
        self.assertions = []
        self.ports : Dict[str, PartPort] = {}
    
    def add_port(self, name: str, port_type: type, dir: PortDirection):
        self.ports[name] = PartPort(namespace(self.name, name), port_type, dir)

    def instantiate_ports(self, context: z3.Context):
        model = []
        for p in self.ports.values():
            p.instantiate(context)
            port_model = p.model()
            model.extend(port_model)
        self.assertions.extend(model)
        

    def ivar(self, port_name: str):
        return self.ports[port_name].internal_var()
    
    def evar(self, port_name: str):
        return self.ports[port_name].external_var()

class PartTemplate:
    def __init__(self, name: str):
        self.name = name
        self.negations = set()
    
    def instantiate(self, namespace, context: z3.Context) -> PartModel:
        ''' Returns a unique program model '''
        pass

    def add_negation(self, port_name: str):
        self.negations.add(port_name)


class OrPart(PartTemplate):
    def __init__(self, name, n: int):
        super().__init__(name)
        self.dimension = n

    def instantiate(self, ns, context: z3.Context) -> PartModel:
        instance_name = namespace(ns, self.name)
        model = PartModel(instance_name)
        for i in range(1, self.dimension + 1):
            model.add_port(f'in{i}', bool, PortDirection.IN)
        model.add_port('out', bool, PortDirection.OUT)
        for p in self.negations:
            model.ports[p].set_negated()
        model.instantiate_ports(context)

        or_expr = z3.Or([model.ivar(f'in{i}') for i in range(1, self.dimension + 1)])

        model.assertions.append(or_expr == model.ivar('out'))
        return model

class AndPart(PartTemplate):
    def __init__(self, name, n: int):
        super().__init__(name)
        self.dimension = n

    def instantiate(self, ns, context: z3.Context) -> PartModel:
        instance_name = namespace(ns, self.name)
        model = PartModel(instance_name)
        for i in range(1, self.dimension + 1):
            model.add_port(f'in{i}', bool, PortDirection.IN)
        model.add_port('out', bool, PortDirection.OUT)
        for p in self.negations:
            model.ports[p].set_negated()
        model.instantiate_ports(context)

        and_expr = z3.And([model.ivar(f'in{i}') for i in range(1, self.dimension + 1)])
        model.assertions.append(and_expr == model.ivar('out'))
        return model

class CoilPart(PartTemplate):
    def __init__(self, name, port_type=bool, coil_type: str = 'Coil'):
        super().__init__(name)
        self.coil_type = coil_type
        self.port_type = port_type

    def instantiate(self, ns, context: z3.Context) -> PartModel:
        instance_name = namespace(ns, self.name)
        model = PartModel(instance_name)
        model.add_port('in', self.port_type, PortDirection.IN)
        model.add_port('operand', self.port_type, PortDirection.OUT)
        model.add_port('out', self.port_type, PortDirection.OUT)
        model.add_port('_old_operand', self.port_type, PortDirection.IN)
        for p in self.negations:
            model.ports[p].set_negated()
        model.instantiate_ports(context)

        logic = z3.And(self._internal_model(model), model.ivar('in') == model.ivar('out'))
        model.assertions.append(logic)

        return model

    def _internal_model(self, model: PartModel):
        # So a normal coil is just
        #   in == operand
        if self.coil_type == 'Coil':
            return model.ivar('in') == model.ivar('operand')

        if self.coil_type == 'SCoil':
            return z3.If(model.ivar('in'), model.ivar('operand') == True, model.ivar('operand') == model.ivar('_old_operand'))

        if self.coil_type == 'RCoil':
            return z3.If(model.ivar('in'), model.ivar('operand') == False, model.ivar('operand') == model.ivar('_old_operand'))

        raise RuntimeError('Unknown coil type {}'.format(self.coil_type))



# class Part:
#     '''
#     A Part has a name and a set of typed ports
#     '''

#     def __init__(self, name):
#         self.name = name
#         self.ports: Dict[PartPort] = {}

#     def model(self):
#         ports = self._port_models()
#         logic_model = self._evaluate_model()
#         if not ports:
#             return logic_model
#         else:
#             return (logic_model, z3.And(ports))

#     def _evaluate_model(self):
#         raise NotImplementedError()

#     def check_assignments(self):
#         pass

#     def _add_port(self, name: str, port_type: type, direction: PortDirection):
#         self.ports[name] = PartPort(
#             namespace(self.name, name), port_type, direction)

#     def _port_models(self):
#         model = []
#         for port in self.ports.values():
#             model.extend(port.model())
#         return model

#     def _combine(self, logic_model):
#         ports = self._port_models()
#         if not ports:
#             return logic_model
#         else:
#             return (logic_model, z3.And(ports))

#     def port(self, name: str) -> PartPort:
#         return self.ports[name]

#     def ivar(self, name: str):
#         '''
#         Retrieves the exterior facing signal
#         '''
#         return self.port(name).internal_var()

#     def evar(self, name: str):
#         '''
#         Retrieves the exterior facing signal
#         '''
#         return self.port(name).external_var()


# class OrPart(Part):
#     def __init__(self, name: str, n: int):
#         super().__init__(name)
#         self._add_port('out', bool, PortDirection.OUT)
#         self.n = n
#         for i in range(n):
#             self._add_port(f'in{i + 1}', bool, PortDirection.IN)

#     def _evaluate_model(self):
#         or_ex = [self.ivar(f'in{i}') for i in range(1, self.n + 1)]
#         return z3.Or(or_ex) == self.ivar('out')


# class AndPart(Part):
#     def __init__(self, name: str, n: int):
#         super().__init__(name)
#         self._add_port('out', bool, PortDirection.OUT)
#         self.n = n
#         for i in range(n):
#             self._add_port(f'in{i + 1}', bool, PortDirection.IN)

#     def _evaluate_model(self):
#         or_ex = [self.ivar(f'in{i}') for i in range(1, self.n + 1)]
#         return z3.And(or_ex) == self.ivar('out')


# class CoilPart(Part):
#     def __init__(self, name, port_type=bool, coil_type: str = 'Coil'):
#         super().__init__(name)
#         self._add_port('in', port_type, PortDirection.IN)
#         self._add_port('operand', port_type, PortDirection.OUT)
#         self._add_port('out', port_type, PortDirection.OUT)
#         self._add_port('_old_operand', port_type, PortDirection.IN)
#         self.coil_type = coil_type

#     def _internal_model(self):
#         # So a normal coil is just
#         #   in == operand
#         if self.coil_type == 'Coil':
#             return self.ivar('in') == self.ivar('operand')

#         if self.coil_type == 'SCoil':
#             return z3.If(self.ivar('in'), self.ivar('operand') == True, self.ivar('operand') == self.ivar('_old_operand'))

#         if self.coil_type == 'RCoil':
#             return z3.If(self.ivar('in'), self.ivar('operand') == False, self.ivar('operand') == self.ivar('_old_operand'))

#         raise RuntimeError('Unknown coil type {}'.format(self.coil_type))

#     def _evaluate_model(self):
#         return z3.And(self._internal_model(), self.ivar('in') == self.ivar('out'))


# class PTriggerPart(Part):
#     def __init__(self, name):
#         super().__init__(name)
#         self._add_port('in', bool, PortDirection.IN)
#         self._add_port('out', bool, PortDirection.OUT)
#         self._add_port('bit', bool, PortDirection.OUT)
#         self._add_port('_old_bit', bool, PortDirection.IN)

#     def _evaluate_model(self):
#         m = []
#         # Output is true iff !_old_bit and in
#         m.append(z3.And(self.ivar('in'), z3.Not(
#             self.ivar('_old_bit'))) == self.ivar('out'))
#         m.append(self.ivar('in') == self.ivar('bit'))
#         return m


# class NTriggerPart(Part):
#     def __init__(self, name):
#         super().__init__(name)
#         self._add_port('in', bool, PortDirection.IN)
#         self._add_port('out', bool, PortDirection.OUT)
#         self._add_port('bit', bool, PortDirection.OUT)
#         self._add_port('_old_bit', bool, PortDirection.IN)

#     def _evaluate_model(self):
#         m = []
#         # Output is true iff _old_bit and !in
#         m.append(z3.And(z3.Not(self.ivar('in')),
#                  self.ivar('_old_bit')) == self.ivar('out'))
#         m.append(self.ivar('in') == self.ivar('bit'))
#         return m
