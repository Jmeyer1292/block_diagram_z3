
class ScopeContext:
    def __init__(self):
        self.accesses = {}
        self.parts = {}
        self.wires = {}


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

