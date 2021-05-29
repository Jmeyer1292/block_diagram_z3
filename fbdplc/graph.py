
class ScopeContext:
    def __init__(self):
        self.accesses = {}
        self.parts = {}
        self.wires = {}


class VariableResolver:
    def __init__(self):
        self.data = {}

    @staticmethod
    def ir_name(name: str, access_no: int) -> str:
        return f'{name}_${access_no}'

    def list_variables(self):
        return [k for k in self.data]

    def write(self, name):
        if name in self.data:
            self.data[name] += 1
            return self.ir_name(name, self.data[name])
        else:
            self.data[name] = 0
            return self.ir_name(name, 0)

    def read(self, name, idx = None):
        if idx is not None:
            assert(name in self.data)
            return self.ir_name(name, idx)
         
        data = self.data.get(name, None)
        if data is None:
            self.data[name] = 0
            data = 0
        return self.ir_name(name, data)

