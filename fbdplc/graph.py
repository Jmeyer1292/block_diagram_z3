from enum import unique

from fbdplc.utils import namespace
from fbdplc.sorts import SORT_MAP, UDTInstance, UDTSchema, g_udt_archive
import functools
from typing import List


class ScopeContext:
    def __init__(self, name=''):
        self.name = name
        self.accesses = {}
        self.parts = {}
        self.wires = {}
        self.calls = {}


class VariableResolver:
    def __init__(self):
        self.data = {}

    @staticmethod
    def ir_name(name: str, access_no: int) -> str:
        return f'{name}#{access_no}'

    def list_variables(self):
        return [k for k in self.data]

    def write(self, name):
        if name in self.data:
            self.data[name] += 1
            return self.ir_name(name, self.data[name])
        else:
            self.data[name] = 0
            return self.ir_name(name, 0)

    def read(self, name, idx=None):
        if idx is not None:
            assert name in self.data, f'"{name}" not in variable resolver directory. Has {self.list_variables()}'
            return self.ir_name(name, idx)

        data = self.data.get(name, None)
        if data is None:
            self.data[name] = 0
            data = 0
        return self.ir_name(name, data)
    
    
    def create(self, name: str):
        # Should this have sort too?
        assert name not in self.data
        self.data[name] = 0


class MemoryProxy:
    def __init__(self, ns, ctx):
        self.ns = ns
        self.ctx = ctx
        # Maps name: str -> Tuple[access_count: int, sort: Type]
        self.data = {}
        # Maps unique_name: str -> Instance
        self._variables = {}

    def list_variables(self):
        return [n for n in self.data]

    @staticmethod
    def ir_name(name: str, access_no: int) -> str:
        return f'{name}#{access_no}'

    def lastest_name(self, name: str):
        return self.ir_name(name, self.data[name][0])
    
    def __make_var(self, ir, sort):
        unique_ir_name = namespace(self.ns, ir)
        v = sort.make(unique_ir_name, self.ctx)
        self._variables[ir] = v
        return v

    def __create(self, name: str, sort):
        # Should this have sort too?
        assert name not in self.data
        assert sort in SORT_MAP.values()
        self.data[name] = [0, sort]
        
        ir_name = self.lastest_name(name)
        return self.__make_var(ir_name, sort)
    
    def create(self, name: str, sort):
        assert sort in SORT_MAP.values() or sort in g_udt_archive.values()
        
        if isinstance(sort, UDTSchema):
            for n, v in sort.iterfields(name + '.'):
                self.__create(n, v)
        else:
            self.__create(name, sort)
    
    def __read(self, name: str, index = None, sort = None):
        assert name in self.data, f'{name} not in memory object'

        entry = self.data[name]
        read_no = entry[0] if index is None else index
        assert read_no <= entry[0], f'Attempting to read an index that doesnt exist for {name}: {read_no}'  

        ir = self.ir_name(name, read_no)
        v = self._variables[ir]
        if sort is not None:
            assert sort == entry[1], 'Types do not match'
        return v
    
    def read(self, name: str, index = None, sort = None):
        if isinstance(sort, UDTSchema):
            instance = UDTInstance(sort)
            for n, v in sort.iterfields(name + '.'):
                variable = self.__read(n, index, v)
                instance.fields[n] = variable
            return instance
        else:
            return self.__read(name, index, sort)

    def __write(self, name: str, sort = None):
        # Only works on primitives
        assert name in self.data, f'{name} not in memory object'
        entry = self.data[name]
        if sort is not None:
            assert sort == entry[1], f'Types do not match {sort} vs {entry[1]}'
        else:
            sort = entry[1]

        entry[0] = entry[0] + 1
        return self.__make_var(self.ir_name(name, entry[0]), sort)

    def write(self, name: str, sort = None):
        if isinstance(sort, UDTSchema):
            instance = UDTInstance(sort)
            for n, v in sort.iterfields(name + '.'):
                variable = self.__write(n, v)
                instance.fields[n] = variable
            return instance
        else:
            return self.__write(name, sort)

def merge_scopes(a: ScopeContext, b: ScopeContext) -> ScopeContext:
    result = ScopeContext(a.name + '+' + b.name)

    result.parts = a.parts.copy()
    result.parts.update(b.parts)

    result.accesses = a.accesses.copy()
    result.accesses.update(b.accesses)

    result.wires = a.wires.copy()
    result.wires.update(b.wires)

    result.calls = a.calls.copy()
    result.calls.update(b.calls)

    return result


def merge_nets(nets: List[ScopeContext]):
    return functools.reduce(merge_scopes, nets)
