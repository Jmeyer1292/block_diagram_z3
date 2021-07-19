from fbdplc.utils import namespace
from fbdplc.sorts import SORT_MAP, UDTInstance, children, is_primitive
import functools
from typing import List

import logging
logger = logging.getLogger(__name__)


class ScopeContext:
    def __init__(self, name=''):
        self.name = name
        self.accesses = {}
        self.parts = {}
        self.wires = {}
        self.calls = {}


class MemoryProxy:
    def __init__(self, ns, ctx):
        self.ns = ns
        self.ctx = ctx
        self.tree = {}
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

    def __create(self, name: str, sort, unique=True):
        assert not unique or (
            name not in self.data), f'Symbol "{name}" already in memory'
        assert sort in SORT_MAP.values(), f'Symbol type {sort} not recognized'
        self.data[name] = [0, sort]

        ir_name = self.lastest_name(name)
        return self.__make_var(ir_name, sort)

    def sort(self, name: str):
        return self.tree[name]

    def _make_variables(self, name: str, sort, unique=True):
        # Now we've got a variable of 'name' and 'sort', we need to create its children:
        # Create the root of the new type and everything under it:
        self.tree[name] = sort
        if is_primitive(sort):
            logger.info(f'Creating primitive "{name}" of sort "{sort}"')
            self.__create(name, sort, unique=unique)
        else:
            for child_name, child_sort in children(sort):
                self._make_variables(name + '.' + child_name, child_sort)

    def create(self, name: str, sort, unique=True):
        # Mem is kept as a tree
        tree_levels = name.split('.')
        logger.debug(f'Access levels: {tree_levels}')

        # Create any access levels above the variable being created
        for i in range(len(tree_levels) - 1):
            level = '.'.join(tree_levels[0: i + 1])

            if level in self.data:
                logger.debug(
                    f'We already have {level} w/ at index = {i} and with sort {self.data[level][1]}')
            else:
                has_sort = i + 1 == len(tree_levels)
                if has_sort:
                    logger.debug(
                        f'Creating new level {level} of known sort {sort}')
                else:
                    logger.warn(
                        f'Creating new level {level} with UNKNOWN sort')

                this_sort = sort if has_sort else None
                self.tree[level] = this_sort

        # Now we've got a variable of 'name' and 'sort', we need to create its children:
        self._make_variables(name, sort, unique=unique)

    def read(self, name: str, index=None, sort=None):
        '''
        Read the variable with "name" from the symbol tree. If "sort" is provided, perform
        type checking.

        May return a primitive, a user-defined-type instance, or an untyped dictionary of
        objects if the type is not available.

        I should be able to get rid of this untyped behavior.
        '''
        assert name in self.tree, f'{name} not in symbol tree'

        tree_sort = self.tree[name]
        if tree_sort is not None and sort is not None:
            assert tree_sort == sort, f"Read types don't match {tree_sort} vs {sort}"

        resolved_sort = None
        if tree_sort is not None:
            resolved_sort = tree_sort
        elif sort is not None:
            resolved_sort = sort

        if is_primitive(resolved_sort):
            return self.__read(name, index=index, sort=resolved_sort)
        else:
            instance = UDTInstance(resolved_sort)
            for n, v in resolved_sort.iterfields():
                variable = self.__read(name + '.' + n, sort=v, index=index)
                instance.fields[n] = variable
            return instance

    def __read(self, name: str, index=None, sort=None):
        assert name in self.data, f'{name} not in memory object'

        entry = self.data[name]
        read_no = entry[0] if index is None else index
        assert read_no <= entry[
            0], f'Attempting to read an index that doesnt exist for {name}: {read_no}'

        ir = self.ir_name(name, read_no)
        v = self._variables[ir]
        if sort is not None:
            assert sort == entry[1], 'Types do not match'
        return v

    def __write(self, name: str, sort=None):
        # Only works on primitives
        assert name in self.data, f'{name} not in memory object'
        entry = self.data[name]
        if sort is not None:
            assert sort == entry[1], f'Types do not match {sort} vs {entry[1]}'
        else:
            sort = entry[1]

        entry[0] = entry[0] + 1
        return self.__make_var(self.ir_name(name, entry[0]), sort)

    def write(self, name: str, sort=None):
        tree_sort = self.tree[name]
        if tree_sort is not None and sort is not None:
            assert tree_sort == sort, f"Read types don't match {tree_sort} vs {sort}"

        resolved_sort = None
        if tree_sort is not None:
            resolved_sort = tree_sort
        elif sort is not None:
            resolved_sort = sort

        if is_primitive(resolved_sort):
            return self.__write(name, sort=resolved_sort)
        else:
            instance = UDTInstance(resolved_sort)
            for n, v in resolved_sort.iterfields():
                variable = self.__write(name + '.' + n, sort=v)
                instance.fields[n] = variable
            return instance


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
