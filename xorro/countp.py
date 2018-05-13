"""
This xor propagator actually does not interfere with clasp's propagation.  In
fact we just check (count) the number of truth's assignments given by clasp
respecting the parity given for each xor constraint In case of conflict, add
the nogood and let clasp to propagate again
"""

from . import util

class XOR:
    def __init__(self, literals, parity):
        self.__literals = literals
        self.__parity = parity

    def check(self, ass):
        count  = sum(1 for lit in self if ass.is_true(lit))
        if count % 2 != self.__parity:
            return [lit if ass.is_true(lit) else -lit for lit in self]

    def __iter__(self):
        return iter(self.__literals)

class CountCheckPropagator:
    def __init__(self):
        self.__states = []

    def init(self, init):
        for thread_id in range(len(self.__states), init.number_of_threads):
            self.__states.append([])

        constraints = util.symbols_to_xor(init)
        for constraint in constraints.values():
            xor = XOR(list(sorted(constraint["literals"])), constraint["parity"])
            self.__states[thread_id].append(xor)

    def check(self, control):
        state = self.__states[control.thread_id]
        for xor in state:
            nogood = xor.check(control.assignment)
            if nogood is not None:
                control.add_nogood(nogood) and control.propagate()
                return
