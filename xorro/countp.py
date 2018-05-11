"""
This xor propagator actually does not interfere with clasp's propagation.  In
fact we just check (count) the number of truth's assignments given by clasp
respecting the parity given for each xor constraint In case of conflict, add
the nogood and let clasp to propagate again
"""

def get_parity(par):
    if str(par) == "odd": return 1
    else: return 0

def invert_parity(par):
    return int(par) ^ 1

##########################################################################################################
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
        constraints = {}

        for atom in init.symbolic_atoms.by_signature("__parity",2):
            cid = atom.symbol.arguments[0].number
            par = atom.symbol.arguments[1].name
            constraints[cid] = {"parity": get_parity(par), "literals": set()}

        for atom in init.symbolic_atoms.by_signature("__parity",3):
            cid = atom.symbol.arguments[0].number
            lit = init.solver_literal(atom.literal)
            ass = init.assignment

            if ass.is_true(lit):
                constraints[cid]["parity"] = invert_parity(constraints[cid]["parity"])
            elif not ass.is_false(lit):
                literals = constraints[cid]["literals"]
                if lit in literals:
                    literals.remove(lit)
                elif -lit in literals:
                    literals.remove(-lit)
                    constraints[cid]["parity"] = invert_parity(constraints[cid]["parity"])
                else:
                    constraints[cid]["literals"].add(lit)

        for constraint in constraints.values():
            for thread_id in range(len(self.__states), init.number_of_threads):
                self.__states.append([])
            xor = XOR(list(sorted(constraint["literals"])), constraint["parity"])
            self.__states[thread_id].append(xor)

    def check(self, control):
        state = self.__states[control.thread_id]
        for xor in state:
            nogood = xor.check(control.assignment)
            if nogood is not None:
                control.add_nogood(nogood) and control.propagate()
                return
