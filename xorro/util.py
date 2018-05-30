from collections import namedtuple
from itertools import *
from functools import *
import sys

def attrdef(m, a, b):
    return getattr(m, a if hasattr(m, a) else b)

zip_longest = attrdef(sys.modules[__name__], 'zip_longest', 'izip_longest')

def get_parity(par):
    if str(par) == "odd": return 1
    else: return 0

def invert_parity(par):
    return int(par) ^ 1

def symbols_to_xor(init):
    constraints = {}
    xor_literals = []

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
                if lit not in xor_literals:
                    xor_literals.append(lit)
    return constraints, sorted(xor_literals)

def default_get_lit(init):
    value = init.assignment.value
    def get_lit(atom):
        lit = init.solver_literal(atom.literal)
        return lit, value(lit)
    return get_lit

class _XORConstraint:
    def __init__(self, parity):
        self.parity = parity
        self.literals = set()

def symbols_to_xor_r(symbolic_atoms, get_lit):
    """
    This is a refactored version of symbols_to_xor, which should be used
    instead of symbols_to_xor. When all occurrences have been replaced,
    symbols_to_xor should be removed.

    Returns None if the constraints are trivially unsatisfiable, otherwise
    returns a list of xor constraints and a list of facts. A xor constraint is
    represented as a list of literals.

    Arguments:
    symbolic_atoms -- The domain having predicates __parity/2 and __parity/3.
    get_lit        -- Function mapping a symbolic atom to a litral and its
                      truth value.
    """
    constraints = {}

    for atom in symbolic_atoms.by_signature("__parity",2):
        cid = atom.symbol.arguments[0].number
        par = atom.symbol.arguments[1].name
        constraints[cid] = _XORConstraint(get_parity(par))

    for atom in symbolic_atoms.by_signature("__parity",3):
        constraint = constraints[atom.symbol.arguments[0].number]
        lit, truth = get_lit(atom)

        if truth:
            constraint.parity = invert_parity(constraint.parity)
        elif truth is None:
            if lit in constraint.literals:
                constraint.literals.remove(lit)
            elif -lit in constraint.literals:
                constraint.literals.remove(-lit)
                constraint.parity = invert_parity(constraint.parity)
            else:
                constraint.literals.add(lit)

    facts = set()
    result = []
    for constraint in constraints.values():
        literals = sorted(constraint.literals)
        n = len(literals)
        if n == 0:
            if constraint.parity == 1:
                return None
        else:
            if constraint.parity == 0:
                literals[0] = -literals[0]
            if n > 1:
                result.append(literals)
            else:
                facts.add(literals[0])

    return result, sorted(facts)
