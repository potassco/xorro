from . import util
from itertools import chain
import clingo

class UPTotalPropagator:
    def __init__(self):
        self.__sat = True
        self.__consequences = []
        self.__xors = []
        self.__lits = []

    def init(self, init):
        """
        Initializes xor constraints and watches based on the symbol table.

        Constraints of length zero and one are handled specially, to keep the
        implementation of the general constraints simple.
        """
        ret = util.symbols_to_xor_r(init.symbolic_atoms, util.default_get_lit(init))
        if ret is None:
            self.__sat = False
        else:
            constraints, facts = ret
            self.__consequences.extend(facts)

            ## Reduce constraints with facts (Pre-GJE)
            ## Perform propagation from facts
            if facts and constraints:
                constraints, facts = propagate_implications(constraints, facts)
                ## TODO: Detect conflicts and satisfiability from here
                self.__consequences.extend(facts)
                
            for constraint in constraints:
                if len(constraint) > 1:
                    self.__xors.append(constraint)
                    for literal in constraint:
                        if abs(literal) not in self.__lits:
                            self.__lits.append(abs(literal))

        init.check_mode = clingo.PropagatorCheckMode.Fixpoint

    def check(self, control):
        """
        Since the XOR constraint above handles only constraints with at least
        two literals, here the other two cases are handled.

        Empty conflicting constraints result in top-level conflicts and unit
        constraints will be propagated on the top-level.
        """
        if control.assignment.decision_level == 0:
            if not self.__sat:
                control.add_clause([]) and control.propagate()
                return
            for lit in self.__consequences:
                if not control.add_clause([lit]) or not control.propagate():
                    return

        elif control.assignment.is_total:
            xors = self.__xors
            for xor in xors:
                conflict = True
                nogood = []
                if xor[0] < 0:
                    conflict = False
                
                for lit in xor:
                    lit = abs(lit)
                    if control.assignment.is_true(lit):
                        nogood.append( lit)
                    elif control.assignment.is_false(lit):
                        nogood.append(-lit)
                        
                    value = control.assignment.value(lit)
                    if value:
                        conflict ^= True
                        
                if conflict:
                    if not control.add_nogood(nogood) or not control.propagate():
                        return
