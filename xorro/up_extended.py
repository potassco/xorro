from . import util
import clingo

def propagate_implications(constraints, facts):
    for constraint in constraints:
        odd = False
        for lit in facts:
            if lit in constraint:
                odd ^= True
                constraint_.remove( lit)
            elif -lit in constraint_:
                constraint_.remove(-lit)
        if odd and constraint:
            constraint[0] = -constraint[0]## Keep the even parity
    return constraints
    
def propagate_(assigned, unassigned):
    implication = False
    for i in range(len(unassigned)):
        if len(unassigned[i]) == 1:
            literal = unassigned[i][0]
            implication = True
            assigned[i].append(literal)

            for j in range(len(unassigned)):
                if len(unassigned[j]) > 1:
                    odd = False
                    if literal in unassigned[j]:
                        odd ^= True
                        assigned[j].append(literal)
                        unassigned[j].remove(literal)
                    elif -literal in unassigned[j]:
                        assigned[j].append( literal)
                        unassigned[j].remove(-literal)

                    if odd and unassigned[j]:
                        unassigned[j][0] = -unassigned[j][0]## Keep the even parity

    return assigned if implication else None

class XOR:
    """
    A XOR constraint maintains the following invariants:
    1. there are at least two literals, and
    2. the first two literals are unassigned, or all literals are assigned and
       the first two literals have been assigned last on the same decision
       level.
    """
    def __init__(self, literals):
        assert(len(literals) >= 2)
        self.__literals = literals
        self.__index = 2

    def __iter__(self):
        return iter(self.__literals)

    def propagate(self, assignment):
        """
        Propagates wrt the given partial assignment
        Return assigned and non assigned literals
        """
        unassigned, assigned = [], []
        odd = False
        for lit in self:
            lit = abs(lit)
            if assignment.is_true(lit):
                assigned.append(lit)
                odd ^=True
            elif assignment.is_false(lit):
                assigned.append(-lit)
            elif assignment.value(lit) is None:
                unassigned.append(lit)

        if odd and unassigned: ## parse it to odd if necessary
            unassigned[0] = -unassigned[0]

        return assigned, unassigned
            
    def reason(self, assignment):
        if not sum(1 for lit in self if assignment.is_true(lit)) % 2:
            return [lit if assignment.is_true(lit) else -lit for lit in self]

class UPExtendedPropagator:
    def __init__(self):
        self.__states  = []
        self.__sat = True
        self.__consequences = []

    def init(self, init):
        init.check_mode = clingo.PropagatorCheckMode.Fixpoint
        
        for thread_id in range(len(self.__states), init.number_of_threads):
            self.__states.append([])

        ret = util.symbols_to_xor_r(init.symbolic_atoms, util.default_get_lit(init))
        if ret is None:
            self.__sat = False
        else:
            constraints, facts = ret
            if facts and constraints:
                constraints = propagate_implications(constraints, facts)
                ## TODO: Detect conflicts and satisfiability from here
            self.__consequences.extend(facts)

            for constraint in constraints:
                xor = XOR(list(sorted(constraint)))
                self.__states[thread_id].append(xor)

    def check(self, control):
        """
        Here we handle three cases:
         1) Empty conflicting constraints result in top-level conflicts 
         2) unary constraints will be propagated on the top-level, and
         3) UP from partial assignment without updating the state. 
            Also, this UP version propagates in further xors after new implication is found.
        """
        if control.assignment.decision_level == 0:
            if not self.__sat:
                control.add_clause([]) and control.propagate()
                return
            for lit in self.__consequences:
                if not control.add_clause([lit]) or not control.propagate():
                    return

        elif control.assignment.decision_level > 0:
            state = self.__states[control.thread_id]
            if state:
                ass = control.assignment
                partial = []
                to_propagate = []
                propagate = False
                for xor in state:
                    assigned, unassigned = xor.propagate(ass)
                    if len(unassigned) == 1:
                        propagate = True
                    partial.append(assigned)
                    to_propagate.append(unassigned)

                    if len(unassigned) == 0: ## Total assignment on this specific XOR
                        nogood = xor.reason(ass)
                        if nogood is not None:
                            control.add_nogood(nogood) and control.propagate()
                            return

                if propagate: ## Partial assingment with something to propagate
                    clauses = propagate_(partial, to_propagate)
                    if clauses is not None:
                        for clause in clauses:
                            if not control.add_clause(clause) or not control.propagate():
                                return
