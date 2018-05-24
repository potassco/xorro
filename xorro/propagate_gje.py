from . import util
from . import gje
from itertools import chain
import clingo
from copy import deepcopy

class XOR:
    """
    A XOR constraint maintains the following invariants:
    1. there are at least two literals, and
    2. the first two literals are unassigned, or all literals are assigned and
       the first two literals have been assigned last on the same decision
       level.
    Furthermore, an index pointing to the literal after the literal assigned
    last is maintained. We start the search for the next unassigned literal
    from this point. This is important to get the amortized linear propagation
    time.
    """
    def __init__(self, literals, parity):
        assert(len(literals) >= 2)
        self.__literals = literals
        self.__parity = parity
        self.__index = 2

    def __len__(self):
        return len(self.__literals)

    def __getitem__(self, idx):
        return self.__literals[idx]

    def __setitem__(self, idx, val):
        self.__literals[idx] = val
        return val            

    def propagate(self, assignment, i):
        """
        Propagates the given assigned index.

        If an unwatched unassigned literal is found, the literals are
        rearranged so that the given index points to it. The function returns
        true if an such a literal is found.
        """
        assert(i < 2)
        for j in chain(range(self.__index, len(self)), range(2, self.__index)):
            if assignment.value(self[j]) is None:
                self.__index = j + 1 if j + 1 < len(self) else 2
                self[i], self[j] = self[j], self[i]
                return True
        return False

    def reason_gje(self, columns, assignment):
        state = {}
        partial = []
        deduced_literals = []

        ## Get Partial Assignment
        state["parity"] = columns["parity"]
        for lit, column in columns.items():
            if lit != "parity":
                value = assignment.value(lit)
                if value == None:
                    state[lit] = column
                elif value == True:
                    state["parity"] = gje.xor_columns(column, state["parity"])
                    partial.append( lit)
                elif value == False:                    
                    partial.append(-lit)                           

        ## Build the matrix from columns state
        matrix, xor_lits = gje.columns_state_to_matrix(state)

        ## If there are more than unary xors perform GJE
        if len(state) > 2:
            matrix = gje.perform_gauss_jordan_elimination(matrix)

        ## Check SATISFIABILITY
        conflict = gje.check_sat(matrix)
        if not conflict and xor_lits:
            ## Imply literals 
            deduced_literals = gje.deduce_clause(matrix, xor_lits)

        return conflict, partial, deduced_literals
        

class Propagate_GJE:
    def __init__(self):
        self.__states  = []
        self.__columns = {}
        self.__columns_state = [{}]
        self.__sat = True
        self.__consequences = []

    def __add_watch(self, ctl, xor, unassigned, thread_ids):
        """
        Adds a watch for the for the given index.

        The literal at the given index has to be either unassigned or become
        unassigned through backtracking before the associated constraint can
        become unit resulting again.
        """
        variable = abs(xor[unassigned])
        ctl.add_watch( variable)
        ctl.add_watch(-variable)
        for thread_id in thread_ids:
            self.__states[thread_id].setdefault(variable, []).append((xor, unassigned))

    def __lits_to_binary(self, xor_lits, constraint, parity):
        columns = self.__columns
        for i in range(len(xor_lits)):
            if xor_lits[i] in constraint:
                columns.setdefault(xor_lits[i], []).append(1)
            else: columns.setdefault(xor_lits[i], []).append(0)
        columns.setdefault("parity", []).append(parity)

    def init(self, init):
        """
        Initializes xor constraints and watches based on the symbol table.

        Constraints of length zero and one are handled specially, to keep the
        implementation of the general constraints simple.
        """
        for thread_id in range(len(self.__states), init.number_of_threads):
            self.__states.append({})
        
        constraints, xor_literals = util.symbols_to_xor(init)
        ## Build matrix row by row and create row state and col state
        for constraint in constraints.values():
            if len(constraint["literals"]) == 1:
                lit = next(iter(constraint["literals"]))
                self.__consequences.append(lit if constraint["parity"] == 1 else -lit)
            elif len(constraint["literals"]):
                xor = XOR(list(sorted(constraint["literals"])), constraint["parity"])
                self.__add_watch(init, xor, 0, range(init.number_of_threads))
                self.__add_watch(init, xor, 1, range(init.number_of_threads))
                self.__lits_to_binary(xor_literals, list(sorted(constraint["literals"])), constraint["parity"])
            elif constraint["parity"] == 1:
                self.__sat = False
                break
            
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

    def propagate(self, control, changes):
        """
        Propagates XOR constraints maintaining two watches per constraint.

        Generated conflicts are guaranteed to be asserting (have at least two
        literals from the current decision level).
        """
        state = self.__states[control.thread_id]
        columns = self.__columns
                        
        for literal in changes:
            variable = abs(literal)

            state[variable], watches = [], state[variable]
            assert(len(watches) > 0)
            for i in range(len(watches)):
                xor, unassigned = watches[i]
                if xor.propagate(control.assignment, unassigned):
                    # We found an unassigned literal, which is watched next.
                    self.__add_watch(control, xor, unassigned, (control.thread_id,))
                else:
                    # Here the constraint is either unit, satisfied, or
                    # conflicting. In any case, we can keep the watch because
                    # (*) the current decision level has to be backtracked
                    # before the constraint can become unit again.
                    state[variable].append((xor, unassigned))                                                           
                    
                    ## GJE
                    conflict, partial, clause = xor.reason_gje(columns, control.assignment)
                    if clause is not None:
                        for lit in clause:
                            if not control.add_nogood(partial+[-lit]) or not control.propagate():
                                return                                
                    if conflict:
                        if not control.add_nogood(partial) or not control.propagate():
                            return
                    
            if len(state[variable]) == 0:
                control.remove_watch( variable)
                control.remove_watch(-variable)
                state.pop(variable)
