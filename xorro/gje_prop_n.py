from . import util
from . import gje
from itertools import chain
import clingo
import numpy as np

class List:
    """
    All columns of the state are built in this class, the parity column and the literals
    """
    def __init__(self, ls):
        self.__list = ls

    def __len__(self):
        return len(self.__list)

    def __getitem__(self, idx):
        return self.__list[idx]
                
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
    def __init__(self, literals):
        assert(len(literals) >= 2)
        self.__literals = literals
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

    def reason_gje(self, columns, assignment, cutoff):
        state = {}
        parities = columns["parity"]
        partial = []

        ## Get Partial Assignment
        for key, value in columns.items():
            if key != "parity":
                assign = assignment.value(key)
                if assign == None:
                    state[key] = value
                elif assign == True:
                    parities = gje.xor_(value._List__list, parities)
                    partial.append( key)
                elif assign == False:
                    partial.append(-key)
        
        ## Build the matrix from columns state
        xor_lits = [ lit for lit in state ]
        m = [ col._List__list for col in state.values()]
        m.append(parities)
        matrix = np.array(m).T

        ## Check SATISFIABILITY and find consequences
        conflict, clause = gje.check_sat_(matrix, xor_lits)
        ## Detect conflict or clauses before GJE
        if conflict:
            return conflict, partial, clause
        
        ## If there are more than unary xors perform GJE
        if len(matrix[0]) > 2 and len(parities)>1:
            matrix = gje.remove_rows_zeros_(matrix)
            matrix = gje.perform_gauss_jordan_elimination_(matrix, False)

            ## Check SATISFIABILITY and find consequences
            conflict, clause = gje.check_sat_(matrix, xor_lits)

        return conflict, partial, clause


class State_GJE:
    def __init__(self, cutoff):
        self.__states   = []
        self.__columns  = []
        self.__literals = []
        self.__sat = True
        self.__consequences = []
        self.__cutoff = cutoff

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

    def init(self, init):
        """
        Initializes xor constraints based on the symbol table to build a binary matrix.
        This propagator is called on fixpoints to perform Gauss-Jordan Elimination after Unit Propagation
        """
        for thread_id in range(len(self.__states), init.number_of_threads):
            self.__states.append({})
            self.__columns.append({})

        init.check_mode = clingo.PropagatorCheckMode.Fixpoint

        ## Get the constraints
        ret = util.symbols_to_xor_r(init.symbolic_atoms, util.default_get_lit(init))
        
        if ret is None:
            self.__sat = False
        elif ret is not None:
            # NOTE: whether facts should be handled here is up to question
            #       this should only be necessary if the propagator is to be used standalone
            #       without any of the other approaches
            constraints, facts = ret
            self.__consequences.extend(facts)

            ## Get the literals and parities
            pars = []
            literals = []
            for constraint in constraints:
                # Consequences
                if len(constraint) == 1:
                    lit = next(iter(constraint))
                    self.__consequences.append(lit if constraint[0] > 1 else -lit)
                # Watch XOR
                elif len(constraint):
                    xor = XOR(constraint)
                    self.__add_watch(init, xor, 0, range(init.number_of_threads))
                    self.__add_watch(init, xor, 1, range(init.number_of_threads))
                # Get literals
                for lit in constraint:
                    value = init.assignment.value(lit)
                    if value == None and abs(lit) not in literals:
                        literals.append(abs(lit))
            
                # FIXME: check if there is another way to do this. All constraints are represented as "odd" constraints but GJE only uses non-negative variables/literals.
                # Somehow we need to convert xor constraints with a negative into a positive literal and invert the parity to build the matrix.
                # Get parities
                if constraint[0] < 0:
                    pars.append(0)
                else:
                    pars.append(1)

            # Sort literals
            self.__literals = List(sorted(literals))
            
            # Add parities to the state
            for thread_id in range(init.number_of_threads):
                self.__columns[thread_id]["parity"] = List(np.array(pars))
                
            # Build the rest of the matrix
            matrix = []
            for constraint in constraints:
                matrix.append(gje.lits_to_binary_(constraint, literals))

            # Transpose
            matrix = np.array(matrix).T
            for thread_id in range(init.number_of_threads):
                for i in range(len(literals)):
                    self.__columns[thread_id][literals[i]] = List(matrix[i])
            
        else:
            # NOTE: if the propagator is to be used standalone, this case has to be handled
            pass
        

    def check(self, control):
        """
        Check if current assignment is conflict-free, detect a conflict or deduce literals
        by doing Gauss-Jordan Elimination
        """
        """
        Since the XOR constraint above handles only constraints with at least
        two literals, here the other two cases are handled.

        Empty conflicting constraints result in top-level conflicts and unit
        constraints will be propagated on the top-level.
        """
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
        state     = self.__states[control.thread_id]
        columns   = self.__columns[control.thread_id]
        cutoff    = self.__cutoff
        
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
                    conflict, partial, clause = xor.reason_gje(columns, control.assignment, cutoff)
                    if conflict:
                        if not control.add_nogood(partial):
                            return
                    elif clause:
                        for lit in clause:
                            if not control.add_nogood(partial+[-lit]):
                                return                                
                    
            if len(state[variable]) == 0:
                control.remove_watch( variable)
                control.remove_watch(-variable)
                state.pop(variable)
