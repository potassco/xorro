from . import util
from . import gje
from itertools import chain
import clingo

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

    def reason(self, assignment, i):
        """
        If the constraint is unit resulting or conflicting returns a reason in
        form of a clause.
        """
        # Switch to the index of the other watched literal that is either
        # unassigned and has to be propagated or has to be checked for a
        # conflict. In the second case it was assigned on the same level as the
        # propagated literal.
        i = 1 - i
        count = 0
        clause = []
        for j in range(len(self)):
            if i == j:
                continue
            if assignment.is_true(self[j]):
                clause.append(-self[j])
                count += 1
            else:
                clause.append(self[j])

        clause.append(-self[i] if count % 2 else self[i])

        return None if assignment.is_true(clause[-1]) else clause

class Simplex_GJE:
    def __init__(self, cutoff):
        self.__states  = []
        self.__states_gje = []
        self.__sat = True
        self.__consequences = []
        self.__cutoff = cutoff
        self.__literals = []
        self.__matrix = []
        self.__basic_lits = []
        self.__non_basic_lits = []

        
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
            self.__states_gje.append({})

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

            """
            How the preprocessing works:
            Get all the literals involved in parity constraints
            Build the matrix and perform a GJE procedure
            Rebuild the XORs after reducing the matrix
            Count the number of XORs of length greater than 2. If more than one exist, it is worth it to keep the matrix
            Else, if exist only one longer XOR or XORs of lenght 2, do not keep the matrix and no GJE is done. Add these XORs to the UP state
            Else, if exist XORs of size 1, extend the consquences list
            If the matrix is not kept, the propagator runs as the UP approach
            Else, if the matrix exist, we need to identify the basic and non basic literals
            TODO: Analyze if the XORs belonging to the matrix are going to be handled in the same state as the other XORs or separately.
            """
            print "constraints", constraints
            for constraint in constraints:
                for lit in constraint:
                    if abs(lit) not in self.__literals:
                        self.__literals.append(abs(lit))
            
            # Build Matrix
            for constraint in constraints:
                row = []
                for lit in self.__literals:
                    if lit in constraint or -lit in constraint:
                        row.append(1)
                    else:
                        row.append(0)
                # If even constraint
                if constraint[0] < 0:
                    row.append(0)
                else:
                    row.append(1)
                self.__matrix.append(row)

            # Preprocess by reducing the matrix to Reduced Row Echelon Form
            print "Initial Matrix"
            gje.print_matrix(self.__matrix)
            self.__matrix = gje.perform_gauss_jordan_elimination(self.__matrix,False)
            print "Reduced Matrix"
            gje.print_matrix(self.__matrix)

            constraints = []
            ## Rebuild XORs after initial GJE
            ## Check cases if XORs of size 1, 2 or greater or equal than 3.
            print "Rebuild xors"
            for row in self.__matrix:
                constraint = []
                for i in range(len(row)-1):
                    if row[i] == 1:
                        constraint.append(self.__literals[i])
                if constraint:
                    if row[-1] == 0:
                        constraint[0] = -constraint[0]
                    constraints.append(constraint)

            print constraints
            longer_xor = 0
            for constraint in constraints:
                if len(constraint) > 2:
                    longer_xor+=1

            matrix = self.__matrix
            self.__matrix = []

            ## Check for constraints after reduced matrix
            for constraint in constraints:
                if len(constraint) == 0:
                    self.__sat = False
                    break
                if len(constraint) == 1:
                    ## Consequences
                    self.__consequences.extend(constraint)
                    pos = self.__literals.index(abs(constraint[0]))
                    for row in self.__matrix:
                        del row[pos]
                    self.__literals.pop(pos)
                elif longer_xor < 2:
                    ## UP
                    xor = XOR(constraint)
                    self.__add_watch(init, xor, 0, range(init.number_of_threads))
                    self.__add_watch(init, xor, 1, range(init.number_of_threads))
                elif longer_xor >= 2:
                    ## For GJE
                    pos = constraints.index(constraint)
                    self.__matrix.append(matrix[pos])
                    #xor = XOR(constraints[i]) ## This case has to be treated
                    #self.__add_watch(init, xor, 0, range(init.number_of_threads), self.__states_gje)
                    #self.__add_watch(init, xor, 1, range(init.number_of_threads), self.__states_gje)

            ## Get basic and non basic literals
            number_basics = len(self.__matrix)
            if number_basics > 0:
                print ""
                print "literals", self.__literals
                gje.print_matrix(self.__matrix)
                print constraints

                self.__basic_lits = self.__literals[0:number_basics]
                print "basic lits", self.__basic_lits
                self.__non_basic_lits = self.__literals[number_basics:]
                print "non basic lits", self.__non_basic_lits
                                            
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
        state  = self.__states[control.thread_id]
        #print state
        for literal in changes:
            #print literal
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

                    clause = xor.reason(control.assignment, unassigned)
                    if clause is not None:
                        if not control.add_clause(clause) or not control.propagate():
                            assert(state[variable])
                            # reestablish the remaining watches with the same
                            # reason as in (*)
                            state[variable].extend(watches[i + 1:])
                            return

            if len(state[variable]) == 0:
                control.remove_watch( variable)
                control.remove_watch(-variable)
                state.pop(variable)
