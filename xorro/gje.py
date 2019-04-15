"""
This module contains all the methods to perform Gauss Jordan Elimination. 

Functions:
For pre process
columns_state_to_matrix -- Transform the state of columns to a single matrix including the parity column
xor_columns             -- Perform xor operation of a single column to the parity column

For GJE
perform_gauss_jordan_elimination -- Entire GJE process
swap -- Sub module for GJE to swap rows
xor  -- Sub module for GJE to xor rows

check_sat      -- Check satisfiability after performing GJE
deduced_clause -- Obtain implications after GJE
"""

import numpy as np

def print_matrix(m):
    for row in m:
        print(row)
    print("")
    
def swap(m, r1, r2):
    """ Swap rows in forward elimination"""
    temp  = m[r1]
    m[r1] = m[r2]
    m[r2] = temp
    return m

def xor(m, i, j):
    """ XOR rows during GJE"""
    for e in range(len(m[0])):
        m[j][e] ^= m[i][e]
    return m

def xor_columns(col, parity):
    """ XOR a column with the parity values from the state  """
    result = []
    for i in range(len(col)):
        result.append(col[i] ^ parity[i])
    return result

def columns_state_to_matrix(state):
    """ Transform the state of columns to a single matrix including the parity column """
    m = []
    lits = []
    for key, values in state.items():
        if key != "parity":
            m.append(values)
            lits.append(key)
    m += [state["parity"]]
    m = np.array(m).T.tolist()
    return m, lits

def remove_rows_zeros(m):
    matrix = []
    for row in m:
        if sum(row) > 0:
            matrix.append(row)
    return matrix

def check_sat(m):
    """ Check the matrix satisfiability wrt the augmented (parity) column  """
    conflict = False
    matrix = np.array(m)

    ## If only augmented column remains
    if len(matrix[0]) == 1:
        for i in range(len(matrix)):
            if matrix[i,0] == 1:
                conflict = True
                break
    else:
        ## Check if exist empty odd which means UNSAT i.e. a conflict
        for row in matrix[::-1]:
            if row[-1] == 1 and np.sum(row[:-1]) == 0:
                ## UNSAT
                conflict = True                        
                break 
    return conflict

def deduce_clause(m, lits):
    """ If no conflict, deduce the implications after GJE """
    clause = []

    #Pre work... Remove rows with all zeros
    mm = remove_rows_zeros(m)
    matrix = np.array(mm)

    ## If empty matrix, means there are no implications
    if matrix.size > 0:
        ## If matrix is square
        if len(matrix) >= (len(matrix[0])-1):                 
            for i in range(len(lits)):
                if matrix[i,-1] == 1:
                    clause.append( lits[i])
                else:
                    clause.append(-lits[i])
        else: ## Rectangular matrix
            for row in matrix:
                if np.sum(row[:-1]) == 1:
                    index = np.where(row[:-1] == 1)[0][0]
                    if row[-1] == 1:
                        clause.append( lits[index])
                    else:
                        clause.append(-lits[index])
    return clause


def perform_gauss_jordan_elimination(m, show):
    """ 
    Perform GJE using swap and xor operations.
    Print options are available using the show flag for tests/debbuging to check the GJE Procedure.
    """
    if show:
        print("Initial State")
        print_matrix(m)

    r, c = 0, 0
    rows = len(m)
    cols = len(m[0])

    if show:
        print("rows: %s cols: %s"%(rows, cols))

    while True:
        _swap = False

        if show:
            print("r %s c %s"%(r, c))

        ## Check Pivot
        if m[r][c] == 0:
            ## Swap
            for i in range(rows):
                if r != i and i > r: ## Avoid comparing the same row and do not swap to upper rows
                    if m[i][c] == 1 and not _swap: ## Check if a swap is not performed before in the same column
                        if show:
                            print("Swapping %s %s and %s %s"%(r, m[r], i, m[i]))
                        #m = swap(m,r,i)
                        temp  = m[r]
                        m[r]  = m[i]
                        m[i]  = temp
                        _swap = True
                        if show:
                            print_matrix(m)
            if not _swap: ## If not swap, means there is no 1 to swap, so go to the next column
                c+=1

        if m[r][c] == 1:
            ## XOR
            for i in range(rows):
                if r != i: ## Avoid comparing the same row
                    if m[i][c] == 1:
                        if show:
                            print("XOR Row %s: %s  into Row %s: %s"%(r, m[r], i, m[i]))
                        for e in range(len(m[0])):
                            m[i][e] ^= m[r][e]
                        if show:
                            print_matrix(m)

        ## Increase row and column
        r+=1
        c+=1

        ## break condition if all rows or all columns (except the augmented column are treated)
        if r == rows or c >= cols-1:
            break
        
    return m

"""
Updated methods using only numpy
"""
def lits_to_binary_(constraint, literals):
    row = []
    for lit in literals:
        if lit in constraint or -lit in constraint:
            row.append(1)
        else:
            row.append(0)
    return row

def remove_rows_zeros_(m):
    matrix = []
    for row in m:
        if np.sum(row) > 0:
            matrix.append(row)
    return np.array(matrix)

def xor_(l1, l2):
    """ XOR a column with the parity values from the state  """
    return np.bitwise_xor(l1,l2)

def check_sat_(m, lits):
    """ Check the matrix satisfiability wrt the augmented (parity) column  and get implications if no conflict """
    conflict = False
    clause   = []

    ## If only augmented column remains
    if len(m[0]) == 1:
        if np.sum(m[:,0]) > 0:
            conflict = True
    else:
        ## Check if exist empty odd which means UNSAT i.e. a conflict
        for row in m[::-1]:
            if row[-1] == 1 and np.sum(row[:-1]) == 0:
                ## UNSAT
                conflict = True                        
                break
            elif np.sum(row[:-1]) == 1:
                ## Unit XOR
                i, = np.where(row[:-1] == 1)[0]
                if row[-1] == 1:
                    if  lits[i] not in clause:
                        clause.append( lits[i])
                else:
                    if -lits[i] not in clause:
                        clause.append(-lits[i])
    return conflict, clause

def perform_gauss_jordan_elimination_(m, show):
    """ 
    Perform GJE using swap and xor operations.
    Print options are available using the show flag for tests/debbuging to check the GJE Procedure.
    """
    if show:
        print m
        print("Initial State")
        print_matrix(m)
    
    r = 0
    c = 0
    rows, cols = len(m), len(m[0])

    if show:
        print("rows: %s cols: %s"%(rows, cols))

    while True:
        if show:
            print("r %s c %s"%(r, c))

        ## Check Pivot
        _swap = False
        if m[r,c] == 0:
            for i in range(r+1,rows):
                if m[i,c] == 1:# If new pivot found... swap
                    if show:
                        print("Swapping %s %s and %s %s"%(r, m[r], i, m[i]))
                    m[[i,r]] = m[[r,i]] ## Swap
                    _swap = True
                    if show:
                        print_matrix(m)
                    break # No more swapping in this column
            if not _swap: ## No swap, move to the next column, same row
                c+=1

        if m[r,c] == 1:
            ## XOR
            for i in range(rows):
                indexes = np.setdiff1d(np.where(m[:,c] == 1),r) # Get all the ones to XOR in the same column
                for i in indexes:
                    m[i] = np.bitwise_xor(m[i],m[r]) # Bitwise XOR
                    if show:
                        print("XOR Row %s: %s  into Row %s: %s"%(r, m[r], i, m[i]))
                if show:
                    print_matrix(m)

        ## Increase row and column
        r+=1
        c+=1

        ## break condition if all rows or all columns (except the augmented column) are treated
        if r == rows or c >= cols-1:
            break

    if show:
        print("Final State")
        print_matrix(m)
        
    return m
