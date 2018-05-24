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
    mm = []
    m = np.array(m)

    #Pre work... Remove rows with all zeros
    sums = m.sum(axis=1)
    for i in range(len(sums)):
        if sums[i] != 0:
            mm.append(m[i].tolist())

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


def perform_gauss_jordan_elimination(m):
    """ Perform GJE using swap and xor operations """
    dimension = len(m)
    if len(m) > len(m[0]):
        dimension = len(m[0])

    ## "Forward Elimination"
    i = 0
    j = 0
    for r in range(dimension):
        if m[i][j] == 0:
            ## Swap and Process Column
            for c in range(r+1,len(m)):
                if m[c][r] == 1:                
                    m = swap(m, r, c)
                    break

        ## Check for 1s to XOR
        for c in range(r+1,len(m)):
            if m[c][r] == 1:
                m = xor(m,r,c)
        i+=1
        j+=1    

    ## "Backward Substitution"
    for r in range(dimension, 1, -1):
        ## Check for 1s to XOR
        for c in range(r, 1, -1):
            if m[i-1][j-1] == 1 and m[c-1-1][r-1] == 1:
                m = xor(m,r-1,c-1-1)
        i-=1
        j-=1

    return m   
