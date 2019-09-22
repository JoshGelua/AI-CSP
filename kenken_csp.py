#Look for #IMPLEMENT tags in this file.
'''
All models need to return a CSP object, and a list of lists of Variable objects
representing the board. The returned list of lists is used to access the
solution.

For example, after these three lines of code

    csp, var_array = kenken_csp_model(board)
    solver = BT(csp)
    solver.bt_search(prop_FC, var_ord)

var_array[0][0].get_assigned_value() should be the correct value in the top left
cell of the KenKen puzzle.

The grid-only models do not need to encode the cage constraints.

1. binary_ne_grid (worth 10/100 marks)
    - A model of a KenKen grid (without cage constraints) built using only
      binary not-equal constraints for both the row and column constraints.

2. nary_ad_grid (worth 10/100 marks)
    - A model of a KenKen grid (without cage constraints) built using only n-ary
      all-different constraints for both the row and column constraints.

3. kenken_csp_model (worth 20/100 marks)
    - A model built using your choice of (1) binary binary not-equal, or (2)
      n-ary all-different constraints for the grid.
    - Together with KenKen cage constraints.

'''
from itertools import *
from cspbase import *

def binary_ne_grid(kenken_grid):
    n = kenken_grid[0][0]
    variables = []
    constraints = []
    value_list = []
    tuple_list = []
    for i in range(n):
        y_variables = []
        for j in range(n):
            y_variables.append(Variable("%d%d"%(i,j), domain = list(range(1, n+1))))
        variables.append(y_variables)
    for row in variables:
        for var in row:
            value_list.append(var)
    csp = CSP("binary_ne_grid", value_list)
    for tuple in permutations(list(range(1, n+1)), 2):
        tuple_list.append(tuple)
    for i in range(n):
        for j in range(n):
            for k in range(j+1, n):
                cons = Constraint("r%d%d%d"%(i,j,k), [variables[i][j], variables[i][k]])
                cons.add_satisfying_tuples(tuple_list)
                constraints.append(cons)

                cons = Constraint("c%d%d%d"%(i,j,k), [variables[j][i], variables[k][i]])
                cons.add_satisfying_tuples(tuple_list)
                constraints.append(cons)
    for constraint in constraints:
        csp.add_constraint(constraint)

    return csp, variables

def nary_ad_grid(kenken_grid):
    n = kenken_grid[0][0]
    variables = []
    tuple_list = []
    row_vars = []
    col_vars= []
    csp = CSP("nary_ad_grid")
    for i in range(1, n + 1):
        row_vars.append([])
        col_vars.append([])
    for i in range(1, n + 1):
        y_variables = []
        for j in range(1, n + 1):
            new_var = Variable("%d%d"%(i, j), domain = list(range(1, n+1)))
            row_vars[i - 1].append(new_var)
            col_vars[j - 1].append(new_var)
            csp.add_var(new_var)
            y_variables.append(new_var)
        variables.append(y_variables)
    for tuple in permutations(list(range(1, n + 1)), n):
        tuple_list.append(tuple)
    for i in range(1, n + 1, 1):
        cons = Constraint("r%d"%(i), row_vars[i - 1])
        cons.add_satisfying_tuples(tuple_list)
        csp.add_constraint(cons)

        cons = Constraint("c%d"%(i), col_vars[i - 1])
        cons.add_satisfying_tuples(tuple_list)
        csp.add_constraint(cons)
    return csp, variables


def kenken_csp_model(kenken_grid):
    variables = []
    size = kenken_grid[0][0]
    n = size
    csp = CSP("Kenken")
    for i in range(1, n + 1):
        row = []
        for j in range(1, n + 1):
            row.append(Variable("%d%d"%(i, j), domain = list(range(1, n+1))))
        variables.append(row)
    cons = []
    kenken_len = len(kenken_grid)
    for cage in range(1, kenken_len):
        if(len(kenken_grid[cage]) == 2):
            row_index = int(str(kenken_grid[cage][0])[0]) - 1
            col_index = int(str(kenken_grid[cage][0])[1]) - 1
            target_num = kenken_grid[cage][1]
            variables[i][j] = Variable("%d%d"%(i, j), [target_num])
        else:
            operation = kenken_grid[cage][-1]
            target_num = kenken_grid[cage][-2]
            cage_vars = []
            domain = []
            for cell in range(len(kenken_grid[cage]) - 2):
                row = int(str(kenken_grid[cage][cell])[0]) - 1
                col = int(str(kenken_grid[cage][cell])[1]) - 1
                cage_vars.append(variables[row][col])
                domain.append(variables[row][col].domain())
            cage_tuple = []
            con = Constraint("cage%d"%(cage), cage_vars)
            prod_domain = product(*domain)
            for dom in prod_domain:
                if (operation == 0):
                    sum = 0
                    for num in dom:
                        sum += num
                    if (sum == target_num):
                        cage_tuple.append(dom)
                elif (operation == 1):
                    for num in permutations(dom):
                        sub = num[0]
                        for n in range(1, len(num)):
                            sub -= num[n]
                        if(sub == target_num):
                            cage_tuple.append(dom)
                elif (operation == 2):
                    for num in permutations(dom):
                        quo = num[0]
                        for n in range(1, len(num)):
                            quo = quo/num[n]
                        if(quo == target_num):
                            cage_tuple.append(dom)
                elif (operation == 3):
                    prod = 1
                    for num in dom:
                        prod *= num
                    if (prod == target_num):
                        cage_tuple.append(dom)
            con.add_satisfying_tuples(cage_tuple)
            cons.append(con)

    for i in range(size):
        for j in range(size):
            for k in range(len(variables[i])):
                if (k > j):
                    row_var1 = variables[i][j]
                    row_var2 = variables[i][k]
                    con = Constraint("r%d%d%d%d)"%(i+1, j+1, i+1, k+1), [row_var1, row_var2])
                    row_tuples = []
                    for dom in product(row_var1.domain(), row_var2.domain()):
                        if dom[0] != dom[1]:
                            row_tuples.append(dom)
                    con.add_satisfying_tuples(row_tuples)
                    cons.append(con)
                if (k > i):
                    col_var1 = variables[i][j]
                    col_var2 = variables[k][j]
                    con = Constraint("c%d%d%d%d)"%(i+1, j+1, k+1, j+1), [col_var1, col_var2])
                    col_tuples = []
                    for dom in product(col_var1.domain(), col_var2.domain()):
                        if dom[0] != dom[1]:
                            col_tuples.append(dom)
                    con.add_satisfying_tuples(col_tuples)
                    cons.append(con)
    for row in variables:
        for var in row:
            csp.add_var(var)
    for con in cons:
        csp.add_constraint(con)
    return csp, variables
