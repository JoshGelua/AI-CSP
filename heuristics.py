#Look for #IMPLEMENT tags in this file. These tags indicate what has
#to be implemented.

import random
'''
This file will contain different variable ordering heuristics to be used within
bt_search.

var_ordering == a function with the following template
    var_ordering(csp)
        ==> returns Variable

    csp is a CSP object---the heuristic can use this to get access to the
    variables and constraints of the problem. The assigned variables can be
    accessed via methods, the values assigned can also be accessed.

    var_ordering returns the next Variable to be assigned, as per the definition
    of the heuristic it implements.

val_ordering == a function with the following template
    val_ordering(csp,var)
        ==> returns [Value, Value, Value...]

    csp is a CSP object, var is a Variable object; the heuristic can use csp to access the constraints of the problem, and use var to access var's potential values.

    val_ordering returns a list of all var's potential values, ordered from best value choice to worst value choice according to the heuristic.

'''

def ord_mrv(csp):
    variable = None
    degree = -float("inf")
    unassigned_vars = csp.get_all_unasgn_vars()
    for var in unassigned_vars:
        domain_size = var.cur_domain_size()
        if variable is None:
            variable = var
            degree = domain_size
        elif domain_size < degree:
            variable = var
            degree = domain_size
    return variable

def val_lcv(csp, var):
    count = {}
    for domain in var.cur_domain():
        var.assign(domain)
        sum = 0
        constraints = csp.get_cons_with_var(var)
        for con in constraints:
            unassigned_vars = con.get_unasgn_vars()
            for variable in unassigned_vars:
                current_domain = variable.cur_domain()
                for dom in current_domain:
                    if not con.has_support(variable, dom):
                        sum += 1
        var.unassign()
        count[domain] = sum

    vals = sorted(count, key=count.get, reverse=False)
    return vals
