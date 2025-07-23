#!/usr/bin/env python
# coding: utf-8

# In[1]:


# TODO
# -remove first AND node if there is only one main component and no setted literals
# -remove false nodes by pushing them up (hence removing nodes)
# -test permutations of components (manually)


# In[2]:


import numpy as np


# In[3]:


def var_orders_to_perm(variable_order, variable_order_prev_component):
    if variable_order == None and variable_order_prev_component == None:
        return "[ ]"
    if variable_order == None or variable_order_prev_component == None:
        raise (notImplemetedError)
        return "[ ]" #TODO implement correct permutation
    assert(len(variable_order) == len(variable_order_prev_component))
    permutation = "[ "
    for i in range(len(variable_order)):
        permutation += str(variable_order[i])+">"+str(variable_order_prev_component[i])+" "
    permutation += "]"
    return permutation


# In[4]:


# Top down reading file

def trace_to_nnf(content,output_file):
    """
    outputs file which lines are unordered: every line starts with index that should be line number
    """

    with open(output_file, "w") as f:
    
        variable_stack = []
        componentID_to_outputline = {}
        outputline_to_variableorder = {}

        lines_stack = []        
        # tuple that represents a node (line, branching literal, variables). 
        # branching literal is 0 for components (OR nodes). 
        # variables are the unasigned variables in a component
        
        output_line = 2
        line = 0
        set_lits = set()
        while (line<len(content)):
            #print("handling line",line)
            if (content[line][0:8] == "deciding"):
                lit = int(content[line].split()[-1])
                var = abs(lit)
                first_component_output_line = output_line
        
                # check if variable is part of component
                i=2
                while (not(str(var) in lines_stack[-1][2])):
                    lines_stack[-1],lines_stack[-i] = lines_stack[-i],lines_stack[-1]
                    i+=1
                assert(str(var) in lines_stack[-1][2])
                
                print(str(lines_stack[-1][0])+" O "+str(var)+" 2 "+str(first_component_output_line)+" [ ] "+str(output_line+1)+" [ ]", file=f)
                vars = lines_stack[-1][2]
                vars.remove(str(var))
                lines_stack.pop()
                lines_stack.append((output_line+1,-lit,vars))
                lines_stack.append((output_line,lit,vars))
                
                #second_branch_output_line[var] = output_line+1
                #second_branch_parity[var] = -lit/var
        
                output_line = output_line + 2
            
                variable_stack.append(var)
        
                line += 1
        
                # check set/unset
                set_lits = set()
                while (content[line][0:11] == "set literal") or (content[line][0:13] == "unset literal"):
                    literal = int(content[line].split()[-1])
                    if (content[line][0:11] == "set literal"):
                        set_lits.add(literal)
                    else: #unset literal
                        set_lits.remove(literal)
                    line += 1
                
                # find components
                comps = []
                new_comps = []
                while (content[line][0:9] == "Cache hit") or (content[line][0:13] == "New component") or (content[line][0:14] == "variable order"):
                    if (content[line][0:14] == "variable order"):
                        variable_order = content[line].split()[2:]
                        line += 1
                    else:
                        variable_order = None
                    
                    if (content[line][0:9] == "Cache hit"):
                        equiv_component = content[line].split()[-1]
                        outputline = componentID_to_outputline.get(equiv_component)
                        variable_order_prev_component = outputline_to_variableorder.get(outputline)
                        permutation = var_orders_to_perm(variable_order, variable_order_prev_component)
                        
                    if (content[line][0:13] == "New component"):
                        new_component = content[line].split()[-1]
                        componentID_to_outputline[new_component] = output_line
                        outputline = output_line
                        output_line += 1
                        vars = content[line+1].split()[1:]
                        outputline_to_variableorder[outputline] = variable_order
                        new_comps.append((outputline,vars))
                        permutation = "[ ]"# identitypermutation(vars)
                        
                    comps.append(str(outputline)+" "+permutation)
                    #vars = content[line+1].split()[1:]
                    line+=2
                if comps != []:
                    line-=1
        
                
        
                if comps != []:
                    #literal_output_line = output_line
                    #print(str(literal_output_line)+" L "+str(lit), file=f)
                    #output_line += 1
                    literal_output_line = "x [ "+str(lit)+">1 ]"
                    
                    set_lit_lines = []
                    for l in set_lits:
                        #print(str(output_line)+" L "+str(l), file=f)
                        #set_lit_lines.append(output_line)
                        #output_line += 1
                        
                        set_lit_lines.append("x [ "+str(l)+">1 ]")
                    
                    print(str(lines_stack[-1][0])+" A "+str(len(comps)+len(set_lits)+1)+" "+str(literal_output_line),*set_lit_lines,*comps, file=f)
                    lines_stack.pop()
                    for (comp,vars) in new_comps:
                        lines_stack.append((comp,0,vars))
                else:
                    assert(content[line][0:15] == "branch is UNSAT" or content[line][0:13] == "branch is SAT")
                    if (content[line][0:15] == "branch is UNSAT"):
                        print(str(lines_stack[-1][0])+" O 0 0", file=f)
                        lines_stack.pop()
                    else:
                        #literal_output_line = output_line
                        #print(str(literal_output_line)+" L "+str(lit), file=f)
                        #output_line += 1
                        literal_output_line = "x [ "+str(lit)+">1 ]"
                        
                        set_lit_lines = []
                        for l in set_lits:
                            #print(str(output_line)+" L "+str(l), file=f)
                            #set_lit_lines.append(output_line)
                            #output_line += 1

                            set_lit_lines.append("x [ "+str(l)+">1 ]")
                            
                        print(str(lines_stack[-1][0])+" A "+str(len(set_lits)+1)+" "+str(literal_output_line),*set_lit_lines, file=f)
                        lines_stack.pop()
                    set_lits = set()
                
                set_lits = set()
                comps = []
                
            elif ((content[line][0:9] == "Cache hit") or (content[line][0:13] == "New component")) or (content[line][0:14] == "variable order"):
                
                # find components
                comps = []
                new_comps = []                    
                
                while (content[line][0:9] == "Cache hit") or (content[line][0:13] == "New component") or (content[line][0:14] == "variable order"):
                    if (content[line][0:14] == "variable order"):
                        variable_order = content[line].split()[2:]
                        line += 1
                    else:
                        variable_order = None
                    
                    if (content[line][0:9] == "Cache hit"):
                        equiv_component = content[line].split()[-1]
                        outputline = componentID_to_outputline.get(equiv_component)
                        variable_order_prev_component = outputline_to_variableorder.get(outputline)
                        permutation = var_orders_to_perm(variable_order, variable_order_prev_component)
                        
                    if (content[line][0:13] == "New component"):
                        new_component = content[line].split()[-1]
                        componentID_to_outputline[new_component] = output_line
                        outputline = output_line
                        output_line += 1
                        vars = content[line+1].split()[1:]
                        outputline_to_variableorder[outputline] = variable_order
                        new_comps.append((outputline,vars))
                        permutation = "[ ]"# identitypermutation(vars)
                        
                    comps.append(str(outputline)+" "+permutation)
                    #vars = content[line+1].split()[1:]
                    line+=2
                if comps != []:
                    line-=1
        
                #lit = lines_stack[-1][1]
                #literal_output_line = output_line
                #print(str(literal_output_line)+" L "+str(lit), file=f)
                #output_line += 1
                if (lines_stack != []): # this is not the first component of the search
                    if not(set_lits == set()):
                        # check if variable is part of component
                        for var in set_lits:
                            absvar = abs(var)
                            if (var == lines_stack[-1][1]):
                                continue
                            i=2
                            while (not(str(absvar) in lines_stack[-1][2])):
                                lines_stack[-1],lines_stack[-i] = lines_stack[-i],lines_stack[-1]
                                i+=1
                            assert(str(absvar) in lines_stack[-1][2])
                            break
                
                set_lit_lines = []
                for l in set_lits:
                    #print(str(output_line)+" L "+str(l), file=f)
                    #set_lit_lines.append(output_line)
                    #output_line += 1
                    set_lit_lines.append("x [ "+str(l)+">1 ]")

                if (lines_stack != []):
                    print(str(lines_stack[-1][0])+" A "+str(len(comps)+len(set_lits)),*set_lit_lines,*comps, file=f)
                    lines_stack.pop()
                else:
                    print("1 A "+str(len(comps)+len(set_lits)),*set_lit_lines,*comps, file=f)
                for (comp,vars) in new_comps:
                    lines_stack.append((comp,0,vars))
        
                set_lits = set()
                comps = []
                
        
                
            elif (content[line][0:12] == "backtracking"):
                #print(str(lines_stack[-1][0])+" O "+str(var)+" 2 "+str(first_component_output_line)+" "+str(output_line+1), file=f)
                #lines_stack.pop()
                if lines_stack == []:
                    print("empty lines_stack")
                line += 1
                continue
            elif (content[line][0:16] == "in second branch"): #component in new branch
                #var = int(content[line].split()[-1])
                #print(var, file=f)
                line += 1
                continue
            elif (content[line][0:15] == "branch is UNSAT"):
                if (content[line-1][0:11] == "set literal" or content[line-1][0:13] == "unset literal" or content[line][0:8] == "deciding"):
                    print(str(lines_stack[-1][0])+" O 0 0", file=f)
                    #if (int(content[line].split()[-1]) == 1):
                    lines_stack.pop()
                    set_lits = set()
                
            elif (content[line][0:13] == "branch is SAT"):
                set_lit_lines = []
                for l in set_lits:
                    #print(str(output_line)+" L "+str(l), file=f)
                    #set_lit_lines.append(output_line)
                    #output_line += 1
                    set_lit_lines.append("x [ "+str(l)+">1 ]")
                    
                if (content[line-1][0:11] == "set literal" or content[line-1][0:13] == "unset literal" or content[line-1][0:8] == "deciding"):
                    print(str(lines_stack[-1][0])+" A "+str(len(set_lits)),*set_lit_lines, file=f)
                    #if (int(content[line].split()[-1]) == 1):
                    lines_stack.pop()
                    set_lits = set()
        
            elif (content[line][0:11] == "set literal"):
                literal = int(content[line].split()[-1])
                #print(set_lits,literal)
                set_lits.add(literal)
            elif (content[line][0:13] == "unset literal"):
                literal = int(content[line].split()[-1])
                #print(set_lits,literal)
                set_lits.remove(literal)
            elif (content[line][0:7] == "restart"):
                print("Symganak has restarted. nnf output is probably wrong")
                set_lits = set()
            else:
                print("line",line,"not handled")
                
            line+=1
            #print(line,lines_stack, file=f)
        print(str(output_line)+" L 1",file=f)
    f.close()


    # replace x by final line number
    final_line = output_line
    file = open(output_file, "r")
    content = file.read()
    file.close()
    new_file = content.replace('x',str(final_line))
    with open(output_file, "w") as f:
        f.write(new_file)


# In[9]:


def find_N_variables(content):
    N_variables = 0
    for line in content:
        for elt in line.split():
            if ">" in elt:
                lit1,lit2 = elt.split(">")
                N_variables = np.max([N_variables,abs(int(lit1)),abs(int(lit2))])
    return N_variables

def order_nnf(file):
    """
    Make sure that lines of nnf are ordered: childs are before fathers
    """
    f = open(file, "r")
    content = f.readlines()
    f.close()

    new_line = 0
    new_line_order = np.full(len(content),None)

    N_nodes = len(content)
    N_edges = 0

    N_variables = find_N_variables(content)
    # we don't know for sure here which variables were in original formula: free variables are not in trace of symganak. 
    # Should be printed to trace of symganak

    for line in range(len(content)): # handle leaves
        if content[line][0] == "L":
            new_line_order[line] = new_line
            new_line += 1
            
    while None in new_line_order: # handle or/and nodes
        for line in np.arange(len(content)-1,-1,-1): 
            if new_line_order[line] != None:
                continue
                
            if content[line][0] == "A":        
                N_components = int(content[line].split()[1])
                components = []
                comparts = content[line].split()
                compart = 2
                    
            elif content[line][0] == "O":
                N_components = int(content[line].split()[2])
                components = []
                comparts = content[line].split()
                compart = 3
                
            elif content[line][0] == "L":
                continue
                
            # gather components of current line
            while compart < len(comparts):
                if not(("[" in comparts[compart]) or ("]" in comparts[compart]) or (">" in comparts[compart])):
                    components.append(comparts[compart])
                    N_edges += 1
                compart += 1
        
            # check if components are on previous line
            ordered = True
            for component in components:
                if new_line_order[int(component)-1] == None:
                    ordered = False
                    break
            if ordered:
                new_line_order[line] = new_line
                new_line += 1

    

    # reorder lines in nnf and rewrite line numbers
    inv_new_line_order = np.full(len(content),None)
    for i in range(len(new_line_order)):
        inv_new_line_order[new_line_order[i]] = i
    with open(file, "w") as f:
        print("nnf {} {} {}".format(N_nodes,N_edges,N_variables),file=f)
        for i in range(len(content)):
            line = content[inv_new_line_order[i]]
            comparts = line.split()
            if comparts[0] == "L":
                compart = 2
            elif comparts[0] == "A":
                compart = 2
            elif comparts[0] == "O":
                compart = 3
        
            while compart<len(comparts):
                if not("[" in comparts[compart]) and not("]" in comparts[compart]) and not(">" in comparts[compart]):
                    comparts[compart] = str(new_line_order[(int(comparts[compart])-1)])
                compart+=1
            print(' '.join(comparts),file=f)  # write new line to file

    return 


# In[10]:


def order_unnf(unordered,output_file):

    file = open(unordered, "r")
    content = file.readlines()
    file.close()

    n = len(content)

    ordered_content = np.full(n,None)
    for i in range(n):
        comparts = content[i].split()
        new_line = int(comparts[0])-1
        ordered_content[new_line] = ' '.join(comparts[1:])

    with open(output_file, "w") as f:
        for i,line in enumerate(ordered_content):
            if line == None:
                print("line not found",i+1)
            else:
                print(line,file=f)
        """
        for i in np.arange(1,n+1):
            stringi = str(i)
            for j in range(n):
                if (content[j].split()[0] == stringi):  #this operation should be made faster
                    #print("hit",i,j)
                    print(*content[j].split()[1:],file=f)
                    break
                if (j == n-1):
                    print("line not found",i,j)
        """
                    
    order_nnf(output_file)


# In[15]:


# Open the file in read mode
file = open("symganak.trace", "r")

# Read the entire content of the file
content = file.readlines()

#print(content)

# Close the file
file.close()


# In[16]:


trace_to_nnf(content,"output.unnf") # outputs unordered nnf
print("halfway")
order_unnf("output.unnf","output.nnf")


# In[ ]:




