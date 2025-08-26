from itertools import combinations
from z3 import *
import numpy as np
from datetime import datetime
import json
import time



################################# PARAMETERS ###############################
team = 6  # default
optimized_version = False
script_filename = 'solutions.json'               # Name if this script is executed for debugging
docker_filename = '/app/outputs/solutions.json'  # Name if this script is executed from docker script
default_filename = script_filename
optimized_label = 'Optimized'
if len(sys.argv) >= 3:
    # Read from command line
    team = int(sys.argv[1])
    yn = sys.argv[2].lower()
    if len(sys.argv) >= 4 and sys.argv[3] == 'docker':
        default_filename = docker_filename
    if yn in ('y', 'yes', 'true', '1'):
        optimized_version = True
else:
    # Interactive input
    team = int(input("\nHow many teams do you want ? "))
    temp = input("Do you want optimized version ? (y/n) ")
    if temp.lower() in ('y', 'yes'):
        optimized_version = True
    temp = input("Are you executing this file using docker ? (y/n) ")
    if temp.lower() in ('y', 'yes'):
        default_filename = docker_filename

# Derivated params
weeks = team-1
if(team % 2 == 0 ):
    periods = team//2
else:
    print("ERROR : Team must be even!")
home = 2
################################# PARAMETERS ###############################



################################# FUNCTIONS and CONSTANT ###############################
solutions = {}

def add_solution_json(m , data , total_time = 0 , optimal = False , obj = None , solution_name = "myAlgorithm"):
    # Choose output destination
   
    match = ['X','X']
    
    sol_list = []
    for p in range(periods):
        period_list = [] # Create one new period list
        for w in range(weeks):
            for t in range(team):
                if(z3.is_true(m[vars[t, 0, p, w]])):
                    match[1] = t+1
                if(z3.is_true(m[vars[t, 1, p, w]])):
                    match[0] = t+1
            period_list.append(match)  # Insert one match
            match = ['X','X']
        sol_list.append(period_list)
    
    new_entry = {}
    new_entry['sol'] = sol_list
    new_entry['time']  = total_time
    new_entry['optimal'] = optimal
    new_entry['obj'] = obj
    data[solution_name] = new_entry

    return data

def import_json_solution(data = solutions , filename=default_filename):
    try:
        with open(filename, "r") as f:
            data = json.load(f)
        return data
    except FileNotFoundError:
        print(f"File {filename} not found. Returning empty dictionary.")
        return {} 
    except Exception:
        print(f"Error during file reading. Returning empty dictionary.") 
        return {}

import json

def export_json_solution_compact(data , filename = default_filename):
    try:
        with open(filename, "w") as f:
            json.dump(data, f, indent=4)
    except Exception as e:
        print(f"Error writing JSON file: {e}")

def export_json_solution(data, filename=default_filename, indent=4, compact_keys=("sol",)):
    """Pretty-print JSON, but keep inner lists in `compact_keys` compact (like [1,2])"""
    def write(obj, f, level=0, parent_key=None):
        pad = " " * (level * indent)

        if isinstance(obj, dict):
            f.write("{\n")
            items = list(obj.items())
            for i, (k, v) in enumerate(items):
                f.write(pad + " " * indent + json.dumps(k) + ": ")
                write(v, f, level + 1, parent_key=k)
                if i < len(items) - 1:
                    f.write(",\n")
            f.write("\n" + pad + "}")

        elif isinstance(obj, list):
            # special formatting for sol
            if parent_key in compact_keys:
                f.write("[\n")
                for i, item in enumerate(obj):
                    f.write(pad + " " * indent)
                    # compact dump of each inner list
                    f.write(json.dumps(item, separators=(",", ":")))
                    if i < len(obj) - 1:
                        f.write(",\n")
                f.write("\n" + pad + "]")
            else:
                f.write("[\n")
                for i, item in enumerate(obj):
                    f.write(pad + " " * indent)
                    write(item, f, level + 1, parent_key=None)
                    if i < len(obj) - 1:
                        f.write(",\n")
                f.write("\n" + pad + "]")

        else:
            f.write(json.dumps(obj))

    try:
        with open(filename, "w") as f:
            write(data, f, 0)
            f.write("\n")
    except Exception as e:
        print(f"Error writing JSON file: {e}")


def visualize_solution_raw(m, file_name=None):
    # Choose output destination
    if file_name:
        f = open(file_name, "w")
        output = f
    else:
        output = sys.stdout

    try:
        print(datetime.now() , file=output)
        for t in range(team):
            print(f"\n\n----------TEAM {t+1}----------", file=output)
            for h in range(home):  # home = 0 (away), 1 (home)
                label = "away : " if h == 0 else "home : "
                print(label, file=output)

                for p in range(periods):
                    for w in range(weeks):
                        temp = z3.is_true(m[vars[t, h, p, w]])
                        print(int(temp), end=" ", file=output)
                    print(file=output)  # Newline after each week row
                
            print(f"-----------------------------", file=output)
    finally:
        if file_name:
            f.close()

# m : is the output of s.model()
def visualize_solution_humanreadable(m, file_name=None):
    # Choose output destination
    if file_name:
        f = open(file_name, "w")
        output = f
    else:
        output = sys.stdout

    try:
        print(datetime.now() , file=output)
        print(f"Solution for n = {team}" , file=output)
        print(f"Format is HOME - AWAY  (ex : 3-2 )" , file=output)
        
        # Table header
        print("\n\n" , file=output)
        for w in range(weeks):
            print(f"w{w}" , file=output , end="       ")
        print(file=output)

        match = ['X','X']
        
        for p in range(periods):
            for w in range(weeks):
                for t in range(team):
                    if(z3.is_true(m[vars[t, 0, p, w]])):
                        match[1] = t+1
                    if(z3.is_true(m[vars[t, 1, p, w]])):
                        match[0] = t+1
                print(f"[{match[0]}-{match[1]}]" , file = output , end="   ")
            print(file=output)
            match = ['X','X']

    finally:
        if file_name:
            f.close()
################################# FUNCTIONS and CONSTANT ###############################




################################# ENCODINGS - PAIRWISE ###############################
def at_least_one(bool_vars):
    return Or(bool_vars)

# Using naive-pairwise(O(n^2))
def at_most_one(bool_vars):
    return And([Not(And(pair[0], pair[1])) for pair in combinations(bool_vars, 2)])

# Using naive-pairwise(O(n^2))
def exactly_one(bool_vars):
    return And(at_least_one(bool_vars), at_most_one(bool_vars))

# Using naive-pairwise (O(n^k+1))
def at_most_k(bool_vars, k):
    return And([Or([Not(x) for x in X]) for X in combinations(bool_vars, k + 1)])
 
# Using naive-pairwise (O(n^k+1))
def at_least_k(bool_vars, k):
    return at_most_k([Not(var) for var in bool_vars], len(bool_vars)-k)

# Using naive-pairwise (O(n^k+1))
def exactly_k(bool_vars, k):
    return And(at_most_k(bool_vars, k), at_least_k(bool_vars, k))
################################# ENCODINGS - PAIRWISE ###############################



start1 = time.perf_counter()
################################# DOMAIN DEFINITION ###############################
# Define the variable
vars = np.empty((team , home , periods , weeks) , dtype=object)
for t in range(0,team):
    for h in range(0,home):    # home = 0 (team play away)   ;  home = 1 (team play at home)
        for p in range(0,periods):
            for w in range(0,weeks):
                if(h == 0):
                    #vars[t,h,p,w] = Bool(f"T{t+1}-P{p+1}-W{w+1}(AWAY)") # an other possible notation
                    vars[t,h,p,w] = Bool(f"X{t+1}{h}{p+1}{w+1}")  
                else:
                    #vars[t,h,p,w] = Bool(f"T{t+1}-P{p+1}-W{w+1}(HOME)") # an other possible notation
                    vars[t,h,p,w] = Bool(f"X{t+1}{h}{p+1}{w+1}") 

print("-------------------------------------------------------------------------------------------------")

if(optimized_version):
    pairwise = Optimize()  # Use Solver() if you don't use optimization function
else:
    pairwise = Solver()
    optimized_label = ''
################################# DOMAIN DEFINITION ###############################




################################# CONSTRAINT ###############################
# Constraint1 - Every team plays with every other team only once;
clauses = []
for t1 in range(0,team):
    for t2 in range(t1+1,team):
            for p in range(0,periods):
                for w in range(0,weeks):
                    t_i = Or(list(vars[t1,:,p,w].flatten()))
                    t_j = Or(list(vars[t2,:,p,w].flatten()))
                    clauses.append(And(t_i , t_j))
            pairwise.add(at_most_one(clauses))
            # print("1 : number of clause in the at_least_one" , len(clauses)) # Dimension check
            clauses = []


# Constraint2 - Every team plays once at week
for t in range(0,team):
    for w in range(0,weeks):
        pairwise.add(exactly_one( list(vars[t,:,:,w].flatten()) ))

# Constraint3 - Every team plays at most twice in the same period over the tournament.
for t in range(0,team):
    for p in range(0,periods):
        c = at_most_k( list(vars[t,:,p,:].flatten()) , k = 2 )
        pairwise.add(c)

# Constraint 4 - Each game has exactly 2 team + Each game cannot be played by 2 home-team or 2 away-team
for h in range(home):
    for p in range(periods):
        for w in range(weeks):
            pairwise.add(exactly_one([vars[t,h,p,w] for t in range(team)]  ))

# Constraint-Extra1 (in the first line, match are fixed)
pairwise.add(And([ Or(vars[t,0,0,t], vars[t,1,0,t]) for t in range(team - 1) ]))
pairwise.add(Or(vars[team-1,0,0,0] , vars[team-1,1,0,0]))

"""# Constraint-Extra1 (in the first,second column, match are fixed)
temp_list = []
half = team//2
for t in range(0, (team-1)):
    column =(t)//half
    line = t%half
    temp_list.append(Or(vars[t,0, line , column] , vars[t,1,line,column]))
pairwise.add(And(temp_list))"""

start2 = time.perf_counter()
init_time = start2-start1
print(f"Init finished! ({init_time:.2f}s)")
################################# CONSTRAINT ###############################



################################ OPT ################################
team_imbalance = [
    Abs(Sum([
        If(vars[t,0,p,w], 1, 0) - If(vars[t,1,p,w], 1, 0)
        for p in range(periods)
        for w in range(weeks)
    ]))
    for t in range(team)
]
total_imbalance = Sum(team_imbalance)

if(optimized_version):
    h = pairwise.minimize(total_imbalance)  # Set the objective function
################################ OPT ################################



################################# MAIN ###############################
# Import of file solutions
solutions = import_json_solution() 
# Time benchmark
start = time.perf_counter()
pairwise_result = pairwise.check()
end = time.perf_counter()
solve_time = ((end-start))


if( pairwise_result == z3.sat):
    print(f"The model is satisfiable (SAT) ✅ - exits at least one solution! (🕒: {init_time:.2f} + {solve_time:.2f} = {(init_time+solve_time):.2f}s)")
    m = pairwise.model()
    solutions = add_solution_json(pairwise.model() , solutions , round(init_time+solve_time,2) , optimized_version , m.evaluate(total_imbalance).as_long() , f"pairwise(n={team})" + optimized_label)
    if(optimized_version):
        print("OPT Evaluation minium possible (opt-enabled) : " , pairwise.lower(h) )
    else:
        print("OPT Evaluation for this model (opt-disabled) : " , m.evaluate(total_imbalance) )
    export_json_solution(solutions)
    visualize_solution_humanreadable(m , file_name="human.txt")
    visualize_solution_raw(m , file_name="raw.txt")

else:
    print("The model is unsatisfiable (UNSAT) ❌  - doesn't exits solution at all")
print("-------------------------------------------------------------------------------------------------")
################################# MAIN ###############################









            

