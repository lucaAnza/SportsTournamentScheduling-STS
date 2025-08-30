import time
import os
import json
import sys
from mip import Model, BINARY, INTEGER, xsum, minimize, OptimizationStatus

# ========== SETTINGS VARIABLE ========== #
script_filename = 'solutions.json'
docker_filename = '/app/outputs/MIP/solutions.json'
solution_filename = script_filename
    
# ==================================== problem size ====================================
if len(sys.argv) > 1:
    n = int(sys.argv[1])
    if len(sys.argv) > 2:
        if(sys.argv[2] == 'docker'):
            solution_filename = docker_filename 
else : 
    n = int(input('Number of teams: '))
    
if n % 2 != 0:
    raise ValueError("n must be even")

P = n // 2            # periods per week
W = n - 1             # weeks
teams = range(n)
weeks = range(W)
periods = range(P)

# all ordered pairs (i<j) (to avoid double match-ups)
pairs = [(i, j) for i in teams for j in teams if i < j]

# ==================================== I/O functions ==================================== # 
def import_json_solution(filename = solution_filename):
    try:
        with open(filename, "r") as f:
            return json.load(f)
    except FileNotFoundError:
        print(f"File {filename} not found. Returning empty dictionary.")
        return {}
    except Exception:
        print(f"Error during file reading. Returning empty dictionary.")
        return {}

def export_json_solution(data, filename, indent=4, compact_keys=("sol",)):
    """Pretty-print JSON, but keep inner lists in `compact_keys` compact (like [1,2])."""
    def write(obj, f, level=0, parent_key=None):
        pad = " " * (level * indent)
        if isinstance(obj, dict):
            f.write("{\n"); items = list(obj.items())
            for i, (k, v) in enumerate(items):
                f.write(pad + " " * indent + json.dumps(k) + ": ")
                write(v, f, level + 1, parent_key=k)
                if i < len(items) - 1: f.write(",\n")
            f.write("\n" + pad + "}")
        elif isinstance(obj, list):
            if parent_key in compact_keys:
                f.write("[\n")
                for i, item in enumerate(obj):
                    f.write(pad + " " * indent + json.dumps(item, separators=(",", ":")))
                    if i < len(obj) - 1: f.write(",\n")
                f.write("\n" + pad + "]")
            else:
                f.write("[\n")
                for i, item in enumerate(obj):
                    f.write(pad + " " * indent)
                    write(item, f, level + 1, parent_key=None)
                    if i < len(items) - 1: f.write(",\n")
                f.write("\n" + pad + "]")
        else:
            f.write(json.dumps(obj))

    with open(filename, "w") as f:
        write(data, f, 0); f.write("\n")

    print(f"✅ Successfully exported the json solution  ('{filename}')")

def add_solution_json(data , new_entry , solution_name = 'Name'):
    data[solution_name] = new_entry
    return data

def add_solution_json(match_list, time, obj, is_optimal, solution_name="Name"):

    data = {
        solution_name: {
            "sol": [
                [list(match) if match is not None else None for match in row]
                for row in match_list
            ],
            "time": round(float(time), 3),
            "optimal": bool(is_optimal),
            "obj": obj
        }
    }
    return data

# ==================================== MODEL and VARIABLES ====================================
# the model aim is to minimize the objective function
m = Model(sense=minimize)
m.verbose = 0  # Avoid to print a lot of information about solving

# y[w][p][i,j] = 1 if match (i,j) is placed in week w, period p
y = [[[m.add_var(var_type=BINARY) for _ in pairs] for _ in periods] for _ in weeks]

# home[w][p][i,j] = 1 if    i is home vs j in (w,p)
# we just have one home-variable for each match:
# i is the team with the lowest index and plays home if home[w][p][i,j]=1
home = [[[m.add_var(var_type=BINARY) for _ in pairs] for _ in periods] for _ in weeks]


# ==================================== constraints ====================================

# 1) Every pair plays exactly once (some week & period)
for k, (i, j) in enumerate(pairs):
    m += xsum(y[w][p][k] for w in weeks for p in periods) == 1
#print(pairs)

# 2) Each (week,period) hosts exactly one game
for w in weeks:
    for p in periods:
        m += xsum(y[w][p][k] for k in range(len(pairs))) == 1

# 3) Every team plays exactly once per week
for w in weeks:
    for t in teams:
        m += xsum(
            y[w][p][k]
            for p in periods
            for k, (i, j) in enumerate(pairs)
            if t in (i, j)
        ) == 1

# 4) no team appears more than twice in the same period across the season
for t in teams:
    for p in periods:
        m += xsum(
            y[w][p][k]
            for w in weeks
            for k, (i, j) in enumerate(pairs)
            if t in (i, j)
        ) <= 2

# ==================================== Home/Away tying and objective ====================================
# Link home to y: for each placed game (i,j) in (w,p), exactly one team is home
for w in weeks:
    for p in periods:
        for k, (i, j) in enumerate(pairs):
            m += home[w][p][k] <= y[w][p][k]            # cannot set home if game not scheduled here
            # If game is here, exactly one is home: home[i]=1 => i home, (1-home)=j home
            # Enforce "home only if played here" and sum over all (w,p) later
        # Also, across all pairs, if (w,p) has a game, its home var must be defined once:
        # but we already have exactly one game per (w,p), so no extra constraint needed

# ==================================== symmetry breaking ====================================

# we fix the first week to be (0,1),(2,3),...
for p in periods:
  idx = pairs.index((2*p,2*p+1))
  m += y[0][p][idx] == 1
  m += home[0][p][idx] == 1

  m += xsum(home[p][p][k]
            #for p in periods
            for k,(i,j) in enumerate(pairs)
            if i == 0
            )==1
'''
  # fixing the diagonal with team0 always playing
  m += xsum(y[p][p][k] # + home[p][p][k]
            #for p in periods
            for k,(i,j) in enumerate(pairs)
            if i == 0
            )==1
'''

# ====================================objective function ====================================

# Count home matches for each team (sum over all (w,p) where they're designated home)
home_cnt = [m.add_var(var_type=INTEGER, lb=0) for _ in teams]

for t in teams:
    m += home_cnt[t] == xsum(
        # t is i and i is home
        home[w][p][k]
        for w in weeks for p in periods
        for k, (i, j) in enumerate(pairs)
        if i == t
    ) + xsum(
        # t is j and j is home -> that happens when i is NOT home where (i,j) is scheduled
        y[w][p][k] - home[w][p][k]
        for w in weeks for p in periods
        for k, (i, j) in enumerate(pairs)
        if j == t
    )

# Balance objective: minimize sum_t max(home_cnt[t], away_cnt[t]) with linearization
max_ha = [m.add_var(var_type=INTEGER, lb=0) for _ in teams]
balance = [m.add_var(var_type=INTEGER, lb=0) for _ in teams]
for t in teams:
    away = (n - 1) - home_cnt[t]
    m += max_ha[t] >= home_cnt[t]
    m += max_ha[t] >= away
    m += balance[t] == (2*max_ha[t]-(n-1))

m.objective = xsum(balance)

# ==================================== OPTIMIZATION ====================================
m.max_mip_gap = 0.0


start = time.perf_counter()
status = m.optimize(max_seconds=300)
end = time.perf_counter()
runtime= end - start

# ==================================== MAIN ====================================

optimal = False
if status == OptimizationStatus.OPTIMAL:
    optimal = True
    print("Optimal solution found ✅ ")
    print("Objective value:", m.objective_value)
elif status == OptimizationStatus.FEASIBLE:
    print("Feasible solution found but not proven optimal ✅")
    print("Objective value:", m.objective_value)
else:
    print("No solution found.")

if m.num_solutions:
    # Build matrix: periods x weeks
    schedule = [[None for _ in weeks] for _ in periods]
    for w in weeks:
        for p in periods:
            for k, (i, j) in enumerate(pairs):
                if y[w][p][k].x >= 0.99:
                    if home[w][p][k].x >= 0.5:
                        schedule[p][w] = (i+1, j+1)   # i home, j away
                    else:
                        schedule[p][w] = (j+1, i+1)   # j home, i away

    data = import_json_solution()
    data = add_solution_json(schedule , runtime , m.objective_value , optimal ,  solution_name=f'MIP (n = {n}) OPT = {optimal}')
    print(m.objective_value)
    export_json_solution(data , filename=solution_filename)
    
else:
    print("No feasible solution found.")

    