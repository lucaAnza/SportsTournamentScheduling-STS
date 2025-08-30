#!/usr/bin/env python3
from itertools import combinations
from z3 import *
import numpy as np
from datetime import datetime
import json, sys, time

# =============================== CONFIG ===================================
SEED_FOR_REPRODUTION = 0       # set to 0 for default; >0 for reproduce an attempt

# ========================== CLI / PARAMETERS ===============================
team = 6
optimized_version = False
precomputing_version = False
optimized_label = 'Optimized'
precomputing_label = '(Pre-solving)'
script_filename = 'solutions.json'
docker_filename = '/app/outputs/SAT/solutions.json'
default_filename = script_filename

# terminal parameters : team(int) , optimized (bool) , launched_from_docker (bool) , precomputing(bool)
if len(sys.argv) >= 3:
    team = int(sys.argv[1])
    yn = sys.argv[2].lower()
    if len(sys.argv) >= 4 and sys.argv[3] == 'docker':
        default_filename = docker_filename
    if yn in ('y', 'yes', 'true', '1'):
        optimized_version = True
    if len(sys.argv) == 5 and sys.argv[4].lower() in ('y', 'yes', 'true', '1'):
        precomputing_version = True
else:
    team = int(input("\nHow many teams do you want ? "))
    temp = input("Do you want optimized version ? (y/n) ")
    if temp.lower() in ('y', 'yes'):
        optimized_version = True
    temp = input("Are you executing this file using docker ? (y/n) ")
    if temp.lower() in ('y', 'yes'):
        default_filename = docker_filename

if team % 2 != 0:
    print("ERROR : Team must be even!")
    sys.exit(1)

weeks   = team - 1
periods = team // 2
home    = 2  # for visualization

# Z3 params
set_param('sat.cardinality.solver', True)   # Specialized encodings for cardinality constraints
if SEED_FOR_REPRODUTION:
    set_param('random_seed', SEED_FOR_REPRODUTION)

# =============================== IO HELPERS ================================
def import_json_solution(filename=default_filename):
    try:
        with open(filename, "r") as f:
            return json.load(f)
    except FileNotFoundError:
        print(f"File {filename} not found. Returning empty dictionary.")
        return {}
    except Exception:
        print(f"Error during file reading. Returning empty dictionary.")
        return {}

def export_json_solution(data, filename=default_filename, indent=4, compact_keys=("sol",)):
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

# ========================== ROUND-ROBIN PAIRS GENERATION ============================
def round_robin_pairs(n):
    arr = list(range(n))
    weeks_list = []
    for w in range(n - 1):
        pairs = []
        for i in range(n // 2):
            a = arr[i]
            b = arr[n - 1 - i]
            if a < b: pairs.append((a, b))
            else:     pairs.append((b, a))
        weeks_list.append(pairs)
        # rotate (fix arr[0])
        arr = [arr[0]] + [arr[-1]] + arr[1:-1]
    return weeks_list


################################# ENCODINGS - PAIRWISE ###############################
def at_least_one(bool_vars):
    return Or(bool_vars)

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

################################# ENCODINGS - HEULE ###############################
# naive pairwise-encoding
def at_most_one(bool_vars):
    return And([Not(And(pair[0], pair[1])) for pair in combinations(bool_vars, 2)])

def at_most_one_heule(bool_vars, name ):
    if len(bool_vars) <= 4:
        return And(at_most_one(bool_vars))
    y = Bool(f"y_{name}")
    # Before it was : return And(And(at_most_one_np(bool_vars[:3] + [y])), And(at_most_one(bool_vars[3:] + [Not(y)], name+"_")))
    group1 = bool_vars[:3] + [y]
    group2 = [Not(y)] + bool_vars[3:]  # Prepend ¬y for clarity
    return And(
        at_most_one_heule(group1, name + "_left"),   # TODO : check if left and right are the best
        at_most_one_heule(group2, name + "_right")   # TODO : check if left and right are the best
    )   

def exactly_one_heule(bool_vars, name = 'A'):
    return And(at_most_one_heule(bool_vars, name), at_least_one(bool_vars))
################################# ENCODINGS - HEULE ###############################


# ============================== MODEL VARS =================================
start1 = time.perf_counter()
M = [[[Bool(f"M_{t1}_{t2}_w{w}") for w in range(weeks)] for t2 in range(team)] for t1 in range(team)] # t1,t2 plays in week w
HOME = [[Bool(f"HOME_{t}_w{w}") for w in range(weeks)] for t in range(team)] # team t is home in week w
P = [[[Bool(f"P_t{t}_p{p}_w{w}") for w in range(weeks)] for p in range(periods)] for t in range(team)] # team t is assigned to period p in week w
S = Optimize() if optimized_version else Solver()
# ============================== CONSTRAINTS ================================

# Constraint 1 : every team plays with every other team only once;
for t1 in range(team):
    for t2 in range(t1 + 1, team):
        S.add(PbEq([(M[t1][t2][w], 1) for w in range(weeks)], 1))

# Constraint2 : each team play exactly one per week: sum over p of P[t][p][w] == 1
for w in range(weeks):
    for t in range(team):
        # S.add(PbEq([(P[t][p][w], 1) for p in range(periods)], 1))   # SAT translation of x1​+x2​+x3​ = 1 (PbEq also enabled weight 3x1 + 4x2 + ...)
        S.add(exactly_k([P[t][p][w] for p in range(periods)], 1))   # TODO : use exactly one of sequential,heule,bitwise

# Constraint3 : each team plays two per period : sum over weeks of P[t][p][w] <= 2
for t in range(team):
    for p in range(periods):
        S.add(PbLe([(P[t][p][w], 1) for w in range(weeks)], 2))

# Constraint4 : Home/away consistency: when (t1,t2) plays in w, HOME differs
for w in range(weeks):
    for t1 in range(team):
        for t2 in range(t1 + 1, team):
            S.add(Implies(M[t1][t2][w], Xor(HOME[t1][w], HOME[t2][w])))

# Constraint5 : Each game is played by 2 team : sum over t of P[t][p][w] == 2
for w in range(weeks):
    for p in range(periods):
        S.add(PbEq([(P[t][p][w], 1) for t in range(team)], 2))     # SAT translation of x1​+x2​+x3​ =2 (PbEq also enabled weight 3x1 + 4x2 + ...)
        # S.add(exactly_k([P[t][p][w] for t in range(team)], 2))     # TODO : use exactly k of sequential 


#Link periods variable (P) to pair variable (M)
for w in range(weeks):
    for t1 in range(team):
        for t2 in range(t1 + 1, team):
            # If the pair plays in week w, they share exactly one period
            S.add(Implies(M[t1][t2][w], Or([And(P[t1][p][w], P[t2][p][w]) for p in range(periods)])))
            
            # If two teams share (period p, week w), then that (t1,t2) is the match that week
            for p in range(periods):
                S.add(Implies(And(P[t1][p][w], P[t2][p][w]), M[t1][t2][w]))

# ================================ PRECOMPUTING ==================================
if precomputing_version:
    pre1 = time.perf_counter()
    # Generate possible pairs
    rr_weeks = round_robin_pairs(team)  # weeks -> list[(a,b)]
    
    # Define only the possible couple of match
    M_true = set()  # start with an empty set
    for w, pairs in enumerate(rr_weeks):      
        for a, b in pairs:                     
            t1 = min(a, b)                     
            t2 = max(a, b)
            M_true.add((t1, t2, w))            

    # Say that is sat only if the generated couple are the one in M_true
    for t1 in range(team):
        for t2 in range(t1+1, team):
            for w in range(weeks):
                if (t1, t2, w) in M_true:
                    S.add(M[t1][t2][w])
                else:
                    S.add(Not(M[t1][t2][w]))
    pre2 = time.perf_counter()
    precomputing_time = pre2-pre1
    print(f"Precomputing time :  ({precomputing_time:.2f}s)")
# =============================== OBJECTIVE =================================
# Total imbalance of home vs away per team (sum of abs diffs)
team_imbalance = []

for t in range(2):
    homes = Sum([If(HOME[t][w], 1, 0) for w in range(weeks)])
    team_imbalance.append(Abs(homes - (weeks - homes)))
total_imbalance = Sum(team_imbalance)

if optimized_version:
    h = S.minimize(total_imbalance)
else:
    optimized_label = ''
    
start2 = time.perf_counter()
init_time = start2 - start1
print(f"Init finished! ({init_time:.2f}s)")

# ================================ OUTPUT ===================================
def pack_week_pairs_from_model(model):
    """For each week, return a list of (home_team, away_team) ordered by period p=0..periods-1."""
    weeks_pairs = [[] for _ in range(weeks)]
    for w in range(weeks):
        for p in range(periods):
            teams_here = [t for t in range(team) if is_true(model[P[t][p][w]])]
            assert len(teams_here) == 2, f"Week {w}, period {p} does not have exactly 2 teams."
            t1, t2 = teams_here[0], teams_here[1]
            h1 = is_true(model[HOME[t1][w]])
            h2 = is_true(model[HOME[t2][w]])
            home_team = t1 if h1 else t2
            away_team = t2 if h1 else t1
            weeks_pairs[w].append((home_team, away_team))
    return weeks_pairs

def add_solution_json(m, data, total_time=0, optimal=False, obj=None, solution_name="myAlgorithm"):
    # Build a periods×weeks array of matches [home,away] using the model
    sol_list = [[['X', 'X'] for _ in range(weeks)] for __ in range(periods)]
    packed = pack_week_pairs_from_model(m)  # per week: list of (home, away) following period order
    for w in range(weeks):
        for p, (h, a) in enumerate(packed[w]):
            sol_list[p][w] = [h + 1, a + 1]  # 1-based
    new_entry = {'sol': sol_list, 'time': total_time, 'optimal': optimal, 'obj': obj}
    data[solution_name] = new_entry
    return data

def visualize_solution_humanreadable(m, file_name=None):
    out = open(file_name, "w") if file_name else sys.stdout
    try:
        print(datetime.now(), file=out)
        print(f"Solution for n = {team}", file=out)
        print(f"Format is HOME - AWAY  (ex : 3-2 )", file=out)
        print("\n", file=out)
        for w in range(weeks):
            print(f"w{w}", end="       ", file=out)
        print(file=out)
        packed = pack_week_pairs_from_model(m)
        for p in range(periods):
            for w in range(weeks):
                h, a = packed[w][p]
                print(f"[{h+1}-{a+1}]", end="   ", file=out)
            print(file=out)
    finally:
        if file_name: out.close()

def visualize_solution_raw(m, file_name=None):
    out = open(file_name, "w") if file_name else sys.stdout
    try:
        print(datetime.now(), file=out)
        V = np.zeros((team, home, periods, weeks), dtype=int)
        packed = pack_week_pairs_from_model(m)
        for w in range(weeks):
            for p, (h, a) in enumerate(packed[w]):
                V[h, 1, p, w] = 1  # home team at (p,w)
                V[a, 0, p, w] = 1  # away team at (p,w)
        for t in range(team):
            print(f"\n\n----------TEAM {t+1}----------", file=out)
            for hh in range(home):
                print(("away : " if hh == 0 else "home : "), file=out)
                for p in range(periods):
                    for w in range(weeks):
                        print(int(V[t, hh, p, w]), end=" ", file=out)
                    print(file=out)
            print(f"-----------------------------", file=out)
    finally:
        if file_name: out.close()

# ================================ MAIN =====================================
solutions = import_json_solution(default_filename)

start = time.perf_counter()
res = S.check()
end = time.perf_counter()
solve_time = end - start

if res == sat:
    m = S.model()
    total = m.evaluate(total_imbalance).as_long()
    print(f"The model is satisfiable (SAT) ✅ - exits at least one solution! (🕒: {init_time:.2f} + {solve_time:.2f} = {(init_time+solve_time):.2f}s)")
    solutions = add_solution_json(
        m, solutions,
        total_time=round(init_time + solve_time, 2),
        optimal=optimized_version,
        obj=total,
        solution_name=f"SAT2(n={team})" + optimized_label + precomputing_label
    )
    if optimized_version:
        print("OPT Evaluation minimum possible (opt-enabled):", S.lower(h))
    else:
        print("OPT Evaluation for this model (opt-disabled):", total)
    export_json_solution(solutions, default_filename)
    visualize_solution_humanreadable(m, file_name="human.txt")
    visualize_solution_raw(m, file_name="raw.txt")
else:
    print("The model is unsatisfiable (UNSAT) ❌  - doesn't exits solution at all")
print("-------------------------------------------------------------------------------------------------")
