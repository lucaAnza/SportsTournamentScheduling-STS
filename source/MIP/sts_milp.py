import time
import sys
from mip import Model, BINARY, INTEGER, xsum, minimize, OptimizationStatus
from common.utils import *




# ========== SETTINGS VARIABLE ========== #
script_filename = 'solutions.json'
docker_filename = '/app/outputs/MIP/solutions.json'
default_filename = script_filename
debug_info = True
    
# ==================================== problem size ====================================
n , W , P , _ , default_filename , _ , _ = get_user_settings(sys.argv , docker_filename , script_filename)
teams = range(n)
weeks = range(W)
periods = range(P)

# all ordered pairs (i<j) (to avoid double match-ups)
pairs = [(i, j) for i in teams for j in teams if i < j]


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
# Fix the first week to be (0,1),(2,3),… (and fix home team) 
# Fix the team 0 to play into the diagonal
for p in periods:
  idx = pairs.index((2*p,2*p+1))  # Obtain the index of the pair (2p,2p+1)
  m += y[0][p][idx] == 1
  m += home[0][p][idx] == 1
  m += xsum(home[p][p][k] for k,(i,j) in enumerate(pairs) if i == 0) ==1


# ====================================objective function ====================================
home_cnt = [m.add_var(var_type=INTEGER, lb=0) for _ in teams]

# Count home matches for each team (sum over all (w,p) where they're designated home)
for t in teams:
    A = xsum(home[w][p][k] for w in weeks for p in periods for k, (i, _) in enumerate(pairs) if i == t)  # home games where team t is the i (the smaller index in the pair)
    B = xsum(home[w][p][k] for w in weeks for p in periods for k, (_, j) in enumerate(pairs) if j == t)  # home games where team t is the j (the larger index in the pair)
    
    for t in teams:
        m += home_cnt[t] ==  A  +  B

# Balance objective: minimize sum_t max(home_cnt[t], away_cnt[t]) with linearization
max_ha = [m.add_var(var_type=INTEGER, lb=0) for _ in teams]
balance = [m.add_var(var_type=INTEGER, lb=0) for _ in teams]
for t in teams:
    away = (W - 1) - home_cnt[t]
    m += max_ha[t] >= home_cnt[t]
    m += max_ha[t] >= away
    m += balance[t] == (2*max_ha[t]-(n-1))

m.objective = xsum(balance)

# ==================================== OPTIMIZATION ====================================
m.max_mip_gap = 0.0  # Do not stop until the gap is zero -> OPTIMAL SOLUTION FOUND
start = time.perf_counter()
status = m.optimize(max_seconds=300)
end = time.perf_counter()
runtime= end - start

# ==================================== MAIN ====================================
# By the default the library try to find the optimal value if it fail returns the non-optimal results
optimal = False
if status == OptimizationStatus.OPTIMAL:
    optimal = True
    print(f"✅ Optimal solution found (opt = {m.objective_value})")
elif status == OptimizationStatus.FEASIBLE:
    print(f"✅ Feasible solution found but not proven optimal (opt = {m.objective_value})")
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

    data = import_json_solution(default_filename)
    data = add_solution_json(schedule , runtime , m.objective_value , optimal ,  solution_name=f'MIP (n = {n}) OPT = {optimal}')
    export_json_solution(data , filename=default_filename)
    
else:
    print("No feasible solution found.")


# ========== DEBUG INFO ========== #
if debug_info:
    print("\n=== DEBUG INFO ===")
    print(f"Problem size: n={n}, W={W}, P={P}")

    