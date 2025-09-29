from datetime import datetime
import sys
import json
from z3 import *
import time
from abc import abstractmethod
import argparse
from itertools import combinations


################################# WRAP CLASS #########################################
class ContextSolver():
    
    def __init__(self , z3_solver , team , solution_filename , init_time , opt_enabled):

        if not(team % 2 == 0):
            raise ValueError("Team must be a non-negative integer")

        self.opt_enabled = opt_enabled
        self.obj = None
        self.init_time = init_time
        self.solve_time = -1
        self.solver = z3_solver  # Solver
        self.model = None        # ModelRef  (A solution instance)
        self.team = team
        self.week = self.team - 1
        self.periods = self.team // 2
        self.home = 2
        self.solution_filename = solution_filename
        self.data = self.import_json_solution()

    def import_json_solution(self):
        try:
            with open(self.solution_filename, "r") as f:
                data = json.load(f)
            return data
        except FileNotFoundError:
            print(f"File {self.solution_filename} not found. Returning empty dictionary.")
            return {} 
        except Exception:
            print(f"Error during file reading. Returning empty dictionary.") 
            return {} 
        
    def export_json_solution(self , indent=4, compact_keys=("sol",)):
    
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
            with open(self.solution_filename, "w") as f:
                write(self.data, f, 0)
                f.write("\n")
        except Exception as e:
            print(f"Error writing JSON file: {e}")

    @abstractmethod
    def add_solution_json(self, solution_name):
        # TO IMPLEMENT IN SUBCLASS
        pass

    def solve(self):
        start = time.perf_counter() # -----------------------------------------------------------------------------TIME(START)
        find_one_at_least_one_solution = False
        sat_result = self.solver.check()   # Start the SAT search and fill the variable model with the solution (ModelRef)
        if(sat_result == z3.sat): 
            find_one_at_least_one_solution = True
            self.model = self.solver.model()
            self.obj = self.compute_obj_function()

        if(self.opt_enabled):
            self.solve_opt()
            
        end = time.perf_counter()  # ------------------------------------------------------------------------------- TIME(END)
        self.solve_time = ((end-start))
        if(find_one_at_least_one_solution):
            return True
        else:
            return False
    
    @abstractmethod
    def compute_obj_function(self):
        # TO IMPLEMENT IN SUBCLASS
        pass

    @abstractmethod
    def solve_opt(self):
        # TO IMPLEMENT IN SUBCLASS
        pass
    

class SAT1(ContextSolver):

    def __init__(self , z3_solver , team , vars , solution_filename , init_time , opt_enabled):
        self.vars = vars
        super().__init__(z3_solver , team , solution_filename , init_time , opt_enabled )

    def compute_obj_function(self):
        vars = self.vars
        team_imbalance = [Abs(Sum([ If(vars[t,0,p,w], 1, 0) - If(vars[t,1,p,w], 1, 0) for p in range(self.periods) for w in range(self.week) ])) for t in range(self.team)]
        total_imbalance = Sum(team_imbalance)
        obj = self.model.evaluate(total_imbalance)
        return obj.as_long()
    
    def add_solution_json(self , solution_name ):
        
        if(self.opt_enabled) : solution_name = solution_name + '(OPT-version)'
        vars = self.vars
        
        match = ['X','X']
        
        sol_list = []
        for p in range(self.periods):
            period_list = [] # Create one new period list
            for w in range(self.week):
                for t in range(self.team):
                    if(z3.is_true(self.model[vars[t, 0, p, w]])):
                        match[1] = t+1
                    if(z3.is_true(self.model[vars[t, 1, p, w]])):
                        match[0] = t+1
                period_list.append(match)  # Insert one match
                match = ['X','X']
            sol_list.append(period_list)
        
        new_entry = {}
        new_entry['sol'] = sol_list
        new_entry['time']  = round(self.solve_time + self.init_time,2)
        new_entry['optimal'] = self.opt_enabled
        new_entry['obj'] = (self.obj)
        self.data[solution_name] = new_entry

    def solve_opt(self):
        sat_result = sat
        self.solver.push()  # Create a snapshot of the model
        upper_bound = (self.periods*self.week)//2

        # Linear research (every team the upperbound is decreased of 1)
        while sat_result == sat:
            self.model = self.solver.model()
            # Constraint for optimality
            for t in range(self.team):  
                for h in range(self.home):
                    self.solver.add(at_most_k(list(self.vars[t,h,:,:].flatten()) , upper_bound))  
            sat_result = self.solver.check() 
            upper_bound = upper_bound - 1
        
        self.solver.pop() # Restored the status of the solver (removed all constraint about optimality)
        self.obj = self.compute_obj_function()

    def visualize_solution_raw(self , file_name):
        
        m = self.model

        # Choose output destination
        if file_name:
            f = open(file_name, "w")
            output = f
        else:
            output = sys.stdout

        try:
            print(datetime.now() , file=output)
            for t in range(self.team):
                print(f"\n\n----------TEAM {t+1}----------", file=output)
                for h in range(self.home):  # home = 0 (away), 1 (home)
                    label = "away : " if h == 0 else "home : "
                    print(label, file=output)

                    for p in range(self.periods):
                        for w in range(self.week):
                            temp = z3.is_true(m[self.vars[t, h, p, w]])
                            print(int(temp), end=" ", file=output)
                        print(file=output)  # Newline after each week row
                    
                print(f"-----------------------------", file=output)
        finally:
            if file_name:
                f.close()


# TODO : Finish to implement this class and test SAT1
class SAT2(ContextSolver):

    def __init__(self , z3_solver , team , M , HOME , P, solution_filename , init_time , opt_enabled):
        self.M = M
        self.HOME = HOME
        self.P = P
        super().__init__(z3_solver , team , solution_filename , init_time , opt_enabled )

    def pack_week_pairs_from_model(self , model : ModelRef):
        """For each week, return a list of (home_team, away_team) ordered by period p=0..periods-1."""
        weeks_pairs = [[] for _ in range(self.week)]
        for w in range(self.week):
            for p in range(self.periods):
                teams_here = [t for t in range(self.team) if is_true(model[self.P[t][p][w]])]
                assert len(teams_here) == 2, f"Week {w}, period {p} does not have exactly 2 teams."
                t1, t2 = teams_here[0], teams_here[1]
                t1_play_at_home = is_true(model[self.HOME[t1][w]])
                if(t1_play_at_home):
                    home_team , away_team = t1 , t2
                else:
                    home_team , away_team = t2 , t1
                weeks_pairs[w].append((home_team, away_team))
        return weeks_pairs

    def compute_obj_function(self):   
        team_imbalance = []
        matches = self.team - 1 # Each team plays always n-1 match
        # Compute team_imbalance for each team and sum it
        for t in range(self.team):
            homes = Sum([If(self.HOME[t][w], 1, 0) for w in range(self.week)])  
            team_imbalance.append(Abs(matches - homes))
        total_imbalance = Sum(team_imbalance)
        obj = self.solver.model().evaluate(total_imbalance)
        return obj.as_long()

    def add_solution_json(self , solution_name):
        # Build a periods×weeks array of matches [home,away] using the model
        sol_list = [[['X', 'X'] for _ in range(self.week)] for __ in range(self.periods)]
        packed = self.pack_week_pairs_from_model(self.solver.model())  # per week: list of (home, away) following period order
        for w in range(self.week):
            for p, (h, a) in enumerate(packed[w]):
                sol_list[p][w] = [h + 1, a + 1]  # 1-based
        new_entry = {'sol': sol_list, 'time': self.init_time + self.solve_time, 'optimal': self.opt_enabled, 'obj': self.obj}
        self.data[solution_name] = new_entry
        return self.data
    
    # ===================== TO FIX - NOT WORKING AT THE MOMENT ============
    # TODO : Remember that it was added a constraint into SAT2.py model
    # TODO : Understand why the classical solve function looks like it always find the optimal solution
    # MAIN IDEA 
    """ - Add a new variable AWAY[T][W]
        - Add a new constraint at most_one AWAY[T][w],H[T],[w]
        -    Add a new constraint for optimization atmost(AWAY[T][0] , ...) and atmost(AWAY[T][0],...)
    """
    def solve_opt(self):
        sat_result = sat
        self.solver.push()  # Create a snapshot of the model
        upper_bound = (self.periods*self.week)//2

        # Linear research (every team the upperbound is decreased of 1)
        while sat_result == sat:
            self.model = self.solver.model()
            # Constraint for optimality
            for t in range(self.team):  
                for h in range(self.home):
                    self.solver.add(at_most_k(list(self.vars[t,h,:,:].flatten()) , upper_bound))  
            sat_result = self.solver.check() 
            upper_bound = upper_bound - 1
        
        self.solver.pop() # Restored the status of the solver (removed all constraint about optimality)
        self.obj = self.compute_obj_function()
    # ===================== TO FIX - NOT WORKING AT THE MOMENT ============
################################# WRAP CLASS #########################################




################################# I/O FUNCTIONS #########################################
def _yes(prompt: str) -> bool:
    return input(prompt).strip().lower() in ("y", "yes", "true", "1")

def get_user_settings(argv, docker_filename, script_filename):
    parser = argparse.ArgumentParser(
        prog="scheduler",
        description="Sports Tournament Scheduler settings"
    )
    
    # team is optional on the CLI; if omitted we fall back to interactive prompts
    parser.add_argument("team", type=int, nargs="?", help="Number of teams")
    parser.add_argument("--optimized", action="store_true", help="Look for the optimal solution")
    parser.add_argument("--docker", action="store_true", help="Needed for using the right path")
    parser.add_argument("--precomputing", action="store_true", help="Enable precomputing version")

    # Parse given argv (expects full sys.argv-like list)
    args = parser.parse_args(argv[1:])

    # Interactive fallback if team was not provided
    if args.team is None:
        team = int(input("\nHow many teams do you want ? "))
        optimized_version = _yes("Do you want optimized version ? (y/n) ")
        docker_mode = _yes("Are you executing this file using docker ? (y/n) ")
        precomputing_version = _yes("Do you want precomputing version ? (y/n) ")
    else:
        team = args.team
        optimized_version = args.optimized
        docker_mode = args.docker
        precomputing_version = args.precomputing

    # Derivated variables
    default_filename = docker_filename if docker_mode else script_filename
    weeks = team - 1
    periods = team // 2
    home = 2

    return team, weeks, periods, home, default_filename, optimized_version, precomputing_version


# m : is the output of s.model()
def visualize_solution_humanreadable(m, team , file_name=None):
    
    # Define problem size
    weeks   = team - 1
    periods = team // 2
    home  = 2 

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
################################# I/O FUNCTIONS #########################################



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