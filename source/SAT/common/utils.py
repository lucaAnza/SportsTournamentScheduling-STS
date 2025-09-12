import datetime
import sys
import json
from z3 import *
import time


################################# WRAP CLASS #########################################
class ContextSolver():
    
    def __init__(self , z3_model , team , vars , solution_filename , init_time , opt_enabled):

        if not(team % 2 == 0):
            raise ValueError("Team must be a non-negative integer")

        self.opt_enabled = opt_enabled
        self.obj = None
        self.init_time = init_time
        self.solve_time = -1
        self.model = z3_model
        self.team = team
        self.vars = vars
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

    def add_solution_json(self , solution_name ):
        
        if(self.opt_enabled) : solution_name = solution_name + '(OPT-version)'
        vars = self.vars
        m = self.model.model()

        match = ['X','X']
        
        sol_list = []
        for p in range(self.periods):
            period_list = [] # Create one new period list
            for w in range(self.week):
                for t in range(self.team):
                    if(z3.is_true(m[vars[t, 0, p, w]])):
                        match[1] = t+1
                    if(z3.is_true(m[vars[t, 1, p, w]])):
                        match[0] = t+1
                period_list.append(match)  # Insert one match
                match = ['X','X']
            sol_list.append(period_list)
        
        new_entry = {}
        new_entry['sol'] = sol_list
        new_entry['time']  = round(self.solve_time + self.init_time,2)
        new_entry['optimal'] = self.opt_enabled
        new_entry['obj'] = (self.obj.as_long())
        self.data[solution_name] = new_entry

    def solve(self):
        start = time.perf_counter()
        sat_result = self.model.check()
        end = time.perf_counter()
        self.solve_time = ((end-start))
        self.obj = self.compute_obj_function()

        if(sat_result == z3.sat):
            return True
        else:
            return False
        
    def compute_obj_function(self):
        vars = self.vars
        team_imbalance = [Abs(Sum([ If(vars[t,0,p,w], 1, 0) - If(vars[t,1,p,w], 1, 0) for p in range(self.periods) for w in range(self.week) ])) for t in range(self.team)]
        total_imbalance = Sum(team_imbalance)
        obj = self.model.model().evaluate(total_imbalance)
        return obj
################################# WRAP CLASS #########################################




################################# I/O FUNCTIONS #########################################
def get_user_settings(argv , docker_filename , script_filename):
    default_filename = script_filename
    optimized_version = False
    if len(argv) >= 3:
        # Read from command line
        team = int(argv[1])
        yn = sys.argv[2].lower()
        if len(argv) >= 4 and argv[3] == 'docker':
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

    weeks = team-1
    periods = team//2
    home = 2

    return team , weeks , periods , home , default_filename , optimized_version


def visualize_solution_raw(m, team ,  file_name=None):
    
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