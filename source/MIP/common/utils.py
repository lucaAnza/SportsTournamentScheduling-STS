import json
import argparse


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

    # See if is launched by docker
    docker_mode = args.docker
    print("DOCKER MODE - DEBUG : " , docker_mode)

    # Interactive fallback if team was not provided
    if args.team is None:
        team = int(input("\nHow many teams do you want ? "))
        optimized_version = _yes("Do you want optimized version ? (y/n) ")
        precomputing_version = _yes("Do you want precomputing version ? (y/n) ")
    else:
        team = args.team
        optimized_version = args.optimized
        precomputing_version = args.precomputing

    # Derivated variables
    default_filename = docker_filename if docker_mode else script_filename
    weeks = team - 1
    periods = team // 2
    home = 2

    return team, weeks, periods, home, default_filename, optimized_version, precomputing_version


def import_json_solution(filename):
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
################################# I/O FUNCTIONS #########################################



