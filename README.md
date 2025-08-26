# 🏆 Sports Tournament Scheduling (STS) Solver

Organizing sports tournaments is a strategically important, yet complex task. As sports continue to grow in commercial value and global popularity, the demand to efficiently generate equitable tournament schedules has become increasingly critical.

This repository provides an implementation for solving the Sports Tournament Scheduling (STS) problem, a challenging combinatorial decision and optimization problem.

## 🚀 Features

- Generates feasible tournament schedules for a given set of teams.

- Ensures fairness and balance, avoiding scheduling conflicts and minimizing travel or idle rounds.

- Provides optimization strategies to improve schedule quality (e.g., minimizing breaks, balancing home/away games).

- Modular design to allow students and researchers to experiment with different algorithms (constraint programming, local search, metaheuristics, SAT/SMT solvers, etc.).

## 🔧 Technologies & Methods

- Python-based implementation (easy to extend and modify).

- Incorporates combinatorial optimization techniques.

- Implements multiple solving paradigms using differents tecnology:

  - SAT (Boolean Satisfiability) for logical constraint modeling.   (**MINIZINC**)

  - MIP (Mixed-Integer Programming) for optimization under linear constraints. 

  - CP (Constraint Programming) for flexible scheduling constraints.  (**Z3**)


## 📚 Use Cases

- Academic research in combinatorial optimization and AI.

- Practical applications in sports management systems.

- Teaching material for courses on optimization, scheduling, and operations research.

## 📝 Getting Started

1. Start the Docker engine.
2. Run the command:

   ```bash
   bash start.sh
   ```
3. Use the script menu as you prefer.

   * Every **JSON solution generated** will be saved in the `/outputs` directory.
   * Each program appends its solution to the same file.
   * To reset, simply delete `outputs/solutions.json`.


###  Result

In the `/Result` directory, you will find **key results** saved for specific values of n (e.g., n = 2, n = 6, n = 12).
For each model, the _highest value of n_ successfully reached is also recorded.
For example, if a model only shows _n = 12_ and no other values, it means that 12 is the maximum value it was able to achieve.

### TODO

1. Populate /Result
2. instead of saving outputs in `/outputs` save them in r`es/SAT/outputs` , `res/CP/outputs` , ...
