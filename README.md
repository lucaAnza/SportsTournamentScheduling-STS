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

## 📝 Getting Started (Linux)

1. Start the Docker engine.
2. Move to `.../SportsTournamentScheduling-STS`
3. Open the **Bash Terminal** and Run the command:

   ```bash
   bash start.sh
   ```
4. Use the script menu as you prefer.

   * Every **JSON solution generated** will be saved in the `result/<MODEL>/outputs` directory.
   * Each program appends its solution to the same file.
   * To reset, simply delete `solutions.json` file.

## 📝 Getting Started (Windows)

1. Start the Docker engine.
2. Move to `.../SportsTournamentScheduling-STS`
3. Open the **Powershell** and Run the command:

   ```bash
   docker build -t cmdo_img:latest .

   docker run --rm -it -v ${PWD}\result\SAT\outputs:/app/outputs/SAT cmdo_img -v ${PWD}\result\CP\outputs:/app/outputs/CP cmdo_img -v ${PWD}\result\MIP\outputs:/app/outputs/MIP cmdo_img 
   
   ```
4. Use the script menu as you prefer.

   * Every **JSON solution generated** will be saved in the `result/<MODEL>/outputs` directory.
   * Each program appends its solution to the same file.
   * To reset, simply delete `solutions.json` file.


###  Result

In the `/result` directory, you will find **key results** saved for specific values of n (e.g., n = 2, n = 6, n = 12).
For each model, the _highest value of n_ successfully reached is also recorded.
For example, if a model only shows _n = 12_ and no other values, it means that 12 is the maximum value it was able to achieve.

### TODO

1. Populate /result
2. Ask into CP script if is run from docker or not
3. Fix Optimize function. You cannot use **Optimize**()!!!
   ```python
   # Continue this code
   attempt = 0
   loop = True
   if(optimized_version):
      
      while(loop):
         attempt = attempt + 1
         # Doing a search
         initial_upper_bound = team**2

         start = time.perf_counter()
         pairwise_result = pairwise.check()
         end = time.perf_counter()
         solve_time = ((end-start))

         if( pairwise_result == z3.sat):
               obj = pairwise.model().evaluate(total_imbalance)
               print(f"Attemp{attempt} -> SAT ✅ - obj = {pairwise.model().evaluate(total_imbalance)}")
               pairwise.add()
         else:
               loop = False
   ```
4. Analize the discussion post -> https://virtuale.unibo.it/mod/forum/view.php?id=1888696

