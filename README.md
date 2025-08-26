# CMDO 2025 Luca and Martino


## Running the project (using docker)

1. Start the Docker engine.
2. Run the command:

   ```bash
   bash start.sh
   ```
3. Use the script menu as you prefer.

   * Every **JSON solution generated** will be saved in the `/outputs` directory.
   * Each program appends its solution to the same file.
   * To reset, simply delete `outputs/solutions.json`.


## Result

In the `/Result` directory, you will find **key results** saved for specific values of n (e.g., n = 2, n = 6, n = 12).
For each model, the _highest value of n_ successfully reached is also recorded.
For example, if a model only shows _n = 12_ and no other values, it means that 12 is the maximum value it was able to achieve.

## TODO

1. fix label of opt
2. Populate /Result
