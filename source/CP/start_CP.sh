#!/usr/bin/env bash
set -euo pipefail

# Parameters
docker=${1:-}     # --docker if using Docker, empty string otherwise

# Absolute path to THIS script's folder (e.g., .../SAT)
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)" 
while true; do
    echo -e "\n===== Program Menu ====="
    echo "1. Model1 (CP) Gecode [feasible]"
    echo "2. Model2 (CP) Chuffed [feasible]"
    echo "3. Model1 (CP) Gecode [optimal]"
    echo "4. Model2 (CP) Chuffed [optimal]"
    echo "0. EXIT "
    echo "========================"

    read -rp "Select a program to run (0 to exit): " choice

    if [[ "$choice" == "0" ]]; then
        echo "Exiting..."
        break
    elif [[ "$choice" == "1" ]]; then
        # Ask parameters
        read -rp "Enter number of teams (int): " team
        
        start=$(date +%s.%N)
        minizinc --solver Gecode -D "n=$team" "$SCRIPT_DIR/STS_matchVar_first column.mzn" > output.txt
        end=$(date +%s.%N)
        runtime=$(echo "$end - $start" | bc)
        python3 $SCRIPT_DIR/minizinc_reader.py $runtime "$docker"
        rm output.txt
    elif [[ "$choice" == "2" ]]; then
        # Ask parameters
        read -rp "Enter number of teams (int): " team
        
        start=$(date +%s.%N)
        minizinc --solver Chuffed -D "n=$team" "$SCRIPT_DIR/STS_matchVar_first column.mzn" > output.txt
        end=$(date +%s.%N)
        runtime=$(echo "$end - $start" | bc)
        python3 $SCRIPT_DIR/minizinc_reader.py $runtime "$docker"
        rm output.txt
    elif [[ "$choice" == "3" ]]; then
        # Ask parameters
        read -rp "Enter number of teams (int): " team
        
        start=$(date +%s.%N)
        minizinc --solver Gecode -D "n=$team" "$SCRIPT_DIR/STS_matchVar_first column_opt.mzn" > output.txt
        end=$(date +%s.%N)
        runtime=$(echo "$end - $start" | bc)
        python3 $SCRIPT_DIR/minizinc_reader.py $runtime "$docker"
        rm output.txt
    elif [[ "$choice" == "4" ]]; then
        # Ask parameters
        read -rp "Enter number of teams (int): " team
        
        start=$(date +%s.%N)
        minizinc --solver Chuffed -D "n=$team" "$SCRIPT_DIR/STS_matchVar_first column_opt.mzn" > output.txt
        end=$(date +%s.%N)
        runtime=$(echo "$end - $start" | bc)
        python3 $SCRIPT_DIR/minizinc_reader.py $runtime "$docker"
        rm output.txt
    else
        echo "Invalid option. Try again."
    fi
done
