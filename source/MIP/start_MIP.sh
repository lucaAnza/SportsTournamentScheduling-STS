#!/usr/bin/env bash
set -euo pipefail

# Absolute path to THIS script's folder (e.g., .../SAT)
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

while true; do
    echo -e "\n===== Program Menu ====="
    echo "1. Model-1"
    echo "0. EXIT "
    echo "========================"

    read -rp "Select a program to run (0 to exit): " choice

    if [[ "$choice" == "0" ]]; then
        echo "Exiting..."
        break
    elif [[ "$choice" == "1" ]]; then
        # Ask parameters
        read -rp "Enter number of teams (int): " team 
        python $SCRIPT_DIR/sts_milp.py $team

    else
        echo "Invalid option. Try again."
    fi
done
