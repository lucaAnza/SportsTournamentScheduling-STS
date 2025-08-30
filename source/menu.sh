#!/bin/bash

# Directories and corresponding start scripts
declare -A scripts
scripts["SAT"]="SAT/start_SAT.sh"
scripts["CP"]="CP/start_CP.sh"
scripts["MIP"]="MIP/start_MIP.sh"

while true; do
    echo -e "\n\n===== Start Menu ====="
    i=1
    keys=()
    for key in "${!scripts[@]}"; do
        echo "$i. $key"
        keys[$i]=$key
        ((i++))
    done
    echo "0. Exit"
    echo "======================"

    read -p "Choose a program to run (0 to exit): " choice

    if [[ "$choice" -eq 0 ]]; then
        echo "Exiting..."
        break
    elif [[ -n "${keys[$choice]}" ]]; then
        script="${scripts[${keys[$choice]}]}"
        echo "Running $script ..."
        bash "$script"
    else
        echo "Invalid choice. Try again."
    fi
done
