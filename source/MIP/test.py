import sys

docker_filename = '/app/outputs/MIP/solutions.txt'
filename = docker_filename


with open(filename, "w") as f:
        f.write("HI")