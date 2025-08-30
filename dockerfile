RUN apt-get update 

# Library for bash banchmark time
RUN apt-get install -y bc

# Python img
FROM python:3.11

# Install Z3-solver (SAT)
RUN pip install --no-cache-dir z3-solver numpy

# Install MiniZinc (CP)
apt-get install -y minizinc

# Install Mip (MIP)
RUN pip install mip

# Where the command will be executed. # Usually is used /app as a convention
WORKDIR /app   

# Copy into WORKDIR
COPY source/ /app 

# Comand to execute
CMD ["bash" , "start.sh"]
