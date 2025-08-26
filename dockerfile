# Python img
FROM python:3.11
RUN pip install --no-cache-dir z3-solver numpy

# Where the command will be executed. # Usually is used /app as a convention
WORKDIR /app   

# Copy into WORKDIR
COPY source/ /app 

# Comand to execute
CMD ["bash" , "start.sh"]
