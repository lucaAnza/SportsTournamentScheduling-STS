# Python img
FROM python:3.11
RUN pip install --no-cache-dir z3-solver numpy

# Install MiniZinc binaries
RUN apt-get update && apt-get install -y wget \
    && wget https://github.com/MiniZinc/MiniZincIDE/releases/download/2.8.5/MiniZincIDE-2.8.5-bundle-linux-x86_64.tgz \
    && tar -xvzf MiniZincIDE-2.8.5-bundle-linux-x86_64.tgz -C /opt \
    && ln -s /opt/MiniZincIDE-2.8.5-bundle-linux-x86_64/bin/minizinc /usr/local/bin/minizinc \
    && rm MiniZincIDE-2.8.5-bundle-linux-x86_64.tgz

# Where the command will be executed. # Usually is used /app as a convention
WORKDIR /app   

# Copy into WORKDIR
COPY source/ /app 

# Comand to execute
CMD ["bash" , "start.sh"]
