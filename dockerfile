# Python img
FROM python:3.11
RUN pip install --no-cache-dir z3-solver numpy mip

# Install MiniZinc ()
RUN apt-get update && apt-get install -y minizinc

# Install MiniZinc bundle (includes Chuffed) + bc  (COMMENT THIS IF YOU WANT TO TEST GECODE)
RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates \
    wget \
    bc \
    libgl1 \
    && apt-get clean \
    && rm -rf /var/lib/apt/lists/*

RUN wget -qO /tmp/minizinc.tgz https://github.com/MiniZinc/MiniZincIDE/releases/download/2.9.5/MiniZincIDE-2.9.5-bundle-linux-x86_64.tgz \
    && mkdir -p /opt \
    && tar -xzf /tmp/minizinc.tgz -C /opt \
    && mv /opt/MiniZincIDE-2.9.5-bundle-linux-x86_64 /opt/minizinc \
    && rm /tmp/minizinc.tgz
ENV PATH="/opt/minizinc/bin:$PATH"
#################################################################################################


# Usefull library for time in bash script
RUN apt-get install -y bc  

# Where the command will be executed. # Usually is used /app as a convention
WORKDIR /app   

# Copy into WORKDIR
COPY source/ /app 

# Comand to execute
CMD ["bash" , "menu.sh" , "--docker"]
