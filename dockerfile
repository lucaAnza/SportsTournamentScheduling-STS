# Python img
FROM python:3.11
RUN pip install --no-cache-dir z3-solver numpy mip

# Install MiniZinc (apt) + deps needed by bundle solvers
RUN apt-get update && apt-get install -y --no-install-recommends \
    minizinc \
    bc \
    ca-certificates \
    wget \
    libgl1 \
    && rm -rf /var/lib/apt/lists/*

# Install MiniZinc bundle (includes Chuffed)
ENV MINIZINC_VERSION=2.9.5
RUN wget -qO /tmp/minizinc.tgz \
    https://github.com/MiniZinc/MiniZincIDE/releases/download/${MINIZINC_VERSION}/MiniZincIDE-${MINIZINC_VERSION}-bundle-linux-x86_64.tgz \
    && mkdir -p /opt \
    && tar -xzf /tmp/minizinc.tgz -C /opt \
    && mv /opt/MiniZincIDE-${MINIZINC_VERSION}-bundle-linux-x86_64 /opt/minizinc \
    && rm /tmp/minizinc.tgz

ENV PATH="/opt/minizinc/bin:$PATH"

# Where the command will be executed
WORKDIR /app

# Copy into WORKDIR
COPY source/ /app

# Command to execute
CMD ["bash", "menu.sh", "--docker"]
