FROM python:3.10-slim

RUN apt-get update && apt-get install -y \
    curl \
    wget \
    unzip \
    git \
    libicu-dev \
    genisoimage \
    e2fsprogs \
    && rm -rf /var/lib/apt/lists/*

# Install .NET 8.0 SDK (Required by Dafny 4.x)
RUN wget https://dot.net/v1/dotnet-install.sh -O dotnet-install.sh \
    && chmod +x ./dotnet-install.sh \
    && ./dotnet-install.sh --channel 8.0 --install-dir /usr/share/dotnet \
    && ln -s /usr/share/dotnet/dotnet /usr/bin/dotnet

# Install Dafny 4.11.0
ENV DAFNY_VERSION=4.11.0
RUN wget "https://github.com/dafny-lang/dafny/releases/download/v${DAFNY_VERSION}/dafny-${DAFNY_VERSION}-x64-ubuntu-22.04.zip" -O dafny.zip \
    && unzip dafny.zip -d /opt/ \
    && rm dafny.zip \
    && mv /opt/dafny* /opt/dafny-sdk \
    && chmod +x /opt/dafny-sdk/dafny

ENV PATH=$PATH:/opt/dafny-sdk

# Install Firecracker
RUN ARCH="$(uname -m)" && \
    FC_VERSION="v1.7.0" && \
    echo "Downloading Firecracker ${FC_VERSION} for ${ARCH}..." && \
    wget "https://github.com/firecracker-microvm/firecracker/releases/download/${FC_VERSION}/firecracker-${FC_VERSION}-${ARCH}.tgz" && \
    tar -xzf "firecracker-${FC_VERSION}-${ARCH}.tgz" && \
    mv "release-${FC_VERSION}-${ARCH}/firecracker-${FC_VERSION}-${ARCH}" /usr/local/bin/firecracker && \
    chmod +x /usr/local/bin/firecracker && \
    rm -rf "firecracker-${FC_VERSION}-${ARCH}.tgz" "release-${FC_VERSION}-${ARCH}"

# Create directory for VM resources
RUN mkdir -p /opt/vm-resources

# Copy VM resources (Must be built beforehand using firecracker/build_resources.sh)
COPY firecracker/vmlinux /opt/vm-resources/
COPY firecracker/rootfs.ext4 /opt/vm-resources/

ENV POETRY_HOME="/opt/poetry"
ENV PATH="$POETRY_HOME/bin:$PATH"

RUN curl -sSL https://install.python-poetry.org | python3 -

WORKDIR /app

COPY pyproject.toml poetry.lock* ./
RUN poetry config virtualenvs.create false \
    && poetry install --no-root --no-interaction

COPY . .

EXPOSE 8080

CMD ["uvicorn", "main:app", "--host", "0.0.0.0", "--port", "8080"]