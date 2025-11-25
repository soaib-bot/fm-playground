FROM python:3.10-slim

RUN apt-get update && apt-get install -y \
    curl \
    wget \
    docker.io \
    unzip \
    git \
    libicu-dev \
    zip \
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

# Install Poetry
ENV POETRY_VERSION=1.8.3 POETRY_HOME=/opt/poetry
RUN curl -sSL https://install.python-poetry.org | python - --version "$POETRY_VERSION" \
	&& ln -s /opt/poetry/bin/poetry /usr/local/bin/poetry
WORKDIR /app
COPY pyproject.toml poetry.lock* ./
RUN poetry install --no-root
COPY . .

EXPOSE 8080

CMD ["poetry", "run", "uvicorn", "main:app", "--host", "0.0.0.0", "--port", "8080"]
