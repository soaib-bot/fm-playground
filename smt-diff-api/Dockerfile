FROM python:3.10-slim

# Install system deps: build tools and z3 runtime (optional)
RUN apt-get update \
	&& apt-get install -y --no-install-recommends \
	   build-essential \
	   cmake \
	   curl \
	   git \
	   z3 \
	&& rm -rf /var/lib/apt/lists/*

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
