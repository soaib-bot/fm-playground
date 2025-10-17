FROM python:3.10-alpine
RUN apk add --no-cache poetry
WORKDIR /app
COPY pyproject.toml poetry.lock* ./
RUN poetry install --no-root
COPY . .
EXPOSE 8080
CMD ["poetry", "run", "uvicorn", "main:app", "--host", "0.0.0.0", "--port", "8080"]
