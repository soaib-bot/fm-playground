from __future__ import annotations

import logging
import os
from logging.handlers import TimedRotatingFileHandler
from typing import Optional


def _get_env(name: str, default: Optional[str] = None) -> Optional[str]:
    return os.getenv(name, default)


def init_logging() -> None:

    log_dir = _get_env("LOG_DIR", "logs")
    os.makedirs(log_dir, exist_ok=True)

    log_file = os.path.join(log_dir, _get_env("LOG_FILE", "app.log"))
    level_name = _get_env("LOG_LEVEL", "INFO").upper()
    backup_count = int(_get_env("LOG_BACKUP_COUNT", "30"))

    try:
        level = getattr(logging, level_name)
    except Exception:
        level = logging.INFO

    fmt = _get_env(
        "LOG_FORMAT",
        "%(asctime)s %(levelname)s [%(name)s] %(message)s",
    )
    datefmt = _get_env("LOG_DATEFMT", "%Y-%m-%d %H:%M:%S")

    handler = TimedRotatingFileHandler(
        filename=log_file,
        when="midnight",
        backupCount=backup_count,
        encoding="utf-8",
        interval=1,
    )
    handler.setLevel(level)
    handler.setFormatter(logging.Formatter(fmt=fmt, datefmt=datefmt))

    root = logging.getLogger()
    root.setLevel(level)

    # Avoid adding duplicate handlers for the same file
    add_handler = True
    for h in root.handlers:
        if isinstance(h, TimedRotatingFileHandler):
            existing = getattr(h, "baseFilename", None)
            try:
                existing = os.path.abspath(existing) if existing else None
            except Exception:
                existing = None
            try:
                target = os.path.abspath(log_file)
            except Exception:
                target = log_file
            if existing == target:
                add_handler = False
                break

    if add_handler:
        root.addHandler(handler)

    # Ensure common uvicorn loggers propagate to the root logger so their output
    # is captured by the file handler.
    for name in ("uvicorn", "uvicorn.error", "uvicorn.access"):
        lg = logging.getLogger(name)
        lg.setLevel(level)
        lg.propagate = True

    logging.getLogger(__name__).info(
        "Initialized logging: file=%s level=%s backups=%s",
        log_file,
        logging.getLevelName(level),
        backup_count,
    )
