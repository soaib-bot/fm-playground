import os
from typing import Union

import requests
from dotenv import load_dotenv
from fastapi import FastAPI, HTTPException
from fastapi.middleware.cors import CORSMiddleware
from smt_redundancy.explain_redundancy import explain_redundancy_from_smtlib

load_dotenv()
import redis
from redis_cache import RedisCache
from z3_exec.z3 import process_commands

API_URL = os.getenv("API_URL")
REDIS_URL = os.getenv("REDIS_URL")
client = redis.Redis.from_url(REDIS_URL)
cache = RedisCache(redis_client=client)

app = FastAPI()
app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)


def is_redis_available() -> bool:
    try:
        client.ping()
        return True
    except redis.ConnectionError:
        return False


def get_code_by_permalink(check: str, p: str) -> Union[str, None]:
    try:
        check = check.upper()
        if check == "SMT":
            url = f"{API_URL}api/permalink/?check={check}&p={p}"
            res = requests.get(url)
            code = res.json().get("code")
            return code
    except Exception:
        raise HTTPException(status_code=404, detail="Permalink not found")


def run_z3(code: str, check_redundancy: bool = False) -> str:
    if is_redis_available():

        @cache.cache()
        def cached_run_z3(code: str, check_redundancy: bool) -> str:
            return process_commands(code, check_redundancy=check_redundancy)

        try:
            return cached_run_z3(code, check_redundancy=check_redundancy)
        except Exception:
            raise HTTPException(status_code=500, detail="Error running z3")
    else:
        try:
            return process_commands(code, check_redundancy=check_redundancy)
        except Exception:
            raise HTTPException(status_code=500, detail="Error running z3")


@app.get("/smt/run/", response_model=None)
def execute_z3(check: str, p: str):
    code = get_code_by_permalink(check, p)
    try:
        return run_z3(code)
    except Exception:
        raise HTTPException(status_code=500, detail="Error running code")


@app.get("/smt/check-redundancy/", response_model=None)
def check_redundancy(check: str, p: str):
    code = get_code_by_permalink(check, p)
    try:
        result, redundant_lines = run_z3(code, check_redundancy=True)
        return {"result": result, "redundant_lines": redundant_lines}
    except Exception:
        raise HTTPException(status_code=500, detail="Error running code")


@app.get("/smt/explain-redundancy/", response_model=None)
def explain_redundancy(check: str, p: str, assertion_line: int):
    code = get_code_by_permalink(check, p)
    try:
        time_taken, minimal_set, given_assert, minimal_line_ranges = (
            explain_redundancy_from_smtlib(
                code, assertion_line, method="marker_quick_explain"
            )
        )
        return {
            "time_taken": time_taken,
            "minimal_set": [str(assertion) for assertion in minimal_set],
            "given_assert": str(given_assert),
            "minimal_line_ranges": minimal_line_ranges,
        }
    except ValueError as e:
        raise HTTPException(status_code=400, detail=str(e))
    except Exception as e:
        raise HTTPException(status_code=500, detail=f"Error running code: {str(e)}")
