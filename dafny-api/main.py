import os
from typing import Union

import requests
from dotenv import load_dotenv
from fastapi import FastAPI, HTTPException
from fastapi.middleware.cors import CORSMiddleware
from dafny_exec.dafny import run_dafny

load_dotenv()


API_URL = os.getenv("API_URL")


app = FastAPI()
app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)




def get_code_by_permalink(check: str, p: str) -> Union[str, None]:
    try:
        check = check.upper()
        if check == "DFY":
            url = f"{API_URL}api/permalink/?check={check}&p={p}"
            res = requests.get(url)
            code = res.json().get("code")
            return code
    except Exception:
        raise HTTPException(status_code=404, detail="Permalink not found")


def run(code: str) -> str:
    try:
        return run_dafny(code)
    except Exception:
        raise HTTPException(status_code=500, detail="Error running dafny")


@app.get("/dfy/run/", response_model=None)
def code(check: str, p: str):
    if not check or not p:
        raise HTTPException(status_code=400, detail="Invalid query parameters")
    code = get_code_by_permalink(check, p)
    try:
        return run(code)
    except Exception:
        raise HTTPException(status_code=500, detail="Error running code")
