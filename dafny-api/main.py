import os
from typing import Union

import requests
from dotenv import load_dotenv
from fastapi import FastAPI, HTTPException
from fastapi.middleware.cors import CORSMiddleware
from dafny_exec.dafny import run_dafny, verify_dafny, run_in_gvisor
from pydantic import BaseModel

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


class CodeRequest(BaseModel):
    code: str


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


@app.get("/dfy/run/", response_model=None)
def code(check: str, p: str):
    if not check or not p:
        raise HTTPException(status_code=400, detail="Invalid query parameters")
    code = get_code_by_permalink(check, p)
    try:
        return run_dafny(code)
    except Exception:
        raise HTTPException(status_code=500, detail="Error running code")


@app.get("/dfy/verify/", response_model=None)
def code_verify(check: str, p: str):
    if not check or not p:
        raise HTTPException(status_code=400, detail="Invalid query parameters")
    code = get_code_by_permalink(check, p)
    try:
        return verify_dafny(code)
    except Exception as e:
        import traceback

        error_detail = f"Error verifying dafny code: {str(e)}\n{traceback.format_exc()}"
        print(error_detail)
        raise HTTPException(status_code=500, detail=error_detail)







# ------------- Debugging Endpoints -------------
@app.post("/run")
def run_code(request: CodeRequest):
    """Run Dafny code (compile and execute)"""
    try:
        return run_in_gvisor(request.code)
    except Exception as e:
        import traceback

        error_detail = f"Error running dafny code: {str(e)}\n{traceback.format_exc()}"
        print(error_detail)
        raise HTTPException(status_code=500, detail=error_detail)
