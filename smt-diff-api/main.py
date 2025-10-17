import json
import os
import requests
from dotenv import load_dotenv
from fastapi import FastAPI, HTTPException
from fastapi.middleware.cors import CORSMiddleware
from fastapi import HTTPException
from pydantic import BaseModel
from typing import Dict, Any, Union
import smt_diff

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
        if check == "SMTSemDiff" or check == "SMT":
            url = f"{API_URL}api/permalink/?check={check}&p={p}"
            res = requests.get(url)
            code = res.json().get("code")
            return code
    except Exception:
        raise HTTPException(status_code=404, detail="Permalink not found")


def get_metadata_by_permalink(check: str, p: str) -> Union[Dict[str, Any], None]:
    try:
        if check == "SMTSemDiff":
            url = f"{API_URL}api/metadata?check={check}&p={p}"
            res = requests.get(url)
            return res.json()
    except Exception:
        raise HTTPException(status_code=404, detail="Permalink not found")

def get_code_by_id(code_id) -> Union[Dict[str, Any], None]:
    try:
        url = f"{API_URL}api/code/{code_id}"
        res = requests.get(url)
        return res.json()
    except Exception:
        raise HTTPException(status_code=404, detail="Permalink not found")


class SmtDiffRequest(BaseModel):
    """Request model for starting witness enumeration."""

    check: str  # SMTSemDiff
    p: str  # Permalink
    analysis: str  # current-vs-left, left-vs-current, common


class SmtDiffResponse(BaseModel):
    """Response model for starting enumeration."""

    specId: str
    witness: str


# --------------------------------------------------


@app.get("/run/", response_model=SmtDiffResponse)
async def run_smt_diff(check: str, p: str, analysis: str):
    try:
        s1_spec = get_code_by_permalink(check, p)
        s2_metadata = get_metadata_by_permalink(check, p)
        left_side_code_id = json.loads(s2_metadata).get("meta", {}).get("leftSideCodeId")
        s2_spec = get_code_by_id(left_side_code_id).get("code")

        if analysis == "current-vs-left":
            specId = smt_diff.store_witness(s1_spec, s2_spec, mode="diff")
            first_witness = smt_diff.get_next_witness(specId)
            if first_witness is None:
                raise HTTPException(
                    status_code=404,
                    detail="No diff witnesses found",
                )
        elif analysis == "left-vs-current":
            # s2 previous and s1 current
            # TODO: FIX the naming convention here to avoid confusion
            specId = smt_diff.store_witness(s2_spec, s1_spec, mode="diff")
            first_witness = smt_diff.get_next_witness(specId)
            if first_witness is None:
                raise HTTPException(
                    status_code=404,
                    detail="No diff witnesses found",
                )
        elif analysis == "common":
            specId = smt_diff.store_witness(s1_spec, s2_spec, mode="common")
            first_witness = smt_diff.get_next_witness(specId)
            if first_witness is None:
                raise HTTPException(
                    status_code=404,
                    detail="No common witnesses found",
                )
        else:
            raise HTTPException(
                status_code=400,
                detail=f"Invalid mode: {analysis}. Supported modes: current-vs-left, left-vs-current, common",
            )
        return SmtDiffResponse(specId=specId, witness=first_witness)
    except HTTPException:
        raise
    except Exception as e:
        raise HTTPException(
            status_code=500, detail=f"Error starting enumeration: {str(e)}"
        )


@app.get("/next/{specId}", response_model=SmtDiffResponse)
async def get_next_witness(specId: str):
    try:
        cache_info = smt_diff.get_cache_info(specId)
        if cache_info is None:
            raise HTTPException(
                status_code=404, detail=f"Cache not found or expired: {specId}"
            )
        next_witness = smt_diff.get_next_witness(specId)

        if next_witness is None:
            raise HTTPException(
                status_code=404, detail="No more witnesses or cache exhausted"
            )

        return SmtDiffResponse(specId=specId, witness=next_witness)
    except HTTPException:
        raise
    except Exception as e:
        raise HTTPException(
            status_code=500, detail=f"Error retrieving next witness: {str(e)}"
        )
