import json
import os
from typing import Any, Dict, Union

import requests
from dotenv import load_dotenv
from fastapi import FastAPI, HTTPException
from fastapi.middleware.cors import CORSMiddleware
from limboole_diff import limboole_diff
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


def get_code_by_permalink(check: str, p: str) -> Union[str, None]:
    try:
        if check == "SATSemDiff" or check == "SAT":
            url = f"{API_URL}api/permalink/?check={check}&p={p}"
            res = requests.get(url)
            code = res.json().get("code")
            return code
    except Exception:
        raise HTTPException(status_code=404, detail="Permalink not found")


def get_metadata_by_permalink(check: str, p: str) -> Union[Dict[str, Any], None]:
    try:
        if check == "SATSemDiff":
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


class SATDiffRequest(BaseModel):
    """Request model for starting witness enumeration."""

    check: str  # SATSemDiff
    p: str  # Permalink
    analysis: str  # current-vs-left (Not Previous But Current), left-vs-current (Not Current But Previous), common


class SATDiffResponse(BaseModel):
    """Response model for starting enumeration."""

    witness: str


# --------------------------------------------------


@app.get("/run/", response_model=SATDiffResponse)
async def run_sem_analysis(check: str, p: str, analysis: str):
    try:
        current_formula = get_code_by_permalink(check, p)
        previous_metadata = get_metadata_by_permalink(check, p)
        left_side_code_id = (
            json.loads(previous_metadata).get("meta", {}).get("leftSideCodeId")
        )
        previous_formula = get_code_by_id(left_side_code_id).get("code")

        if analysis == "not-previous-but-current":
            witness = limboole_diff.diff_witness(current_formula, previous_formula)
            if witness is None:
                raise HTTPException(
                    status_code=404,
                    detail="No diff witnesses found",
                )
        elif analysis == "not-current-but-previous":
            witness = limboole_diff.diff_witness(previous_formula, current_formula)
            if witness is None:
                raise HTTPException(
                    status_code=404,
                    detail="No diff witnesses found",
                )
        elif analysis == "common-witness":
            witness = limboole_diff.common_witness(current_formula, previous_formula)
            if witness is None:
                raise HTTPException(
                    status_code=404,
                    detail="No common witnesses found",
                )
        elif analysis == "semantic-relation":
            witness = limboole_diff.semantic_relation(current_formula, previous_formula)
            if witness is None:
                raise HTTPException(
                    status_code=404,
                    detail="Could not determine semantic relation",
                )
        else:
            raise HTTPException(
                status_code=400,
                detail=f"Invalid mode: {analysis}. Supported modes: current-vs-left, left-vs-current, common",
            )
        return SATDiffResponse(witness=witness)
    except HTTPException:
        raise
    except Exception as e:
        raise HTTPException(
            status_code=500, detail=f"Error starting enumeration: {str(e)}"
        )


# --------------------------------------------------
