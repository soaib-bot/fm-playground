import json
import os
from typing import Any, Dict, Union

import requests
from dotenv import load_dotenv
from fastapi import FastAPI, HTTPException
from fastapi.middleware.cors import CORSMiddleware
from limboole_diff import limboole_diff
from limboole_diff.logging_config import init_logging
from pydantic import BaseModel

init_logging()

import logging

logger = logging.getLogger(__name__)


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

    specId: str
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
            specId, witness = limboole_diff.store_witness(
                current_formula, previous_formula, mode="diff"
            )
            if witness is None:
                raise HTTPException(
                    status_code=404,
                    detail="No diff witnesses found",
                )
            # witness = limboole_diff.diff_witness(current_formula, previous_formula)
        elif analysis == "not-current-but-previous":
            specId, witness = limboole_diff.store_witness(
                previous_formula, current_formula, mode="diff"
            )
            if witness is None:
                raise HTTPException(
                    status_code=404,
                    detail="No diff witnesses found",
                )
        elif analysis == "common-witness":
            specId, witness = limboole_diff.store_witness(
                current_formula, previous_formula, mode="common"
            )
            if witness is None:
                raise HTTPException(
                    status_code=404,
                    detail="No common witnesses found",
                )
        elif analysis == "semantic-relation":
            semantic_relation = limboole_diff.semantic_relation(
                current_formula, previous_formula
            )
            if semantic_relation is None:
                raise HTTPException(
                    status_code=404,
                    detail="Could not determine semantic relation",
                )
            logger.info(
                "RUN: specId=%s check=%s p=%s analysis=%s",
                "semantic-relation",
                check,
                p,
                analysis,
            )
            return SATDiffResponse(
                specId="semantic-relation", witness=semantic_relation
            )
        else:
            raise HTTPException(
                status_code=400,
                detail=f"Invalid mode: {analysis}. Supported modes: current-vs-left, left-vs-current, common",
            )
        logger.info(
            "RUN: specId=%s check=%s p=%s analysis=%s", specId, check, p, analysis
        )
        return SATDiffResponse(specId=specId, witness=witness)
    except HTTPException:
        raise
    except Exception as e:
        raise HTTPException(
            status_code=500, detail=f"Error starting enumeration: {str(e)}"
        )


@app.get("/next/{specId}", response_model=SATDiffResponse)
async def get_next_witness(specId: str):
    try:
        cache_info = limboole_diff.cache_manager.get_cache_info(specId)
        if cache_info is None:
            raise HTTPException(
                status_code=404, detail=f"Cache not found or expired: {specId}"
            )
        next_witness = limboole_diff.get_next_witness(specId)

        if next_witness is None:
            raise HTTPException(
                status_code=404, detail="No more witnesses or cache exhausted"
            )
        logger.info("NEXT: specId=%s", specId)
        return SATDiffResponse(specId=specId, witness=next_witness)
    except HTTPException:
        raise
    except Exception as e:
        raise HTTPException(
            status_code=500, detail=f"Error retrieving next witness: {str(e)}"
        )


@app.get("/eval/{specId}", response_model=Dict[str, str])
def eval_formula(specId: str, formula: str = None):
    try:
        logger.info("/eval called - specId=%s formula=%s", specId, formula)
        cache_info = limboole_diff.cache_manager.get_cache_info(specId)
        if cache_info is None:
            raise HTTPException(
                status_code=404, detail=f"Cache not found or expired: {specId}"
            )
        evaluation = limboole_diff.evaluate_formula(specId, formula)
        if evaluation is None:
            raise HTTPException(status_code=404, detail="Error evaluating formula")
        logger.info(
            "EVAL: specId=%s formula=%s evaluation=%s", specId, formula, evaluation
        )
        return {"evaluation": evaluation}
    except HTTPException:
        raise
    except Exception as e:
        raise HTTPException(
            status_code=500, detail=f"Error evaluating formula: {str(e)}"
        )


# --------------------------------------------------
