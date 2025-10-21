from limboole_diff.limboole_diff import (
    evaluate_formula,
    get_next_witness,
    store_witness,
)


def test_store_witness_diff():

    f1 = "(a | b)"
    f2 = "(a | b | c)"
    specId, res = store_witness(f1, f2, mode="common")
    assert specId is not None
    assert res.startswith("% SATISFIABLE formula (satisfying assignment follows)")
    witness = get_next_witness(specId)
    assert witness.startswith("% SATISFIABLE formula (satisfying assignment follows)")
    witness = get_next_witness(specId)
    assert witness.startswith("% SATISFIABLE formula (satisfying assignment follows)")
    witness = get_next_witness(specId)
    assert witness.startswith("% SATISFIABLE formula (satisfying assignment follows)")
    witness = get_next_witness(specId)
    assert witness.startswith("% SATISFIABLE formula (satisfying assignment follows)")
    witness = get_next_witness(specId)
    assert witness.startswith("% SATISFIABLE formula (satisfying assignment follows)")
    witness = get_next_witness(specId)
    assert witness == None


def test_evaluate_formula():
    f1 = "(a | b)"
    f2 = "(a | b | c)"
    specId, res = store_witness(f1, f2, mode="common")
    assert specId is not None
    eval = evaluate_formula(specId, "(a & b & c)")
    assert eval.startswith("% SATISFIABLE formula")
