from z3_exec.z3 import (
    check_redundancy_only,
    get_next_model,
    process_commands,
    run_z3,
    run_z3_with_cache,
)

valid_spec = """(declare-const a Int)
(declare-const b Int)
(assert (> a 1))
(assert (> b 1))
(assert (= (* a b) 17))
(check-sat)
(get-model)"""


def test_train_success():
    result = run_z3(valid_spec)
    assert "unsat" in result
    assert " model is not available" in result


def test_run_z3_with_cache():
    spec = """(declare-const a Int)
(declare-const b Int)
(assert (> a 1))
(assert (< a 1))
(check-sat)
(get-model)"""

    specId, result = run_z3_with_cache(spec)
    assert specId is not None
    model = get_next_model(specId)
    model = get_next_model(specId)


def test_process_commands():
    spec = """(declare-const a Int)
(declare-const b Int)
(assert (> a 1))
(assert (< b 1))
(check-sat)
(get-model)"""

    specId, result, redundant_lines = process_commands(spec, check_redundancy=True)
    assert result is not None
    assert redundant_lines is not None


def test_check_redundancy_only():
    spec = """(declare-const a Int)
(declare-const b Int)
(assert (> a 1))
(assert (> a 2))

(check-sat)
(get-model)"""

    output, redundant_lines = check_redundancy_only(spec)
    assert redundant_lines is not None
