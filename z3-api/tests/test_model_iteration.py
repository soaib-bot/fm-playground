from z3_exec.model_iteration import get_next_model, iterate_models

valid_spec = """(declare-const a Int)
(declare-const b Int)
(assert (> a 1))
(assert (> b 1))
(assert (= (* a b) 17))
(check-sat)
(get-model)"""


def test_train_success():
    specId = iterate_models(valid_spec)
    assert specId is not None
    try:
        next_model = get_next_model(specId)
    except Exception as e:
        assert "No model found" in str(e)


def test_run_z3_with_cache():
    spec = """(declare-const a Int)
(declare-const b Int)
(assert (> a 1))
(assert (< a 1))
(check-sat)
(get-model)"""

    specId = iterate_models(spec)
    assert specId is not None
    try:
        next_model = get_next_model(specId)
    except Exception as e:
        assert "No model found" in str(e)


def test_process_commands():
    spec = """(declare-const a Int)
(declare-const b Int)
(assert (> a 1))
(assert (< b 1))
(check-sat)
(get-model)"""

    specId = iterate_models(spec)
    assert specId is not None
    next_model = get_next_model(specId)
    assert next_model is not None
