from limboole_diff.limboole_diff import (
    common_witness,
    diff_witness,
    sanitize_formula,
    semantic_relation,
)


def test_semantic_relation_equivalent():
    f1 = "a & b"
    f2 = "a & b"
    relation = semantic_relation(f1, f2)
    assert "Current ≡ Previous" in relation


def test_semantic_relation_previous_implies_current():
    f1 = "a & b"  # current
    f2 = "a"  # previous
    relation = semantic_relation(f1, f2)
    assert "Current ⊨ Previous" in relation


def test_semantic_relation_incomparable():
    f1 = "a & b"
    f2 = "b & c"
    relation = semantic_relation(f1, f2)
    assert "The formulas are incomparable" in relation


def test_common_witness():
    f1 = "a & b & d"
    f2 = "a & b & c"
    specId, witness = common_witness(f1, f2)
    assert specId is not None
    assert "a = 1" in witness
    assert "b = 1" in witness


def test_diff_witness():
    f1 = "a & b & d"
    f2 = "a & b & c"
    specId, witness = diff_witness(f1, f2)
    assert specId is not None
    assert "d = 1" in witness
    assert "c = 0" in witness


def test_sanitize_formula():
    formula = """
    a & b % this is a comment
    & c   % another comment
    & d
    """
    sanitized = sanitize_formula(formula)
    expected = "a & b & c & d"
    assert sanitized == expected

    formula = "a & b    &    c"
    sanitized = sanitize_formula(formula)
    expected = "a & b & c"
    assert sanitized == expected

    formula = """
    a %& b  this is a comment
    % another comment
    & c   % another comment
    & d
    """
    sanitized = sanitize_formula(formula)
    expected = "a & c & d"
    assert sanitized == expected
