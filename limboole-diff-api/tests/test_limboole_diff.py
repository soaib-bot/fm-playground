from limboole_diff.limboole_diff import common_witness, diff_witness, semantic_relation


def test_semantic_relation_equivalent():
    f1 = "a & b"
    f2 = "a & b"
    relation = semantic_relation(f1, f2)
    assert relation == "The formulas are equivalent."


def test_semantic_relation_previous_implies_current():
    f1 = "a & b"  # current
    f2 = "a"  # previous
    relation = semantic_relation(f1, f2)
    assert relation == "Current ⊨ Previous"


def test_semantic_relation_incomparable():
    f1 = "a & b"
    f2 = "b & c"
    relation = semantic_relation(f1, f2)
    assert relation == "The formulas are incomparable."


def test_common_witness():
    f1 = "a & b & d"
    f2 = "a & b & c"
    witness = common_witness(f1, f2)
    assert "a = 1" in witness
    assert "b = 1" in witness


def test_diff_witness():
    f1 = "a & b & d"
    f2 = "a & b & c"
    witness = diff_witness(f1, f2)
    assert "d = 1" in witness
    assert "c = 0" in witness
