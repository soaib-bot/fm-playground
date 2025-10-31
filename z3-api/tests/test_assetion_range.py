from z3 import *
from smt_redundancy.explain_redundancy import find_assertion_line_ranges


def test_space_in_assert():
    spec="""(declare-const x Int)
(assert (> x 2))
( assert (> x 1))
(check-sat)"""
    line_ranges = find_assertion_line_ranges(spec)
    lines_only = [(t[0], t[1]) for t in line_ranges]
    assert lines_only == [(2,2), (3,3)] 
    ranges_only = [(t[2], t[3]) for t in line_ranges]
    assert ranges_only == [(0,17), (0,18)]
    assertions_only = [t[4] for t in line_ranges]
    assert assertions_only[0].sexpr() == '(> x 2)'
    assert assertions_only[1].sexpr() == '(> x 1)'

def test_line_comment_in_assert():
    spec="""(declare-const x Int)
(assert (> x 2))
(assert 
    (> x 1)  
    ; this is a comment 
)
(check-sat)"""
    line_ranges = find_assertion_line_ranges(spec)
    lines_only = [(t[0], t[1]) for t in line_ranges]
    assert lines_only == [(2,2), (3,6)]
    ranges_only = [(t[2], t[3]) for t in line_ranges]
    assert ranges_only == [(0,17), (0,2)]
    assertions_only = [t[4] for t in line_ranges]
    assert assertions_only[0].sexpr() == '(> x 2)'
    assert assertions_only[1].sexpr() == '(> x 1)'

def test_multiple_asserts_single_line():
    spec="""(declare-const x Int)
(assert (> x 2)) (assert (> x 1))
(check-sat)"""
    line_ranges = find_assertion_line_ranges(spec)
    # Both assertions are on the same line - should now be separated
    lines_only = [(t[0], t[1]) for t in line_ranges]
    assert lines_only == [(2,2), (2,2)]
    ranges_only = [(t[2], t[3]) for t in line_ranges]
    assert ranges_only == [(0,17), (17,34)]
    assertions_only = [t[4] for t in line_ranges]
    assert assertions_only[0].sexpr() == '(> x 2)'
    assert assertions_only[1].sexpr() == '(> x 1)'
    
def test_push_pop_asserts():
    spec="""(declare-const x Int)
(push)
(assert (> x 2))
(pop)
(assert (> x 1))
(check-sat)"""
    line_ranges = find_assertion_line_ranges(spec)
    lines_only = [(t[0], t[1]) for t in line_ranges]
    assert lines_only == [(3,3), (5,5)]
    ranges_only = [(t[2], t[3]) for t in line_ranges]
    assert ranges_only == [(0,17), (0,17)]
    assertions_only = [t[4] for t in line_ranges]
    assert assertions_only[0].sexpr() == '(> x 2)'
    assert assertions_only[1].sexpr() == '(> x 1)'