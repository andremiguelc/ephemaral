"""Layer 3: Invariant compiler tests — .aral → SMT-LIB output assertions."""

import pytest
from conftest import compile_fixture, run_aral_compile


# ============================================================
# Comparison operators
# ============================================================

class TestComparisonOperators:
    def test_gte(self):
        out = compile_fixture("cmp_gte.aral")
        assert "(>= total 0.0)" in out
        assert "inv-total-non-negative" in out

    def test_eq(self):
        out = compile_fixture("cmp_eq.aral")
        assert "(= total subtotal)" in out

    def test_neq(self):
        out = compile_fixture("cmp_neq.aral")
        assert "(not (= total 0.0))" in out

    def test_gt(self):
        out = compile_fixture("cmp_gt.aral")
        assert "(> total 0.0)" in out

    def test_lt(self):
        out = compile_fixture("cmp_lt.aral")
        assert "(< total 10000.0)" in out

    def test_lte(self):
        out = compile_fixture("cmp_lte.aral")
        assert "(<= total 10000.0)" in out


# ============================================================
# Arithmetic in invariant body
# ============================================================

class TestArithmetic:
    def test_subtraction(self):
        out = compile_fixture("arith_sub.aral")
        assert "(- subtotal total)" in out
        assert ">=" in out

    def test_multiplication(self):
        out = compile_fixture("arith_mul.aral")
        assert "(* unitPrice quantity)" in out


# ============================================================
# Boolean connectives
# ============================================================

class TestLogic:
    def test_conjunction(self):
        out = compile_fixture("logic_and.aral")
        assert "(and" in out
        assert "(>= total 0.0)" in out
        assert "(<= total 10000.0)" in out

    def test_disjunction(self):
        out = compile_fixture("logic_or.aral")
        assert "(or" in out


# ============================================================
# Multiple invariants in one file
# ============================================================

class TestMultipleInvariants:
    def test_two_invariants(self):
        out = compile_fixture("multi.aral")
        assert "inv-total-non-negative" in out
        assert "inv-margin-non-negative" in out
        # Both should have assert statements
        assert out.count("(assert") >= 2

    def test_constants_declared(self):
        out = compile_fixture("multi.aral")
        assert "(declare-const total Real)" in out
        assert "(declare-const subtotal Real)" in out


# ============================================================
# Comments
# ============================================================

class TestComments:
    def test_comments_ignored(self):
        """Comments should not affect compilation."""
        out = compile_fixture("with_comments.aral")
        assert "(>= total 0.0)" in out
        assert "inv-total-non-negative" in out


# ============================================================
# Unsupported constructs
# ============================================================

class TestUnsupportedConstructs:
    def test_skip_reported(self):
        """Unsupported invariants should be skipped with a message on stderr."""
        result = run_aral_compile("skip_each.aral")
        assert result.returncode == 0
        assert "[skipped]" in result.stderr
        assert "line_items_positive" in result.stderr

    def test_compilable_still_works(self):
        """Compilable invariants in the same file should still compile."""
        out = compile_fixture("skip_each.aral")
        assert "(>= total 0.0)" in out
        assert "inv-total-non-negative" in out


# ============================================================
# Output structure
# ============================================================

class TestOutputStructure:
    def test_has_check_sat(self):
        out = compile_fixture("cmp_gte.aral")
        assert "(check-sat)" in out

    def test_has_declare_const(self):
        out = compile_fixture("cmp_gte.aral")
        assert "(declare-const total Real)" in out

    def test_has_define_fun(self):
        out = compile_fixture("cmp_gte.aral")
        assert "(define-fun inv-total-non-negative () Bool" in out

    def test_has_named_assert(self):
        """Asserts should use :named for unsat core extraction."""
        out = compile_fixture("cmp_gte.aral")
        assert ":named" in out
