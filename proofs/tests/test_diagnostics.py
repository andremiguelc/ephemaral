"""Layer 4: Diagnostic output tests — snapshot capture for LLM evaluation.

This test file captures diagnostic outputs from the ephemaral CLI into snapshot
files. The snapshots are evaluated by the /ephemaral-diagnostics-eval skill,
which checks clarity, accuracy, and absence of jargon.

Deterministic assertions here are minimal — just enough to confirm the right
category was produced. The real evaluation is LLM-based.
"""

import pytest
from pathlib import Path
from conftest import run_ephemaral, write_snapshot, FIXTURES_DIR


def _run_and_snapshot(json_name: str, aral_names, snapshot_name: str) -> str:
    """Run ephemaral, write snapshot, return combined output.
    aral_names can be a single filename or a list of filenames."""
    json_path = FIXTURES_DIR / json_name
    if isinstance(aral_names, str):
        aral_names = [aral_names]
    aral_paths = [FIXTURES_DIR / n for n in aral_names]
    result = run_ephemaral(json_path, aral_paths)
    output = result.stdout + result.stderr

    # Read the source files for context in the snapshot
    json_content = json_path.read_text()
    aral_sections = []
    for p in aral_paths:
        aral_sections.append(f"=== Invariants ({p.name}) ===\n{p.read_text()}")

    snapshot = (
        f"=== Function (Aral-fn JSON) ===\n{json_content}\n"
        + "\n".join(aral_sections) + "\n"
        + f"=== Diagnostic Output ===\n{output}"
    )
    write_snapshot(snapshot_name, snapshot)
    return output


# ============================================================
# VERIFIED
# ============================================================

class TestVerified:
    def test_verified_guarded_sub(self):
        out = _run_and_snapshot(
            "verified_guarded_sub.aral-fn.json",
            "verified_guarded_sub.aral",
            "verified_guarded_sub",
        )
        assert "VERIFIED" in out
        assert "(verified_guarded_sub.aral)" in out  # ESLint-style source ref

    def test_each_in_ite_cond_deserializes(self):
        """Function assigns total via ite(each(...), subtotal, 0). The `each`
        arm in boolExprFromJson must accept the cond; both ite branches
        preserve non-negativity → VERIFIED."""
        out = _run_and_snapshot(
            "each_in_ite_cond_verified.aral-fn.json",
            ["each_in_ite_cond_total.aral", "each_in_ite_cond_subtotal.aral"],
            "each_in_ite_cond_verified",
        )
        assert "VERIFIED" in out
        assert "total_non_negative" in out
        # Guard against regression of the pre-0.1.3 reader error
        assert "expected BoolExpr" not in out


# ============================================================
# UNCONSTRAINED_PARAMETER
# ============================================================

class TestUnconstrainedParameter:
    def test_unconstrained_withdraw(self):
        out = _run_and_snapshot(
            "unconstrained_withdraw.aral-fn.json",
            "unconstrained_withdraw.aral",
            "unconstrained_withdraw",
        )
        assert "UNCONSTRAINED_PARAMETER" in out

    def test_unconstrained_two_params(self):
        out = _run_and_snapshot(
            "unconstrained_two_params.aral-fn.json",
            "unconstrained_two_params.aral",
            "unconstrained_two_params",
        )
        assert "UNCONSTRAINED_PARAMETER" in out


# ============================================================
# INVARIANT_GAP
# ============================================================

class TestInvariantGap:
    def test_invariant_gap_missing_field(self):
        out = _run_and_snapshot(
            "invariant_gap_missing_field.aral-fn.json",
            "invariant_gap_missing_field.aral",
            "invariant_gap_missing_field",
        )
        assert "INVARIANT_GAP" in out


# ============================================================
# RULE_CONFLICT
# ============================================================

class TestRuleConflict:
    def test_rule_conflict_sign_flip(self):
        out = _run_and_snapshot(
            "rule_conflict_sign_flip.aral-fn.json",
            "rule_conflict_sign_flip.aral",
            "rule_conflict_sign_flip",
        )
        assert "RULE_CONFLICT" in out

    def test_rule_conflict_overflow(self):
        out = _run_and_snapshot(
            "rule_conflict_overflow.aral-fn.json",
            "rule_conflict_overflow.aral",
            "rule_conflict_overflow",
        )
        assert "RULE_CONFLICT" in out

    def test_typed_param_rule_conflict(self):
        """Typed param constrained by param .aral, but function logic still violates."""
        out = _run_and_snapshot(
            "typed_param_rule_conflict.aral-fn.json",
            ["typed_param_rule_conflict.aral", "typed_param_rule_conflict_param.aral"],
            "typed_param_rule_conflict",
        )
        assert "RULE_CONFLICT" in out
        assert "UNCONSTRAINED_PARAMETER" not in out
        assert "Even assuming" in out  # New param constraint phrasing
        assert "(typed_param_rule_conflict_param.aral)" in out  # Source ref for param rules
        # No absolute file paths
        assert "/Users/" not in out


# ============================================================
# TYPED PARAM — unconstrained when no matching .aral provided
# ============================================================

# ============================================================
# VERIFIED — with object param preconditions
# ============================================================

class TestPassThroughVerified:
    def test_pass_through_only_assigns_non_invariant_field(self):
        """Function assigns only 'status' (no invariant), but spread preserves total+subtotal → VERIFIED."""
        out = _run_and_snapshot(
            "pass_through_verified.aral-fn.json",
            "pass_through_verified.aral",
            "pass_through_verified",
        )
        assert "VERIFIED" in out
        assert "total_non_negative" in out
        assert "subtotal_non_negative" in out


class TestObjectParamVerified:
    def test_object_param_multiply_verified(self):
        """Object param (scaledAmount-amount, scaledAmount-scale) constrained → VERIFIED."""
        out = _run_and_snapshot(
            "object_param_verified.aral-fn.json",
            ["object_param_verified.aral", "object_param_verified_param.aral"],
            "object_param_verified",
        )
        assert "VERIFIED" in out
        assert "Assuming valid parameters:" in out  # New param assumption header
        assert "(object_param_verified_param.aral)" in out  # Source ref for param rules
        assert "(object_param_verified.aral)" in out  # Source ref for input rules


# ============================================================
# TYPED PARAM — unconstrained when no matching .aral provided
# ============================================================

class TestTypedParamUnconstrained:
    def test_typed_param_still_unconstrained(self):
        """Typed param with no matching .aral → still UNCONSTRAINED_PARAMETER."""
        out = _run_and_snapshot(
            "typed_param_unconstrained.aral-fn.json",
            "typed_param_unconstrained.aral",
            "typed_param_unconstrained",
        )
        assert "UNCONSTRAINED_PARAMETER" in out


# ============================================================
# NULLABLE — optional field with isPresent guard
# ============================================================

class TestNullableVerified:
    def test_nullable_coalesce_verified(self):
        """discount ?? 0 with bounded discount — VERIFIED via implicit presence guard."""
        out = _run_and_snapshot(
            "nullable_coalesce_verified.aral-fn.json",
            "nullable_coalesce_verified.aral",
            "nullable_coalesce_verified",
        )
        assert "VERIFIED" in out
        assert "discount_bounded" in out


class TestNullableRuleConflict:
    def test_nullable_wrong_default(self):
        """discount ?? subtotal*2 produces negative total — RULE_CONFLICT."""
        out = _run_and_snapshot(
            "nullable_wrong_default.aral-fn.json",
            "nullable_wrong_default.aral",
            "nullable_wrong_default",
        )
        assert "RULE_CONFLICT" in out
        assert "total" in out


class TestIsPresentMissingOptional:
    def test_ispresent_without_optional_fields(self):
        """isPresent(field) with field not in optionalFields — rejected at deserialization
        with an actionable error message naming the field and pointing to optionalFields."""
        out = _run_and_snapshot(
            "ispresent_missing_optional.aral-fn.json",
            "ispresent_missing_optional.aral",
            "ispresent_missing_optional",
        )
        assert "isPresent" in out
        assert "optionalFields" in out
        # The error identifies the offending field by name (dynamic, not hardcoded):
        assert "bonus" in out


# ============================================================
# SUM / COLLECTION — M5 diagnostics
# ============================================================

class TestSumVerified:
    def test_sum_passthrough(self):
        """Function updates status, items pass through → sum invariant holds."""
        out = _run_and_snapshot(
            "sum_verified_passthrough.aral-fn.json",
            "sum_verified_passthrough.aral",
            "sum_verified_passthrough",
        )
        assert "VERIFIED" in out
        assert "total_matches_items" in out


class TestSumRuleConflict:
    def test_sum_constant_total(self):
        """Total set to 0 — breaks sum relationship when items have values."""
        out = _run_and_snapshot(
            "sum_rule_conflict_constant.aral-fn.json",
            "sum_rule_conflict_constant.aral",
            "sum_rule_conflict_constant",
        )
        assert "COUNTEREXAMPLE" in out or "RULE_CONFLICT" in out
        assert "total" in out

    def test_sum_wrong_formula(self):
        """Total = tax instead of sum(items, subtotal) + tax."""
        out = _run_and_snapshot(
            "sum_rule_conflict_wrong_formula.aral-fn.json",
            "sum_rule_conflict_wrong_formula.aral",
            "sum_rule_conflict_wrong_formula",
        )
        assert "COUNTEREXAMPLE" in out or "RULE_CONFLICT" in out or "INVARIANT_GAP" in out
        assert "total" in out


class TestSumUnconstrained:
    def test_sum_unconstrained_param(self):
        """Function uses unconstrained 'adjustment' param — UNCONSTRAINED_PARAMETER."""
        out = _run_and_snapshot(
            "sum_unconstrained_param.aral-fn.json",
            "sum_unconstrained_param.aral",
            "sum_unconstrained_param",
        )
        assert "UNCONSTRAINED_PARAMETER" in out
        assert "adjustment" in out


class TestSumInvariantGap:
    def test_sum_gap_shipping_uncovered(self):
        """Function uses 'shipping' but no rule covers it — INVARIANT_GAP."""
        out = _run_and_snapshot(
            "sum_invariant_gap.aral-fn.json",
            "sum_invariant_gap.aral",
            "sum_invariant_gap",
        )
        assert "INVARIANT_GAP" in out or "COUNTEREXAMPLE" in out
        assert "shipping" in out


class TestSumCompound:
    def test_sum_compound_expression_verified(self):
        """sum(lineItems, price * quantity) with identity — VERIFIED."""
        out = _run_and_snapshot(
            "sum_compound_verified.aral-fn.json",
            "sum_compound_verified.aral",
            "sum_compound_verified",
        )
        assert "VERIFIED" in out
        assert "total_matches_line_totals" in out


class TestSumMixed:
    def test_sum_plus_scalar_invariants(self):
        """total >= 0 AND total == sum(items, subtotal) — resetTotal violates sum but satisfies >=0."""
        out = _run_and_snapshot(
            "sum_mixed_invariants.aral-fn.json",
            "sum_mixed_invariants.aral",
            "sum_mixed_invariants",
        )
        assert "COUNTEREXAMPLE" in out or "RULE_CONFLICT" in out
        assert "total" in out


# ============================================================
# DIVISION / ROUNDING — M2 diagnostics (previously uncovered)
# ============================================================

class TestDivRoundVerified:
    def test_div_floor_verified(self):
        """tax = floor(subtotal / 10) with non-negative inputs — VERIFIED."""
        out = _run_and_snapshot(
            "div_round_verified.aral-fn.json",
            "div_round_verified.aral",
            "div_round_verified",
        )
        assert "VERIFIED" in out
        assert "tax_non_negative" in out


class TestDivRoundRuleConflict:
    def test_ceil_exceeds_total(self):
        """share = ceil(total / parts) can exceed total — UNCONSTRAINED or RULE_CONFLICT."""
        out = _run_and_snapshot(
            "div_round_rule_conflict.aral-fn.json",
            "div_round_rule_conflict.aral",
            "div_round_rule_conflict",
        )
        assert "COUNTEREXAMPLE" in out or "UNCONSTRAINED" in out or "RULE_CONFLICT" in out
        assert "share" in out or "parts" in out


# ============================================================
# NULLABLE — invariant gap
# ============================================================

class TestNullableInvariantGap:
    def test_nullable_discount_gap(self):
        """discount is optional, no rule bounds it — INVARIANT_GAP when discount present."""
        out = _run_and_snapshot(
            "nullable_invariant_gap.aral-fn.json",
            "nullable_invariant_gap.aral",
            "nullable_invariant_gap",
        )
        assert "INVARIANT_GAP" in out or "COUNTEREXAMPLE" in out
        assert "discount" in out or "subtotal" in out
