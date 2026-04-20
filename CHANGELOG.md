# Changelog

## 0.1.4

Closes two non-breaking gaps where a construct's proof and IR support
already existed but a surface layer blocked users from reaching it, plus
an internal proof refactor.

- **`each` accepted in Function JSON**. `boolExprFromJson` now recognizes
  `{"each": {"collection": ..., "body": ...}}`. The compiler, renderer,
  and correctness proof for `eachExpr` were already in place; only the
  JSON reader was missing. This unblocks end-to-end verification of
  TypeScript `arr.every(...)` extracted by `ts-to-ephemaral` — previously
  the binary rejected valid parser output with
  `expected BoolExpr (cmp, logic, not, or isPresent)`.

- **`ite(cond, then, else)` accepted inside `sum` bodies.** The `.aral`
  DSL parser now treats `ite` as an atom inside item-body expressions
  passed to `sum(...)`. `Expr.condExpr` was already in the IR with full
  compile/render/correctness proofs; only the surface parser rejected it.
  This covers the universal pattern of conditional aggregation (SQL
  `SUM(CASE WHEN … THEN … ELSE …)`, Python `sum(x.p if x.a else 0 for x
  in xs)`, TS `reduce((s, x) => s + (x.a ? x.p : 0), 0)`) with one
  language-agnostic form:
  `sum(<type>.items, ite(active > 0, value, 0))`.

  Scalar `ite` inside `sum` only for this release. Boolean `ite` inside
  `each` would require a new `BoolExpr` constructor and is deferred.

- **Parser internals**: `parseSumExpr` now finds its matching close paren
  with depth-aware tracking, so nested constructs inside a sum body do
  not truncate the body.

- **Proof refactor**: the `sumExpr` and `eachExpr` cases of the function
  correctness proof now share a single `funEnv_collection_bridge` lemma
  instead of duplicating the four-step environment bridge. No change to
  any theorem signature; prepares the proof for future collection
  constructs (`pairwise`, `max`/`min`).

IR schema (`aralFnVersion`) remains at 0.1.2 — no schema change.

## 0.1.2

Prior release (see git history).
