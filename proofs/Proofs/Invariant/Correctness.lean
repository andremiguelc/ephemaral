/-
  Ephemaral — Correctness Proofs
  Machine-checked proofs that the compiler preserves semantics.
-/
import Proofs.Invariant.Compile
import Proofs.Semantics

mutual
  /-- For any env: evalExpr env e = evalSmtExpr env (compileInvExpr e).
      Used by compile_preserves_semantics and compileFunExpr_preserves. -/
  theorem compileInvExpr_preserves (env : Env) (e : Expr) :
      evalExpr env e = evalSmtExpr env (compileInvExpr e) := by
    match e with
    | .lit n       => simp [evalExpr, evalSmtExpr, compileInvExpr]
    | .field ref   => simp [evalExpr, evalSmtExpr, compileInvExpr]
    | .arith op l r =>
      simp [evalExpr, evalSmtExpr, compileInvExpr]
      rw [compileInvExpr_preserves env l, compileInvExpr_preserves env r]
    | .condExpr c t e =>
      simp [evalExpr, evalSmtExpr, compileInvExpr]
      rw [compileInvBoolExpr_preserves env c]
      split
      · exact compileInvExpr_preserves env t
      · exact compileInvExpr_preserves env e
    | .roundExpr mode e =>
      simp [evalExpr, evalSmtExpr, compileInvExpr]
      rw [compileInvExpr_preserves env e]
    | .sumExpr coll body =>
      -- Both sides use sumN; congr + funext reduces to per-item correctness.
      simp [evalExpr, evalSmtExpr, compileInvExpr]
      congr 1
      funext i
      exact compileInvExpr_preserves (itemEnvAt env coll.toKey i) body

  /-- Boolean counterpart of compileInvExpr_preserves. Covers cmp, logic, neg, and isPresent. -/
  theorem compileInvBoolExpr_preserves (env : Env) (b : BoolExpr) :
      evalBoolExpr env b = evalSmtBoolExpr env (compileInvBoolExpr b) := by
    match b with
    | .cmp op l r =>
      simp [evalBoolExpr, evalSmtBoolExpr, compileInvBoolExpr]
      rw [compileInvExpr_preserves env l, compileInvExpr_preserves env r]
    | .logic op l r =>
      simp [evalBoolExpr, evalSmtBoolExpr, compileInvBoolExpr]
      rw [compileInvBoolExpr_preserves env l, compileInvBoolExpr_preserves env r]
    | .neg inner =>
      simp [evalBoolExpr, evalSmtBoolExpr, compileInvBoolExpr]
      rw [compileInvBoolExpr_preserves env inner]
    | .isPresent ref =>
      simp [evalBoolExpr, compileInvBoolExpr, evalSmtBoolExpr, evalCompOp, evalSmtExpr]
end

/-- For any env and invariant: dslSemantics env inv = smtSemantics env (compile inv).
    The top-level correctness guarantee. -/
theorem compile_preserves_semantics (env : Env) (inv : Invariant) :
    dslSemantics env inv = smtSemantics env (compile inv) := by
  simp [dslSemantics, smtSemantics, compile, compileInvBoolExpr_preserves]
