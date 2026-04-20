/-
  Ephemaral — Function Compiler Correctness Proof
  Machine-checked proof that the function expression compiler preserves semantics.

  Layer 1: language-agnostic. Proved once, works for any language frontend.
-/
import Proofs.Function.Compile
import Proofs.Function.Semantics
import Proofs.Invariant.Correctness

/-- Shared bridge for the `sumExpr` and `eachExpr` cases of the function
    correctness proof. Under `CollectionSafe` (compound collection names
    don't appear in `inputFields`, so `funEnv` passes them through) and
    `CollectionPassthrough` (the environment maps bare and `in-`-prefixed
    collection keys to the same values), the two sides agree on both the
    stored length and the per-item sub-environment. -/
theorem funEnv_collection_bridge (env : Env) (inputFields : List String) (coll : FieldRef)
    (h_safe : CollectionSafe inputFields)
    (h_pass : CollectionPassthrough env) :
    (funEnv env inputFields (coll.toKey ++ "-len")).floor.toNat
        = (env ("in-" ++ coll.toKey ++ "-len")).floor.toNat
    ∧ (∀ i, itemEnvAt (funEnv env inputFields) coll.toKey i
          = itemEnvAt env ("in-" ++ coll.toKey) i) := by
  refine ⟨?_, ?_⟩
  · -- Length bridge: funEnv → bare env (CollectionSafe) → in-prefixed (CollectionPassthrough).
    have hLen : (funEnv env inputFields (coll.toKey ++ "-len")).floor.toNat
              = (env (coll.toKey ++ "-len")).floor.toNat := by
      simp only [funEnv]
      split
      · rename_i h_in
        have := (h_safe coll.toKey 0 "").2
        simp_all
      · rfl
    rw [hLen, h_pass coll.toKey "-len"]
  · -- Per-item bridge: same two-step chain, indexed.
    intro i
    funext name
    have hItemEnv : itemEnvAt (funEnv env inputFields) coll.toKey i name
                  = itemEnvAt env coll.toKey i name := by
      simp only [itemEnvAt, funEnv]
      split
      · rename_i h_in
        have := (h_safe coll.toKey i name).1
        simp_all
      · rfl
    rw [hItemEnv]
    simp only [itemEnvAt]
    have := h_pass coll.toKey ("-" ++ toString i ++ "-" ++ name)
    simp only [String.append_assoc] at this ⊢
    exact this

mutual
  /-- evalExpr (funEnv env inputFields) e = evalSmtExpr env (compileFunExpr inputFields e).
      Needs CollectionSafe (compound names not in inputFields) and
      CollectionPassthrough (env(k++s) = env("in-"++k++s)). -/
  theorem compileFunExpr_preserves (env : Env) (inputFields : List String) (e : Expr)
      (h_safe : CollectionSafe inputFields)
      (h_pass : CollectionPassthrough env) :
      evalExpr (funEnv env inputFields) e
      = evalSmtExpr env (compileFunExpr inputFields e) := by
    match e with
    | .lit n =>
      simp [evalExpr, evalSmtExpr, compileFunExpr]
    | .field ref =>
      cases ref with
      | simple name =>
        simp [evalExpr, compileFunExpr, funEnv, inField, FieldRef.toKey]
        split <;> simp [evalSmtExpr]
      | qualified qual name =>
        simp [evalExpr, compileFunExpr, funEnv, inField, FieldRef.toKey]
        split <;> simp [evalSmtExpr]
    | .arith op l r =>
      simp [evalExpr, evalSmtExpr, compileFunExpr]
      rw [compileFunExpr_preserves env inputFields l h_safe h_pass,
          compileFunExpr_preserves env inputFields r h_safe h_pass]
    | .condExpr c t e =>
      simp [evalExpr, evalSmtExpr, compileFunExpr]
      rw [compileFunBoolExpr_preserves env inputFields c h_safe h_pass]
      split
      · exact compileFunExpr_preserves env inputFields t h_safe h_pass
      · exact compileFunExpr_preserves env inputFields e h_safe h_pass
    | .roundExpr mode e =>
      simp [evalExpr, evalSmtExpr, compileFunExpr]
      rw [compileFunExpr_preserves env inputFields e h_safe h_pass]
    | .sumExpr coll body =>
      simp only [evalExpr, evalSmtExpr, compileFunExpr, inField]
      obtain ⟨hLen, hItem⟩ := funEnv_collection_bridge env inputFields coll h_safe h_pass
      rw [hLen]
      congr 1
      funext i
      rw [hItem i]
      exact compileInvExpr_preserves (itemEnvAt env ("in-" ++ coll.toKey) i) body

  /-- Boolean counterpart of compileFunExpr_preserves.
      Same preconditions (CollectionSafe, CollectionPassthrough). -/
  theorem compileFunBoolExpr_preserves (env : Env) (inputFields : List String) (b : BoolExpr)
      (h_safe : CollectionSafe inputFields)
      (h_pass : CollectionPassthrough env) :
      evalBoolExpr (funEnv env inputFields) b
      = evalSmtBoolExpr env (compileFunBoolExpr inputFields b) := by
    match b with
    | .cmp op l r =>
      simp [evalBoolExpr, evalSmtBoolExpr, compileFunBoolExpr]
      rw [compileFunExpr_preserves env inputFields l h_safe h_pass,
          compileFunExpr_preserves env inputFields r h_safe h_pass]
    | .logic op l r =>
      simp [evalBoolExpr, evalSmtBoolExpr, compileFunBoolExpr]
      rw [compileFunBoolExpr_preserves env inputFields l h_safe h_pass,
          compileFunBoolExpr_preserves env inputFields r h_safe h_pass]
    | .neg inner =>
      simp [evalBoolExpr, evalSmtBoolExpr, compileFunBoolExpr]
      rw [compileFunBoolExpr_preserves env inputFields inner h_safe h_pass]
    | .isPresent ref =>
      cases ref with
      | simple name =>
        simp [evalBoolExpr, compileFunBoolExpr, evalSmtBoolExpr, evalCompOp,
              evalSmtExpr, funEnv, inField, FieldRef.toKey]
        split <;> simp [evalSmtExpr]
      | qualified qual name =>
        simp [evalBoolExpr, compileFunBoolExpr, evalSmtBoolExpr, evalCompOp,
              evalSmtExpr, funEnv, inField, FieldRef.toKey]
        split <;> simp [evalSmtExpr]
    | .eachExpr coll body =>
      simp only [evalBoolExpr, evalSmtBoolExpr, compileFunBoolExpr, inField]
      obtain ⟨hLen, hItem⟩ := funEnv_collection_bridge env inputFields coll h_safe h_pass
      rw [hLen]
      congr 1
      funext i
      rw [hItem i]
      exact compileInvBoolExpr_preserves (itemEnvAt env ("in-" ++ coll.toKey) i) body
end
