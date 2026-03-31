/-
  Ephemaral — Function Compiler Correctness Proof
  Machine-checked proof that the function expression compiler preserves semantics.

  Layer 1: language-agnostic. Proved once, works for any language frontend.
-/
import Proofs.Function.Compile
import Proofs.Function.Semantics
import Proofs.Invariant.Correctness

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
      -- CollectionSafe: compound names aren't in inputFields, so funEnv doesn't prefix them.
      -- CollectionPassthrough: env(k ++ s) = env("in-" ++ k ++ s), bridging the two sides.
      have hItemEnv : ∀ i, itemEnvAt (funEnv env inputFields) coll.toKey i
                        = itemEnvAt env coll.toKey i := by
        intro i; funext name; simp only [itemEnvAt, funEnv]
        split
        · rename_i h_in
          have := (h_safe coll.toKey i name).1
          simp_all
        · rfl
      have hLen : (funEnv env inputFields (coll.toKey ++ "-len")).floor.toNat
                = (env (coll.toKey ++ "-len")).floor.toNat := by
        simp only [funEnv]
        split
        · rename_i h_in
          have := (h_safe coll.toKey 0 "").2
          simp_all
        · rfl
      -- Bridge bare collKey ↔ in-prefixed collKey via CollectionPassthrough.
      have hLenBridge : (env (coll.toKey ++ "-len")).floor.toNat
                      = (env ("in-" ++ coll.toKey ++ "-len")).floor.toNat := by
        rw [h_pass coll.toKey "-len"]
      have hItemBridge : ∀ i, itemEnvAt env coll.toKey i
                           = itemEnvAt env ("in-" ++ coll.toKey) i := by
        intro i; funext name; simp only [itemEnvAt]
        -- Goal: env (collKey ++ "-" ++ i ++ "-" ++ name) = env ("in-" ++ collKey ++ "-" ++ i ++ "-" ++ name)
        -- h_pass gives: env (k ++ suffix) = env ("in-" ++ k ++ suffix) for any suffix
        -- Need to normalize string associativity
        have := h_pass coll.toKey ("-" ++ toString i ++ "-" ++ name)
        simp only [String.append_assoc] at this ⊢
        exact this
      -- Now assemble: DSL → bare env → in-prefixed env → SMT
      rw [hLen, hLenBridge]
      congr 1
      funext i; rw [hItemEnv, hItemBridge]
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
end
