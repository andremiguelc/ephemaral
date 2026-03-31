/-
  Ephemaral — Renderer Correctness Proofs
  Machine-checked proofs that the renderer transformations preserve semantics.

  The compilers (Invariant/Compile, Function/Compile) produce proved SmtExpr types.
  The renderers transform these types before generating SMT-LIB text for Z3.
  These proofs ensure the transformations don't corrupt the expressions:
  - prefixSmtExpr: adds "in-"/"out-" prefixes for input/output context
  - rewriteCollections: remaps collection keys for pass-through collections
  - operator mappings: type constructors → SMT-LIB operator strings
-/
import Proofs.Function.Render
import Proofs.Semantics

-- Prefix preservation

mutual
  /-- evalSmtExpr env (prefixSmtExpr pfx e) = evalSmtExpr (fun n => env (pfx ++ n)) e.
      Prefixing shifts the lookup keys without changing the result. -/
  theorem prefixSmtExpr_preserves (env : Env) (pfx : String) (e : SmtExpr) :
      evalSmtExpr env (prefixSmtExpr pfx e)
      = evalSmtExpr (fun name => env (pfx ++ name)) e := by
    match e with
    | .lit n =>
      simp [evalSmtExpr, prefixSmtExpr]
    | .const name =>
      simp [evalSmtExpr, prefixSmtExpr]
    | .arith op l r =>
      simp [evalSmtExpr, prefixSmtExpr]
      rw [prefixSmtExpr_preserves env pfx l,
          prefixSmtExpr_preserves env pfx r]
    | .condExpr c t e =>
      simp [evalSmtExpr, prefixSmtExpr]
      rw [prefixSmtBoolExpr_preserves env pfx c]
      split
      · exact prefixSmtExpr_preserves env pfx t
      · exact prefixSmtExpr_preserves env pfx e
    | .roundExpr mode e =>
      simp [evalSmtExpr, prefixSmtExpr]
      rw [prefixSmtExpr_preserves env pfx e]
    | .sumExpr collKey body =>
      simp only [evalSmtExpr, prefixSmtExpr]
      -- Prefixed: eval with collKey = pfx ++ collKey, body bare, env = env
      -- Shifted: eval with collKey = collKey, body bare, env = (pfx ++ ·)
      -- These agree because (pfx ++ collKey) ++ suffix = pfx ++ (collKey ++ suffix)
      have hLen : (env ((pfx ++ collKey) ++ "-len")).floor.toNat
                = ((fun name => env (pfx ++ name)) (collKey ++ "-len")).floor.toNat := by
        simp only [String.append_assoc]
      have hItem : ∀ i, itemEnvAt env (pfx ++ collKey) i
                     = itemEnvAt (fun name => env (pfx ++ name)) collKey i := by
        intro i; funext name; simp only [itemEnvAt, String.append_assoc]
      rw [hLen]
      congr 1
      funext i; rw [hItem]

  /-- Boolean counterpart of prefixSmtExpr_preserves. -/
  theorem prefixSmtBoolExpr_preserves (env : Env) (pfx : String) (b : SmtBoolExpr) :
      evalSmtBoolExpr env (prefixSmtBoolExpr pfx b)
      = evalSmtBoolExpr (fun name => env (pfx ++ name)) b := by
    match b with
    | .cmp op l r =>
      simp [evalSmtBoolExpr, prefixSmtBoolExpr]
      rw [prefixSmtExpr_preserves env pfx l,
          prefixSmtExpr_preserves env pfx r]
    | .logic op l r =>
      simp [evalSmtBoolExpr, prefixSmtBoolExpr]
      rw [prefixSmtBoolExpr_preserves env pfx l,
          prefixSmtBoolExpr_preserves env pfx r]
    | .neg inner =>
      simp [evalSmtBoolExpr, prefixSmtBoolExpr]
      rw [prefixSmtBoolExpr_preserves env pfx inner]
end

-- Collection rewriting preservation

mutual
  /-- Rewriting collection keys preserves evalSmtExpr when each (old, new) pair
      satisfies env(old ++ s) = env(new ++ s) for all suffixes s. -/
  theorem rewriteCollections_preserves
      (env : Env) (rewrites : List (String × String)) (e : SmtExpr)
      (h_equiv : ∀ old new, (old, new) ∈ rewrites →
        (∀ suffix, env (old ++ suffix) = env (new ++ suffix))) :
      evalSmtExpr env (rewriteCollections rewrites e) = evalSmtExpr env e := by
    match e with
    | .lit n =>
      simp [evalSmtExpr, rewriteCollections]
    | .const name =>
      simp [evalSmtExpr, rewriteCollections]
    | .arith op l r =>
      simp [evalSmtExpr, rewriteCollections]
      rw [rewriteCollections_preserves env rewrites l h_equiv,
          rewriteCollections_preserves env rewrites r h_equiv]
    | .condExpr c t e =>
      simp [evalSmtExpr, rewriteCollections]
      rw [rewriteBoolCollections_preserves env rewrites c h_equiv]
      split
      · exact rewriteCollections_preserves env rewrites t h_equiv
      · exact rewriteCollections_preserves env rewrites e h_equiv
    | .roundExpr mode e =>
      simp [evalSmtExpr, rewriteCollections]
      rw [rewriteCollections_preserves env rewrites e h_equiv]
    | .sumExpr collKey body =>
      simp only [evalSmtExpr, rewriteCollections]
      -- The rewrite changes collKey to newKey (if found in rewrites).
      -- h_equiv guarantees env(old ++ suffix) = env(new ++ suffix) for all suffixes.
      -- Body is unchanged (rewriteCollections doesn't recurse into sumExpr body).
      -- We split on the find? result:
      split
      · -- Found a rewrite: (old, new) where old == collKey
        rename_i old new h_find
        have h_in := List.mem_of_find?_eq_some h_find
        have h_pred := List.find?_some h_find
        have h_eq : old = collKey := by rwa [beq_iff_eq] at h_pred
        -- h_equiv gives env(old ++ s) = env(new ++ s), rewrite old → collKey
        have h_suf := fun suffix => h_eq ▸ h_equiv old new h_in suffix
        -- h_suf : env(collKey ++ suffix) = env(new ++ suffix)
        congr 1
        · -- Per-item bodies: itemEnvAt env new i = itemEnvAt env collKey i
          funext i; congr 1; funext name; simp only [itemEnvAt]
          have := (h_suf ("-" ++ toString i ++ "-" ++ name)).symm
          simp only [String.append_assoc] at this ⊢
          exact this
        · -- Length: env(new ++ "-len") = env(collKey ++ "-len")
          exact congrArg (fun x => x.floor.toNat) (h_suf "-len").symm
      · -- No rewrite found: expression unchanged
        rfl

  /-- Boolean counterpart of rewriteCollections_preserves. -/
  theorem rewriteBoolCollections_preserves
      (env : Env) (rewrites : List (String × String)) (b : SmtBoolExpr)
      (h_equiv : ∀ old new, (old, new) ∈ rewrites →
        (∀ suffix, env (old ++ suffix) = env (new ++ suffix))) :
      evalSmtBoolExpr env (rewriteBoolCollections rewrites b) = evalSmtBoolExpr env b := by
    match b with
    | .cmp op l r =>
      simp [evalSmtBoolExpr, rewriteBoolCollections]
      rw [rewriteCollections_preserves env rewrites l h_equiv,
          rewriteCollections_preserves env rewrites r h_equiv]
    | .logic op l r =>
      simp [evalSmtBoolExpr, rewriteBoolCollections]
      rw [rewriteBoolCollections_preserves env rewrites l h_equiv,
          rewriteBoolCollections_preserves env rewrites r h_equiv]
    | .neg inner =>
      simp [evalSmtBoolExpr, rewriteBoolCollections]
      rw [rewriteBoolCollections_preserves env rewrites inner h_equiv]
end

-- Operator mapping contracts

/-- Arithmetic operator mapping is correct and exhaustive. -/
theorem arithOpToSmt_exhaustive : ∀ op : ArithOp,
    arithOpToSmt op = match op with
    | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" := by
  intro op; cases op <;> rfl

/-- Comparison operator mapping is correct and exhaustive. -/
theorem compOpToSmt_exhaustive : ∀ op : CompOp,
    compOpToSmt op = match op with
    | .eq => "=" | .neq => "distinct" | .gt => ">"
    | .lt => "<" | .gte => ">=" | .lte => "<=" := by
  intro op; cases op <;> rfl

/-- Logic operator mapping is correct and exhaustive. -/
theorem logicOpToSmt_exhaustive : ∀ op : LogicOp,
    logicOpToSmt op = match op with
    | .and => "and" | .or => "or" := by
  intro op; cases op <;> rfl
