/-
  Ephemaral — Parser Correctness Proofs
  Machine-checked proofs about the invariant DSL parser.
-/
import Proofs.Invariant.Parser

-- Operator parsing

/-- **parseOp is sound.** If parseOp returns an operator, the input string
    is one of the recognized comparison operator tokens. -/
theorem parseOp_sound (s : String) (op : CompOp) :
    parseOp s = some op → s ∈ compOpTokens := by
  intro h
  simp [parseOp] at h
  simp [compOpTokens]
  split at h <;> simp_all

/-- **parseOp is complete.** Every CompOp has a string that roundtrips
    through parseOp. -/
theorem parseOp_complete : ∀ op : CompOp,
    ∃ s, s ∈ compOpTokens ∧ parseOp s = some op := by
  intro op
  cases op <;> simp [compOpTokens, parseOp]

-- Atom parsers

/-- **parseSimpleExpr produces atoms.** If parseSimpleExpr succeeds,
    the result is either a literal or a simple field reference. -/
theorem parseSimpleExpr_shape (token root : String) (e : Expr) :
    parseSimpleExpr token root = some e →
    (∃ n, e = .lit n) ∨ (∃ name, e = .field (.simple name)) := by
  unfold parseSimpleExpr
  simp [bind, Option.bind]
  split
  · rename_i n _
    intro h; left; exact ⟨n, by simp_all⟩
  · simp [guard]
    split <;> simp
    split <;> simp
    intro h
    right; exact ⟨_, h.symm⟩

/-- **parseItemExpr produces atoms.** If parseItemExpr succeeds,
    the result is either a literal or a simple field reference. -/
theorem parseItemExpr_shape (token : String) (e : Expr) :
    parseItemExpr token = some e →
    (∃ n, e = .lit n) ∨ (∃ name, e = .field (.simple name)) := by
  unfold parseItemExpr
  simp [bind, Option.bind]
  split
  · rename_i n _
    intro h; left; exact ⟨n, by simp_all⟩
  · simp [guard]
    split <;> simp
    split <;> simp
    intro h
    right; exact ⟨_, h.symm⟩

-- Operator index finder

/-- Invariant for `findRightmostOp.go`: if it returns `some idx`,
    then `idx < tokens.length` and `ops.contains tokens[idx]!`. -/
private theorem findRightmostOp_go_inv (tokens : List String) (ops : List String)
    (i depth : Nat) (best : Option Nat)
    (h_best : ∀ j, best = some j → j < tokens.length ∧ ops.contains tokens[j]! = true) :
    ∀ j, findRightmostOp.go tokens ops tokens.length i depth best = some j →
      j < tokens.length ∧ ops.contains tokens[j]! = true := by
  induction h_fuel : tokens.length - i generalizing i depth best with
  | zero =>
    intro j hj
    unfold findRightmostOp.go at hj
    split at hj
    · exact h_best j hj
    · exfalso; omega
  | succ n ih =>
    intro j hj
    unfold findRightmostOp.go at hj
    split at hj
    · exact h_best j hj
    · rename_i h_lt
      apply ih (i + 1) _ _ _ (by omega) j hj
      intro k hk
      split at hk
      · cases hk with
        | refl => exact ⟨by omega, by simp_all⟩
      · exact h_best k hk

/-- **findRightmostOp returns a valid index.**
    If it finds an operator, the index is within the token list. -/
theorem findRightmostOp_in_bounds (tokens : List String) (ops : List String) (idx : Nat) :
    findRightmostOp tokens ops = some idx → idx < tokens.length := by
  intro h
  have inv := findRightmostOp_go_inv tokens ops 0 0 none (by simp)
  simp [findRightmostOp] at h
  exact (inv idx h).1

/-- **findRightmostOp returns an operator position.**
    The token at the returned index is one of the searched operators. -/
theorem findRightmostOp_is_op (tokens : List String) (ops : List String) (idx : Nat) :
    findRightmostOp tokens ops = some idx → ops.contains tokens[idx]! = true := by
  intro h
  have inv := findRightmostOp_go_inv tokens ops 0 0 none (by simp)
  simp [findRightmostOp] at h
  exact (inv idx h).2

-- Parser soundness

/-- **parseCmpExpr is sound.** If parseCmpExpr succeeds, the result is a
    comparison whose operator was found by findCompOpIdx, with both sides
    parsed by parseExpr. -/
theorem parseCmpExpr_sound (tokens : List String) (root : String) (b : BoolExpr) :
    parseCmpExpr tokens root = some b →
    ∃ opIdx op lhs rhs,
      findCompOpIdx tokens = some opIdx ∧
      parseOp tokens[opIdx]! = some op ∧
      parseExpr (tokens.take opIdx) root = some lhs ∧
      parseExpr (tokens.drop (opIdx + 1)) root = some rhs ∧
      b = .cmp op lhs rhs := by
  unfold parseCmpExpr
  simp only [bind, Option.bind]
  -- After unfolding, the do chain is nested match/lambda. Use split to
  -- case on findCompOpIdx, then dsimp to beta-reduce the lambda before
  -- splitting on the inner matches.
  split
  · simp
  · rename_i opIdx
    dsimp only []
    split
    · simp
    · rename_i op
      dsimp only []
      split
      · simp
      · rename_i lhs
        dsimp only []
        split
        · simp
        · rename_i rhs
          intro h
          cases h
          exact ⟨_, _, _, _, opIdx, op, lhs, rhs, rfl⟩

/-- **parseBoolExpr is sound.** If parseBoolExpr succeeds, the result is
    either a conjunction, disjunction, or bare comparison — matching exactly
    which branch of the parser produced it. -/
theorem parseBoolExpr_sound (tokens : List String) (root : String) (b : BoolExpr) :
    parseBoolExpr tokens root = some b →
    (∃ idx l r,
      tokens.findIdx? (· == "and") = some idx ∧
      parseCmpExpr (tokens.take idx) root = some l ∧
      parseCmpExpr (tokens.drop (idx + 1)) root = some r ∧
      b = .logic .and l r) ∨
    (∃ idx l r,
      tokens.findIdx? (· == "or") = some idx ∧
      parseCmpExpr (tokens.take idx) root = some l ∧
      parseCmpExpr (tokens.drop (idx + 1)) root = some r ∧
      b = .logic .or l r) ∨
    (parseCmpExpr tokens root = some b) := by
  unfold parseBoolExpr
  simp only [bind, Option.bind]
  split
  · -- Found "and": do chain with two parseCmpExpr calls
    rename_i idx h_and
    split
    · simp
    · rename_i l
      dsimp only []
      split
      · simp
      · rename_i r
        intro h; cases h
        left; exact ⟨_, _, _, h_and, ‹_›, ‹_›, rfl⟩
  · -- No "and", check "or"
    split
    · rename_i idx h_or
      split
      · simp
      · rename_i l
        dsimp only []
        split
        · simp
        · rename_i r
          intro h; cases h
          right; left; exact ⟨_, _, _, h_or, ‹_›, ‹_›, rfl⟩
    · -- No "and", no "or" → bare comparison
      intro h_cmp
      right; right; exact h_cmp
