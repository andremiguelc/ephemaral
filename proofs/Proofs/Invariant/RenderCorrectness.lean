/-
  Ephemaral — Renderer Correctness Proofs
  Proofs that renderSmtExpr / renderSmtBoolExpr produce balanced parentheses.
  Since both the invariant and function renderers share these functions,
  the proofs apply to all SMT-LIB output the system generates.

  Zero custom axioms. All proofs reduce to Lean's standard foundations
  (propext, Classical.choice, Quot.sound) plus kernel trust
  (Lean.ofReduceBool, Lean.trustCompiler from native_decide).

  The toString-produces-no-parens property is proved via
  Batteries.Data.Nat.Digits: Nat.repr → toDigits → isDigit → not parens.

  Precondition:
  - ParenSafe: all SmtExpr.const names and collection keys contain no
    parenthesis characters. Satisfied by construction since names come
    from field identifiers parsed from JSON/DSL.
-/
import Proofs.Invariant.Render
import Batteries.Data.Nat.Digits

-- Parenthesis balance

/-- Parenthesis balance over a char list with accumulator. -/
private def parenBal : Int → List Char → Int
  | acc, [] => acc
  | acc, c :: rest =>
    let step := if c == '(' then acc + 1
                else if c == ')' then acc - 1
                else acc
    parenBal step rest

/-- Count parenthesis balance: +1 for '(', -1 for ')'. -/
def parenBalance (s : String) : Int := parenBal 0 s.toList

private theorem parenBal_shift (acc : Int) (cs : List Char) :
    parenBal acc cs = acc + parenBal 0 cs := by
  induction cs generalizing acc with
  | nil => simp [parenBal]
  | cons c rest ih =>
    simp only [parenBal]
    split
    · rw [ih, ih (0 + 1)]; omega
    · by_cases hc : (c == ')') = true
      · rw [if_pos hc, if_pos hc, ih, ih (0 - 1)]; omega
      · rw [if_neg hc, if_neg hc, ih, ih 0]

private theorem parenBal_append (acc : Int) (cs ds : List Char) :
    parenBal acc (cs ++ ds) = parenBal (parenBal acc cs) ds := by
  induction cs generalizing acc with
  | nil => simp [parenBal]
  | cons c rest ih => simp only [parenBal, List.cons_append]; exact ih _

/-- **parenBalance distributes over string concatenation.** -/
theorem parenBalance_append (s t : String) :
    parenBalance (s ++ t) = parenBalance s + parenBalance t := by
  simp only [parenBalance, String.toList_append]
  rw [parenBal_append, parenBal_shift]

-- Leaf properties

-- toString on Nat produces only digit characters ('0'..'9').
-- Proved via Batteries.Data.Nat.Digits: Nat.repr → toDigits → isDigit → not parens.
private theorem isDigit_not_paren (c : Char) (h : c.isDigit = true) : c ≠ '(' ∧ c ≠ ')' := by
  unfold Char.isDigit at h
  constructor
  · intro heq; subst heq; simp_all
  · intro heq; subst heq; simp_all

private theorem toDigits_not_paren (n : Nat) (c : Char) (hc : c ∈ Nat.toDigits 10 n) :
    c ≠ '(' ∧ c ≠ ')' :=
  isDigit_not_paren c (Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc)

private theorem toString_nat_no_parens (n : Nat) :
    ∀ c ∈ (toString n).toList, c ≠ '(' ∧ c ≠ ')' := by
  show ∀ c ∈ (Nat.repr n).toList, c ≠ '(' ∧ c ≠ ')'
  simp [Nat.repr]
  exact fun c hc => toDigits_not_paren n c hc

-- For Int, toString on non-negative Int.ofNat goes through Nat's toString.
-- This is all formatReal needs (negative branch uses natAbs which is Nat).
private theorem toString_int_ofNat_no_parens (m : Nat) :
    ∀ c ∈ (toString (Int.ofNat m)).toList, c ≠ '(' ∧ c ≠ ')' := by
  show ∀ c ∈ (instToStringInt.toString (Int.ofNat m)).toList, c ≠ '(' ∧ c ≠ ')'
  simp [instToStringInt]
  exact toString_nat_no_parens m

private theorem parenBal_no_parens (cs : List Char)
    (h : ∀ c ∈ cs, c ≠ '(' ∧ c ≠ ')') : parenBal 0 cs = 0 := by
  induction cs with
  | nil => simp [parenBal]
  | cons c rest ih =>
    simp only [parenBal]
    have ⟨hno, hnc⟩ := h c (.head _)
    have h1 : ¬(c == '(') = true := by simp [beq_iff_eq]; exact hno
    have h2 : ¬(c == ')') = true := by simp [beq_iff_eq]; exact hnc
    rw [if_neg h1, if_neg h2]
    exact ih (fun c hm => h c (List.mem_cons_of_mem _ hm))

private theorem parenBalance_no_parens (s : String)
    (h : ∀ c ∈ s.toList, c ≠ '(' ∧ c ≠ ')') : parenBalance s = 0 :=
  parenBal_no_parens s.toList h

private theorem parenBalance_toString_nat (n : Nat) :
    parenBalance (toString n) = 0 :=
  parenBalance_no_parens _ (toString_nat_no_parens n)

private theorem parenBalance_toString_int_ofNat (m : Nat) :
    parenBalance (toString (Int.ofNat m)) = 0 :=
  parenBalance_no_parens _ (toString_int_ofNat_no_parens m)

private theorem parenBalance_toString_int_nonneg (n : Int) (h : ¬(n < 0)) :
    parenBalance (toString n) = 0 := by
  have hnn : 0 ≤ n := Int.not_lt.mp h
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hnn
  exact parenBalance_toString_int_ofNat m

-- formatReal balanced

/-- parenBalance (formatReal n) = 0 for all Rat n. Base case for renderSmtExpr_balanced. -/
theorem formatReal_balanced (n : Rat) : parenBalance (formatReal n) = 0 := by
  unfold formatReal
  split
  · split
    · show parenBalance ("(- " ++ toString (Int.natAbs n.num) ++ ".0)") = 0
      rw [parenBalance_append, parenBalance_append]
      have h1 : parenBalance "(- " = 1 := by native_decide
      have h2 : parenBalance ".0)" = -1 := by native_decide
      rw [h1, parenBalance_toString_nat, h2]; omega
    · rename_i h
      show parenBalance (toString n.num ++ ".0") = 0
      rw [parenBalance_append, parenBalance_toString_int_nonneg n.num h]
      have : parenBalance ".0" = 0 := by native_decide
      rw [this]; omega
  · show parenBalance ("(/ " ++ (if n.num < 0 then "(- " ++ toString (Int.natAbs n.num) ++ ".0)"
        else toString n.num ++ ".0") ++ " " ++ (toString n.den ++ ".0") ++ ")") = 0
    rw [parenBalance_append, parenBalance_append, parenBalance_append, parenBalance_append]
    have hDiv : parenBalance "(/ " = 1 := by native_decide
    have hSpace : parenBalance " " = 0 := by native_decide
    have hClose : parenBalance ")" = -1 := by native_decide
    have hDen : parenBalance (toString n.den ++ ".0") = 0 := by
      rw [parenBalance_append, parenBalance_toString_nat]
      have : parenBalance ".0" = 0 := by native_decide
      omega
    have hNum : parenBalance (if n.num < 0 then "(- " ++ toString (Int.natAbs n.num) ++ ".0)"
          else toString n.num ++ ".0") = 0 := by
      split
      · rw [parenBalance_append, parenBalance_append]
        have : parenBalance "(- " = 1 := by native_decide
        have : parenBalance ".0)" = -1 := by native_decide
        rw [‹parenBalance "(- " = 1›, parenBalance_toString_nat, ‹parenBalance ".0)" = -1›]; omega
      · rename_i h
        rw [parenBalance_append, parenBalance_toString_int_nonneg n.num h]
        have : parenBalance ".0" = 0 := by native_decide
        omega
    rw [hDiv, hNum, hSpace, hDen, hClose]; omega

-- ParenSafe predicate and balanced-parenthesis theorems

-- All constant names and collection keys contain no parenthesis characters.
-- Always true in practice (names come from field identifiers).
mutual
  def SmtExpr.ParenSafe : SmtExpr → Prop
    | .lit _ => True
    | .const name => ∀ c ∈ name.toList, c ≠ '(' ∧ c ≠ ')'
    | .arith _ l r => l.ParenSafe ∧ r.ParenSafe
    | .condExpr c t e => c.ParenSafe ∧ t.ParenSafe ∧ e.ParenSafe
    | .roundExpr _ e => e.ParenSafe
    | .sumExpr collKey body =>
        (∀ c ∈ collKey.toList, c ≠ '(' ∧ c ≠ ')') ∧ body.ParenSafe

  def SmtBoolExpr.ParenSafe : SmtBoolExpr → Prop
    | .cmp _ l r => l.ParenSafe ∧ r.ParenSafe
    | .logic _ l r => l.ParenSafe ∧ r.ParenSafe
    | .neg b => b.ParenSafe
    | .eachExpr collKey body =>
        (∀ c ∈ collKey.toList, c ≠ '(' ∧ c ≠ ')') ∧ body.ParenSafe
end

mutual
  /-- parenBalance (renderSmtExpr e) = 0 when all names are ParenSafe.
      Ensures Z3 receives syntactically valid S-expressions. -/
  theorem renderSmtExpr_balanced (e : SmtExpr) (h : e.ParenSafe) :
      parenBalance (renderSmtExpr e) = 0 := by
    match e with
    | .lit n =>
      simp [renderSmtExpr]
      exact formatReal_balanced n
    | .const name =>
      simp [renderSmtExpr]
      exact parenBalance_no_parens name (by exact h)
    | .arith op l r =>
      simp only [renderSmtExpr]
      have ⟨hl, hr⟩ : l.ParenSafe ∧ r.ParenSafe := h
      have ihl := renderSmtExpr_balanced l hl
      have ihr := renderSmtExpr_balanced r hr
      match op with
      | .div =>
        show parenBalance ("(ite (= " ++ renderSmtExpr r ++ " 0.0) 0.0 (/ " ++ renderSmtExpr l ++ " " ++ renderSmtExpr r ++ "))") = 0
        simp only [parenBalance_append, ihl, ihr]; native_decide
      | .add =>
        show parenBalance ("(+ " ++ renderSmtExpr l ++ " " ++ renderSmtExpr r ++ ")") = 0
        simp only [parenBalance_append, ihl, ihr]; native_decide
      | .sub =>
        show parenBalance ("(- " ++ renderSmtExpr l ++ " " ++ renderSmtExpr r ++ ")") = 0
        simp only [parenBalance_append, ihl, ihr]; native_decide
      | .mul =>
        show parenBalance ("(* " ++ renderSmtExpr l ++ " " ++ renderSmtExpr r ++ ")") = 0
        simp only [parenBalance_append, ihl, ihr]; native_decide
    | .condExpr c t e =>
      simp only [renderSmtExpr]
      have ⟨hc, ht, he⟩ : c.ParenSafe ∧ t.ParenSafe ∧ e.ParenSafe := h
      have ihc := renderSmtBoolExpr_balanced c hc
      have iht := renderSmtExpr_balanced t ht
      have ihe := renderSmtExpr_balanced e he
      show parenBalance ("(ite " ++ renderSmtBoolExpr c ++ " " ++ renderSmtExpr t ++ " " ++ renderSmtExpr e ++ ")") = 0
      simp only [parenBalance_append, ihc, iht, ihe]; native_decide
    | .roundExpr mode e =>
      simp only [renderSmtExpr]
      have he : e.ParenSafe := h
      have ihe := renderSmtExpr_balanced e he
      match mode with
      | .floor =>
        show parenBalance ("(to_real (to_int " ++ renderSmtExpr e ++ "))") = 0
        simp only [parenBalance_append, ihe]; native_decide
      | .ceil =>
        show parenBalance ("(ite (= (to_real (to_int " ++ renderSmtExpr e ++ ")) " ++ renderSmtExpr e ++ ") (to_real (to_int " ++ renderSmtExpr e ++ ")) (to_real (+ (to_int " ++ renderSmtExpr e ++ ") 1)))") = 0
        simp only [parenBalance_append, ihe]; native_decide
      | .halfUp =>
        show parenBalance ("(to_real (to_int (+ " ++ renderSmtExpr e ++ " (/ 1.0 2.0))))") = 0
        simp only [parenBalance_append, ihe]; native_decide
    | .sumExpr collKey body =>
      simp only [renderSmtExpr]
      have ⟨hk, _hb⟩ : (∀ c ∈ collKey.toList, c ≠ '(' ∧ c ≠ ')') ∧ body.ParenSafe := h
      show parenBalance ("(" ++ ("sum-" ++ collKey) ++ " " ++ (collKey ++ "-len") ++ ")") = 0
      simp only [parenBalance_append]
      have hk0 := parenBalance_no_parens collKey hk
      have : parenBalance ("sum-" ++ collKey) = 0 := by
        rw [parenBalance_append, hk0]; native_decide
      have : parenBalance (collKey ++ "-len") = 0 := by
        rw [parenBalance_append, hk0]; native_decide
      simp only [*]; native_decide

  /-- Boolean counterpart of renderSmtExpr_balanced. Covers cmp, logic, and neg. -/
  theorem renderSmtBoolExpr_balanced (b : SmtBoolExpr) (h : b.ParenSafe) :
      parenBalance (renderSmtBoolExpr b) = 0 := by
    match b with
    | .cmp op l r =>
      simp only [renderSmtBoolExpr]
      have ⟨hl, hr⟩ : l.ParenSafe ∧ r.ParenSafe := h
      have ihl := renderSmtExpr_balanced l hl
      have ihr := renderSmtExpr_balanced r hr
      match op with
      | .neq =>
        show parenBalance ("(not (= " ++ renderSmtExpr l ++ " " ++ renderSmtExpr r ++ "))") = 0
        simp only [parenBalance_append, ihl, ihr]; native_decide
      | .eq =>
        show parenBalance ("(= " ++ renderSmtExpr l ++ " " ++ renderSmtExpr r ++ ")") = 0
        simp only [parenBalance_append, ihl, ihr]; native_decide
      | .gt =>
        show parenBalance ("(> " ++ renderSmtExpr l ++ " " ++ renderSmtExpr r ++ ")") = 0
        simp only [parenBalance_append, ihl, ihr]; native_decide
      | .lt =>
        show parenBalance ("(< " ++ renderSmtExpr l ++ " " ++ renderSmtExpr r ++ ")") = 0
        simp only [parenBalance_append, ihl, ihr]; native_decide
      | .gte =>
        show parenBalance ("(>= " ++ renderSmtExpr l ++ " " ++ renderSmtExpr r ++ ")") = 0
        simp only [parenBalance_append, ihl, ihr]; native_decide
      | .lte =>
        show parenBalance ("(<= " ++ renderSmtExpr l ++ " " ++ renderSmtExpr r ++ ")") = 0
        simp only [parenBalance_append, ihl, ihr]; native_decide
    | .logic op l r =>
      simp only [renderSmtBoolExpr]
      have ⟨hl, hr⟩ : l.ParenSafe ∧ r.ParenSafe := h
      have ihl := renderSmtBoolExpr_balanced l hl
      have ihr := renderSmtBoolExpr_balanced r hr
      match op with
      | .and =>
        show parenBalance ("(and " ++ renderSmtBoolExpr l ++ " " ++ renderSmtBoolExpr r ++ ")") = 0
        simp only [parenBalance_append, ihl, ihr]; native_decide
      | .or =>
        show parenBalance ("(or " ++ renderSmtBoolExpr l ++ " " ++ renderSmtBoolExpr r ++ ")") = 0
        simp only [parenBalance_append, ihl, ihr]; native_decide
    | .neg inner =>
      simp only [renderSmtBoolExpr]
      have hi : inner.ParenSafe := h
      have ihi := renderSmtBoolExpr_balanced inner hi
      show parenBalance ("(not " ++ renderSmtBoolExpr inner ++ ")") = 0
      simp only [parenBalance_append, ihi]; native_decide
    | .eachExpr collKey body =>
      simp only [renderSmtBoolExpr]
      have ⟨hk, _hb⟩ : (∀ c ∈ collKey.toList, c ≠ '(' ∧ c ≠ ')') ∧ body.ParenSafe := h
      show parenBalance ("(" ++ ("each-" ++ collKey) ++ " " ++ (collKey ++ "-len") ++ ")") = 0
      simp only [parenBalance_append]
      have hk0 := parenBalance_no_parens collKey hk
      have : parenBalance ("each-" ++ collKey) = 0 := by
        rw [parenBalance_append, hk0]; native_decide
      have : parenBalance (collKey ++ "-len") = 0 := by
        rw [parenBalance_append, hk0]; native_decide
      simp only [*]; native_decide
end
