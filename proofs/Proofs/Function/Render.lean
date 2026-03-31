/-
  Ephemaral — Function Verification Renderer
  Combines function encoding + invariant fragments into a complete
  SMT-LIB verification file.

  Layer 1: language-agnostic. Works with any CompiledFunction + CompiledInvariants.
-/
import Proofs.Types
import Proofs.Function.Types
import Proofs.Function.Compile
import Proofs.Invariant.Render

mutual
  /-- Prepend a string ("in-"/"out-") to every constant name in an SmtExpr.
      Used by renderVerification to place invariants in input/output context. -/
  def prefixSmtExpr (pfx : String) : SmtExpr → SmtExpr
    | .lit n            => .lit n
    | .const name       => .const (pfx ++ name)
    | .arith op l r     => .arith op (prefixSmtExpr pfx l) (prefixSmtExpr pfx r)
    | .condExpr c t e   => .condExpr (prefixSmtBoolExpr pfx c)
                                      (prefixSmtExpr pfx t) (prefixSmtExpr pfx e)
    | .roundExpr mode e => .roundExpr mode (prefixSmtExpr pfx e)
    | .sumExpr collKey body => .sumExpr (pfx ++ collKey) body
      -- Body fields stay bare — they become accessor names scoped under collKey.
      -- e.g., "subtotal" → "in-lineItems-subtotal" via renderSumDef, not "in-subtotal".

  /-- Prefix all constant names in an SmtBoolExpr. -/
  def prefixSmtBoolExpr (pfx : String) : SmtBoolExpr → SmtBoolExpr
    | .cmp op l r   => .cmp op (prefixSmtExpr pfx l) (prefixSmtExpr pfx r)
    | .logic op l r => .logic op (prefixSmtBoolExpr pfx l) (prefixSmtBoolExpr pfx r)
    | .neg b        => .neg (prefixSmtBoolExpr pfx b)
end

/-- Build an SMT-LIB implication guard for optional fields.
    If any of the fragment's constants are optional, wrap the body in:
    (=> (and (not (= {pfx}has-f1 0.0)) (not (= {pfx}has-f2 0.0)) ...) body)
    If none are optional, return the body as-is. -/
private def guardOptionalBody (pfx : String) (optionalFields : List String)
    (fragConsts : List String) (bodyStr : String) : String :=
  let optConsts := fragConsts.filter optionalFields.contains
  if optConsts.isEmpty then bodyStr
  else
    let guards := optConsts.map fun c => s!"(not (= {pfx}has-{c} 0.0))"
    let guardExpr := match guards with
      | [g] => g
      | _ => s!"(and {" ".intercalate guards})"
    s!"(=> {guardExpr} {bodyStr})"

mutual
  /-- Replace collection keys per a rewrite list: e.g. "out-lineItems" → "in-lineItems"
      for pass-through collections. -/
  def rewriteCollections (rewrites : List (String × String)) : SmtExpr → SmtExpr
    | .lit n            => .lit n
    | .const name       => .const name
    | .arith op l r     => .arith op (rewriteCollections rewrites l) (rewriteCollections rewrites r)
    | .condExpr c t e   => .condExpr (rewriteBoolCollections rewrites c)
                                      (rewriteCollections rewrites t) (rewriteCollections rewrites e)
    | .roundExpr mode e => .roundExpr mode (rewriteCollections rewrites e)
    | .sumExpr collKey body =>
      let newKey := match rewrites.find? (·.1 == collKey) with
        | some (_, replacement) => replacement
        | none => collKey
      .sumExpr newKey body

  def rewriteBoolCollections (rewrites : List (String × String)) : SmtBoolExpr → SmtBoolExpr
    | .cmp op l r   => .cmp op (rewriteCollections rewrites l) (rewriteCollections rewrites r)
    | .logic op l r => .logic op (rewriteBoolCollections rewrites l) (rewriteBoolCollections rewrites r)
    | .neg b        => .neg (rewriteBoolCollections rewrites b)
end

def renderVerification (funFrag : CompiledFunction) (invFrags : List CompiledInvariant)
    (funName : String) (paramPreconditions : List CompiledInvariant := [])
    (optionalFields : List String := []) : String :=
  let header := s!"; Ephemaral — Function verification: {funName}"

  -- Detect collections from invariant fragments (find sumExpr nodes)
  let inputSumDefs := invFrags.flatMap fun frag =>
    collectSumBoolExprs (prefixSmtBoolExpr "in-" frag.body)
  -- All collections pass through (Scenario A: read-only collections)
  -- Output invariants reuse input accessor functions.
  -- Strip "in-" prefix (3 chars) from input collKey to get bare collection name
  let stripInPrefix (s : String) : String := (s.drop 3).toString
  let collRewrites := inputSumDefs.map fun sd =>
    ("out-" ++ stripInPrefix sd.collKey, sd.collKey)  -- "out-lineItems" → "in-lineItems"
  -- Names declared by sum defs (to exclude from scalar const declarations).
  -- Include both in- and out- versions since pass-through collections reuse input accessors.
  let sumDeclaredNames := inputSumDefs.flatMap fun sd =>
    let baseName := stripInPrefix sd.collKey
    let inNames := [sd.collKey ++ "-len"] ++ (collectBodyConsts sd.body).eraseDups.map (sd.collKey ++ "-" ++ ·)
    let outNames := ["out-" ++ baseName ++ "-len"] ++ (collectBodyConsts sd.body).eraseDups.map ("out-" ++ baseName ++ "-" ++ ·)
    inNames ++ outNames

  -- 1. Constant declarations
  --    Include constants from invariants too (they may reference fields
  --    the function doesn't directly touch, e.g., subtotal in margin >= 0)
  let invConsts := invFrags.foldl (fun acc frag =>
    acc ++ frag.consts.map (fun c => "in-" ++ c) ++ frag.consts.map (fun c => "out-" ++ c)) []
  -- Parameter precondition constants are bare (no prefix) — they must match param names
  let paramPrecondConsts := paramPreconditions.foldl (fun acc frag => acc ++ frag.consts) []
  let funConsts := funFrag.inConsts ++ funFrag.outConsts ++ funFrag.paramConsts
  let allConsts := (funConsts ++ invConsts ++ paramPrecondConsts).eraseDups
  -- Filter out collection-related names (declared by renderSumDef as Int/functions, not Real)
  let scalarConsts := allConsts.filter fun c => !sumDeclaredNames.contains c
  let constDecls := scalarConsts.map (fun c => s!"(declare-const {c} Real)")

  -- 1b. Collection declarations (accessor functions + define-fun-rec)
  let sumDecls := inputSumDefs.flatMap renderSumDef

  -- 2. Unchanged field equalities
  --    Also include invariant-referenced fields not in the function's field set
  --    (the spread operator preserves them, so out-x = in-x)
  let assignedFields := funFrag.assignDefs.map (·.1)
  let extraUnchanged := invConsts
    |>.filter (·.startsWith "out-")
    |>.filter (fun c => !funFrag.outConsts.contains c)
    |>.filter (fun c => !assignedFields.contains c)
    -- Also exclude collection-related names from scalar unchanged assertions
    |>.filter (fun c => !sumDeclaredNames.contains c)
    |>.map (fun outC => (outC, "in-" ++ (outC.drop 4).toString))
  let allUnchanged := (funFrag.unchangedEqs ++ extraUnchanged).filter fun (outC, _) =>
    !sumDeclaredNames.contains outC
  let unchangedAsserts := allUnchanged.map (fun (outC, inC) =>
    s!"(assert (= {outC} {inC}))")

  -- 3. Assignment definitions
  let assignAsserts := funFrag.assignDefs.map (fun (outC, expr) =>
    s!"(assert (= {outC} {renderSmtExpr expr}))")

  -- 3b. Presence constraints for optional fields (has-{f} ∈ {0, 1})
  let presenceAsserts := optionalFields.foldl (fun acc f =>
    acc ++ [s!"(assert (or (= in-has-{f} 0.0) (= in-has-{f} 1.0)))",
            s!"(assert (or (= out-has-{f} 0.0) (= out-has-{f} 1.0)))"]) []

  -- 4. Input invariants as preconditions (guarded by presence for optional fields)
  let preconditions := invFrags.map (fun frag =>
    let prefixed := prefixSmtBoolExpr "in-" frag.body
    let bodyStr := renderSmtBoolExpr prefixed
    let guarded := guardOptionalBody "in-" optionalFields frag.consts bodyStr
    s!"(assert {guarded})")

  -- 4b. Parameter preconditions (asserted as-is, no prefix)
  --     These constrain typed parameters using their type's invariants.
  let paramPrecondAsserts := paramPreconditions.map (fun frag =>
    s!"(assert {renderSmtBoolExpr frag.body})")

  -- 5. Negated output invariants as postcondition (guarded by presence for optional fields)
  --    For pass-through collections, rewrite "out-collKey" → "in-collKey" so the
  --    output invariant reuses input accessor functions (items didn't change).
  let postBodies := invFrags.map (fun frag =>
    let prefixed := prefixSmtBoolExpr "out-" frag.body
    let rewritten := if collRewrites.isEmpty then prefixed
                     else rewriteBoolCollections collRewrites prefixed
    let bodyStr := renderSmtBoolExpr rewritten
    guardOptionalBody "out-" optionalFields frag.consts bodyStr)
  let postcondition := match postBodies with
    | []  => ""
    | [b] => s!"(assert (not {b}))"
    | _   =>
      let conjoined := "\n    ".intercalate postBodies
      s!"(assert (not (and\n    {conjoined})))"

  -- Assemble
  let sections := [header]
    ++ [""]
    ++ ["; --- Constants ---"]
    ++ constDecls
    ++ (if sumDecls.isEmpty then []
        else ["", "; --- Collection definitions ---"] ++ sumDecls)
    ++ [""]
    ++ ["; --- Unchanged fields ---"]
    ++ unchangedAsserts
    ++ [""]
    ++ (if presenceAsserts.isEmpty then []
        else ["; --- Presence constraints (optional fields) ---"]
             ++ presenceAsserts ++ [""])
    ++ ["; --- Function encoding ---"]
    ++ assignAsserts
    ++ [""]
    ++ ["; --- Preconditions (input invariants) ---"]
    ++ preconditions
    ++ (if paramPrecondAsserts.isEmpty then []
        else ["", "; --- Parameter preconditions (typed parameter invariants) ---"]
             ++ paramPrecondAsserts)
    ++ [""]
    ++ ["; --- Postcondition (negated output invariants) ---"]
    ++ [postcondition]
    ++ ["", "(check-sat)", "(get-model)"]
  "\n".intercalate sections
