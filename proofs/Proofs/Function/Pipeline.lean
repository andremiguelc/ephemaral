/-
  Ephemaral — Function Verification Pipeline
  Wires together: function compiler + invariant compiler + renderer
  + Z3 invocation + diagnostics into a complete verification flow.

  Takes a FunctionRepr (from any source: JSON, parser, LLM) and
  invariant blocks. No language-specific imports.

  This is the ONLY module that knows about both compiler types
  (CompiledFunction, CompiledInvariant) and diagnostic types (DiagnosticInput).
  It translates between the two.
-/
import Proofs.Function.Types
import Proofs.Function.Compile
import Proofs.Function.Render
import Proofs.Function.Diagnostic
import Proofs.Invariant.Pipeline            -- Invariant compilation pipeline
import Proofs.Invariant.Parser              -- for extractRoot (type validation)

/-- Everything needed to diagnose a verification result. -/
structure VerificationContext where
  smt              : String           -- SMT-LIB text (fed to Z3)
  funFrag          : CompiledFunction   -- compiled function (has param names, field names)
  invFrags         : List CompiledInvariant -- which invariants were used (have names, field lists)
  funName          : String           -- function name for display
  inputType        : String           -- the type being transformed (for type-binding validation)
  constrainedParams : List String := []                  -- params constrained by typed param invariants
  paramPrecondRules : List (String × String) := []       -- (param name, rule name) pairs

/-- Extract the invariant root from a single block's body tokens.
    Returns the root prefix (e.g., "order" from "order.total >= 0"). -/
def extractBlockRoot (block : String) : Option String :=
  let lines := cleanLines block
  if lines.length ≥ 2 then
    let bodyLine := lines[1]!
    let tokens := tokenize bodyLine
    extractRoot tokens
  else none

/-- Extract the invariant root from the first parseable block in a list. -/
def extractInvariantRoot (blocks : List String) : Option String :=
  blocks.findSome? extractBlockRoot

/-- Check invariant root vs function input type. Returns a warning if mismatched. -/
def checkTypeBinding (funInputType : String) (invariantBlocks : List String)
    : Option String :=
  match extractInvariantRoot invariantBlocks with
  | some root =>
    if root.toLower == funInputType.toLower then none
    else some s!"Note: invariant root '{root}' doesn't match function type '{funInputType}'. Proceeding — fields will be matched by name."
  | none => none

/-- The single-step routing decision for one block.
    When a block's root matches BOTH inputType and a typed param type,
    route to BOTH lists (same-type params get invariant coverage too).
    Extracted for provability — the foldl in routeBlocks calls this. -/
def routeOneBlock (inputType : String) (paramTypes : List String)
    (acc : List String × List String × List String) (block : String)
    : List String × List String × List String :=
  let (inp, par, skip) := acc
  match extractBlockRoot block with
  | some root =>
    let isInput := root.toLower == inputType
    let isParam := paramTypes.any (· == root.toLower)
    if isInput && isParam then (inp ++ [block], par ++ [block], skip)
    else if isInput then (inp ++ [block], par, skip)
    else if isParam then (inp, par ++ [block], skip)
    else (inp ++ [block], par, skip ++ [root])
  | none => (inp ++ [block], par, skip)

def routeBlocks (funRepr : FunctionRepr) (blocks : List String)
    : (List String × List String × List String) :=
  let inputType := funRepr.inputType.toLower
  let paramTypes := funRepr.typedParams.map (·.type.toLower)
  blocks.foldl (routeOneBlock inputType paramTypes) ([], [], [])

-- Prefix stripping (compiler internals → display names)

/-- Strip "in-" or "out-" prefix from a field name. -/
private def stripFieldPrefix (s : String) : String :=
  if s.startsWith "in-" then (s.drop 3).toString
  else if s.startsWith "out-" then (s.drop 4).toString
  else s

/-- Convert an SMT-LIB invariant name back to the original .aral name.
    "inv-total-non-negative" → "total_non_negative" -/
private def stripInvName (s : String) : String :=
  let stripped := if s.startsWith "inv-" then (s.drop 4).toString else s
  stripped.map fun c => if c == '-' then '_' else c

-- DiagnosticInput builder (the translation layer)

/-- Collect all field names referenced in invariant fragments (bare names). -/
private def allConstrainedFields (invFrags : List CompiledInvariant) : List String :=
  (invFrags.foldl (fun acc frag => acc ++ frag.consts) []).eraseDups

mutual
  def collectSmtConsts : SmtExpr → List String
    | .lit _            => []
    | .const name       => [name]
    | .arith _ l r      => collectSmtConsts l ++ collectSmtConsts r
    | .condExpr c t e   => collectSmtBoolConsts c ++ collectSmtConsts t ++ collectSmtConsts e
    | .roundExpr _ e    => collectSmtConsts e
    | .sumExpr collKey body => [collKey ++ "-len"] ++ collectSmtConsts body
      -- Only collKey-len is a scalar constant. Item fields (collKey-field) are declared
      -- as accessor functions (Int → Real) by renderSumDef, not as scalar Real constants.

  def collectSmtBoolConsts : SmtBoolExpr → List String
    | .cmp _ l r   => collectSmtConsts l ++ collectSmtConsts r
    | .logic _ l r => collectSmtBoolConsts l ++ collectSmtBoolConsts r
    | .neg b       => collectSmtBoolConsts b
    | .eachExpr collKey body => [collKey ++ "-len"] ++ collectSmtBoolConsts body
end

/-- Collect input field names used in assignment expressions. -/
private def usedInputFieldNames (funFrag : CompiledFunction) : List String :=
  funFrag.assignDefs.foldl (fun acc (_, expr) =>
    acc ++ collectSmtConsts expr) []
    |>.filter (·.startsWith "in-")
    |>.map stripFieldPrefix
    |>.eraseDups

/-- Build a DiagnosticInput from compiled structures + Z3 result + CLI data.
    This is the ONLY function that reads from compiler types and produces
    display-ready data for the diagnostic layer. -/
def buildDiagnosticInput (z3result : Z3Result) (ctx : VerificationContext)
    (invComments : List (String × String) := [])
    (invSourceFiles : List (String × String) := []) : DiagnosticInput :=
  let funFrag := ctx.funFrag
  let invFrags := ctx.invFrags
  -- Look up a Z3 model value by constant name
  let modelVal (name : String) : String :=
    match z3result.model.find? (fun e => e.name == name) with
    | some e => prettifyValue e.value
    | none => "unknown"
  -- Build field lists with clean names and prettified values
  let inputFields := funFrag.inConsts.map fun c =>
    (stripFieldPrefix c, modelVal c)
  let outputFields := funFrag.outConsts.map fun c =>
    (stripFieldPrefix c, modelVal c)
  let params := funFrag.paramConsts.map fun c =>
    (c, modelVal c)  -- params have no prefix
  let assignedFields := funFrag.assignDefs.map fun (outConst, _) =>
    (stripFieldPrefix outConst, modelVal outConst)
  let ruleNames := invFrags.map fun frag => stripInvName frag.invName
  { funName        := ctx.funName
  , inputType      := ctx.inputType
  , inputFields
  , outputFields
  , params
  , assignedFields
  , ruleNames
  , ruleComments   := invComments
  , invSourceFiles
  , paramNames     := funFrag.paramConsts
  , usedInputFields := usedInputFieldNames funFrag
  , constrainedFields := allConstrainedFields invFrags
  , constrainedParams := ctx.constrainedParams
  , paramPrecondRules := ctx.paramPrecondRules
  }

/-- Find the object-param prefix for a fragment, if any typed param's prefixed fields
    match the function's parameter constants. Returns the prefix (e.g., "scaledAmount-"). -/
private def findObjectParamPrefix (typedParams : List TypedParam) (params : List String)
    (frag : CompiledInvariant) : Option String :=
  typedParams.findSome? fun tp =>
    let pfx := tp.name ++ "-"
    if frag.consts.any (fun c => params.contains (pfx ++ c)) then some pfx
    else none

/-- Resolve parameter preconditions: scalar (no prefix) or object (prefixed).
    Scalar: invariant field name IS a param name → use as-is.
    Object: invariant field prefixed with "{paramName}-" matches a param → rewrite with prefix. -/
def resolveParamPreconditions (funRepr : FunctionRepr) (frags : List CompiledInvariant)
    : List CompiledInvariant :=
  frags.filterMap fun frag =>
    -- Scalar match: any invariant field directly in params
    if frag.consts.any (funRepr.params.contains ·) then some frag
    -- Object match: find a typed param prefix that maps fields to param constants
    else match findObjectParamPrefix funRepr.typedParams funRepr.params frag with
      | some pfx =>
        some { frag with
          body := prefixSmtBoolExpr pfx frag.body
          consts := frag.consts.map (pfx ++ ·) }
      | none => none

/-- Extract invariant names + skip reasons from blocks that failed to compile. -/
private def extractSkippedInfo (blocks : List String) : List (String × String) :=
  blocks.filter (fun b => (tryCompileBlock b).isNone)
    |>.filterMap fun block =>
      let lines := cleanLines block
      match lines.head? with
      | some l =>
        if l.startsWith "invariant " then
          let afterPrefix := (l.drop 10).trimAscii.toString
          if afterPrefix.endsWith ":" then
            some ((afterPrefix.dropEnd 1).toString, diagnoseSkipReason block)
          else none
        else none
      | none => none

-- Pure pipeline helpers (extracted for provability)

/-- Augment inputFields with invariant-bearing fields for pass-through verification.
    Only adds fields that are NOT already in inputFields or params.
    This ensures the spread guarantee (out-x = in-x) holds for invariant-checked fields. -/
def augmentFields (inputFields params invConsts : List String) : List String :=
  let missing := invConsts.filter fun c =>
    !inputFields.contains c && !params.contains c
  inputFields ++ missing

/-- Check that inputFields and params have no overlapping names.
    Returns the overlapping names if any exist. -/
def findOverlap (inputFields params : List String) : List String :=
  inputFields.filter params.contains

/-- Compile pipeline: FunctionRepr + invariant blocks → VerificationContext.
    Pure computation, no IO. Accepts a FunctionRepr from any source
    (JSON deserialization, parser, hand-constructed).
    Routes blocks by type: input-type → pre+post, typed-param-type → preconditions only. -/
def verifyFunction (funRepr : FunctionRepr) (invariantBlocks : List String)
    : Except String (VerificationContext × Option String) := do
  -- Validate: no name appears in both inputFields and params.
  -- If it does, the compiler silently shadows the param (inputField wins).
  let overlap := findOverlap funRepr.inputFields funRepr.params
  if !overlap.isEmpty then
    throw s!"Name collision: {overlap} appear in both inputFields and params. Use distinct names — the compiler resolves shared names as input fields, making the parameter inaccessible."

  -- Route blocks by type matching
  let (inputBlocks, paramBlocks, skippedRoots) := routeBlocks funRepr invariantBlocks

  -- Type-binding validation for input blocks (warning, not error)
  let typeWarning := checkTypeBinding funRepr.inputType inputBlocks

  -- Compile input-type invariants (pre + post, as before)
  let invFrags := inputBlocks.filterMap tryCompileBlock

  -- Compile parameter precondition invariants
  let paramPrecondFrags := paramBlocks.filterMap tryCompileBlock

  -- Augment inputFields with presence keys for optional fields.
  -- Each optional field "f" adds "has-f" to the field list so that
  -- the compiler generates in-has-f / out-has-f constants automatically.
  let presenceKeys := funRepr.optionalFields.map ("has-" ++ ·)
  let funRepr := if presenceKeys.isEmpty then funRepr
    else { funRepr with inputFields := funRepr.inputFields ++ presenceKeys }

  -- Augment inputFields with invariant-bearing fields for pass-through verification.
  let invConsts := invFrags.foldl (fun acc frag => acc ++ frag.consts) [] |>.eraseDups
  let funRepr := { funRepr with
    inputFields := augmentFields funRepr.inputFields funRepr.params invConsts }

  -- Detect skipped invariants (unsupported syntax) with specific reasons
  let allSkippedInfo := extractSkippedInfo inputBlocks ++ extractSkippedInfo paramBlocks
  let skipWarning := if allSkippedInfo.isEmpty then none
    else
      let lines := allSkippedInfo.map fun (name, reason) => s!"  {name}: {reason}"
      some (s!"Skipped {allSkippedInfo.length} invariant(s) with unsupported syntax:\n" ++
        "\n".intercalate lines)

  -- Route warning for unmatched roots
  let routeWarning := if skippedRoots.isEmpty then none
    else some (s!"Skipped invariant root(s) not matching input type or typed params: " ++
      ", ".intercalate skippedRoots.eraseDups)

  -- Merge all warnings
  let warnings := [typeWarning, skipWarning, routeWarning].filterMap id
  let combinedWarning := if warnings.isEmpty then none
    else some ("\n".intercalate warnings)

  -- Filter to invariants that reference fields this function touches
  let relevantFrags := invFrags.filter fun frag =>
    frag.consts.any fun c =>
      funRepr.inputFields.contains c || funRepr.assigns.any (·.fieldName == c)

  -- Pass-through: if no invariants matched by field overlap but the type
  -- binding matches, include all invariants — the function preserves
  -- invariant-bearing fields via spread (out-x = in-x).
  let relevantFrags := if relevantFrags.isEmpty && typeWarning.isNone then invFrags
                        else relevantFrags

  -- Filter and route parameter preconditions:
  --   Scalar params: invariant field name = param name (no prefix needed)
  --   Object params: invariant field prefixed with "{paramName}-" matches a param constant
  let relevantParamFrags := resolveParamPreconditions funRepr paramPrecondFrags

  if relevantFrags.isEmpty && relevantParamFrags.isEmpty then
    let hint := match combinedWarning with
      | some w => s!" ({w})"
      | none => ""
    throw s!"no compilable invariants found that reference fields touched by '{funRepr.name}'.{hint}"

  -- Layer 1: compile and render
  let funFrag := compileFun funRepr

  -- Warn about collections used in function body but not referenced by any rule
  let funBodyCollKeys := funFrag.assignDefs.flatMap (fun (_, expr) =>
    (collectSumExprs expr).map (·.collKey) ++ (collectEachExprs expr).map (·.collKey))
    |>.eraseDups
  let invCollKeys := (relevantFrags.flatMap fun frag =>
    let prefixed := prefixSmtBoolExpr "in-" frag.body
    (collectSumBoolExprs prefixed).map (·.collKey) ++
    (collectEachBoolExprs prefixed).map (·.collKey))
    |>.eraseDups
  let unreferencedColls := funBodyCollKeys.filter (fun c => !invCollKeys.contains c)
    |>.map (fun s => if s.startsWith "in-" then (s.drop 3).toString else s)
  let collWarning := if unreferencedColls.isEmpty then none
    else some (
      "Note: the function computes over " ++
      ", ".intercalate (unreferencedColls.map (s!"'{·}'")) ++
      " but no rule references " ++
      (if unreferencedColls.length == 1 then "this collection." else "these collections.") ++
      " Verification will check the function against the provided rules only.")
  let combinedWarning := match (combinedWarning, collWarning) with
    | (some w, some cw) => some (w ++ "\n" ++ cw)
    | (none, some cw) => some cw
    | (w, none) => w

  let smt := renderVerification funFrag relevantFrags funRepr.name relevantParamFrags funRepr.optionalFields
  -- Collect constrained param identifiers:
  --   Scalar: the param name itself (e.g., "discountAmount")
  --   Object: the typed param name (e.g., "scaledAmount") + compound consts
  let constrainedCompoundNames := relevantParamFrags.foldl (fun acc frag =>
    acc ++ frag.consts) [] |>.filter (fun c => funRepr.params.contains c) |>.eraseDups
  -- Also include the typed param names for display grouping
  let constrainedTypedNames := funRepr.typedParams.filter (fun tp =>
    constrainedCompoundNames.any (fun c => c == tp.name || c.startsWith (tp.name ++ "-"))
  ) |>.map (·.name)
  let constrainedParamNames := (constrainedCompoundNames ++ constrainedTypedNames).eraseDups
  -- Build (paramName, ruleName) pairs for diagnostic display
  let paramPrecondRulePairs := relevantParamFrags.foldl (fun acc frag =>
    let ruleName := stripInvName frag.invName
    -- Find which typed param this fragment belongs to (by const overlap)
    let paramName := funRepr.typedParams.findSome? fun tp =>
      -- Scalar: const directly in params and matches param name
      if frag.consts.any (· == tp.name) then some tp.name
      -- Object: consts are prefixed with "{paramName}-"
      else if frag.consts.any (fun c => c.startsWith (tp.name ++ "-")) then some tp.name
      else none
    match paramName with
    | some pn => acc ++ [(pn, ruleName)]
    | none => acc
  ) []
  let ctx : VerificationContext := {
    smt, funFrag, invFrags := relevantFrags,
    funName := funRepr.name, inputType := funRepr.inputType,
    constrainedParams := constrainedParamNames,
    paramPrecondRules := paramPrecondRulePairs }
  pure (ctx, combinedWarning)

/-- Full pipeline: compile → Z3 → diagnose. One command, one result.
    When `debug` is true, includes the generated SMT-LIB and raw Z3 output
    before the diagnostic — useful during development. -/
def verifyAndDiagnose (funRepr : FunctionRepr) (invariantBlocks : List String)
    (debug : Bool := false)
    (invComments : List (String × String) := [])
    (invSourceFiles : List (String × String) := []) : IO String := do
  -- Compile (returns context + optional warnings)
  let (ctx, warnings) ← IO.ofExcept (verifyFunction funRepr invariantBlocks)

  -- Write SMT-LIB to temp file and invoke Z3
  let tmpPath := "/tmp/ephemaral-verify.smt2"
  IO.FS.writeFile tmpPath ctx.smt
  let z3out ← IO.Process.output {
    cmd := "z3"
    args := #["-T:10", tmpPath]
  }

  -- Parse Z3 output
  let z3result := parseZ3Output z3out.stdout

  -- Build display-ready diagnostic input (translate compiler internals → clean names)
  let diagInput := buildDiagnosticInput z3result ctx invComments invSourceFiles

  -- Debug preamble (SMT-LIB + raw Z3 output)
  let debugSection := if debug then
    "\n".intercalate [
      "=== DEBUG: Generated SMT-LIB ===",
      ctx.smt,
      "",
      "=== DEBUG: Raw Z3 output ===",
      z3out.stdout.trimAscii.toString,
      "",
      "=== Diagnostic ===",
      ""
    ]
  else ""

  -- Diagnose
  let report ← match z3result.verdict with
  | "sat" =>
    pure (formatDiagnosticReport diagInput)
  | "unsat" =>
    pure (formatVerified diagInput)
  | "timeout" =>
    let debugHint := if debug then "" else " Run with --debug for more detail."
    pure ("\n".intercalate [
      "INCOMPLETE VERIFICATION",
      "",
      s!"Function: {ctx.funName}",
      "",
      "Verification could not complete within the time limit. This typically happens when",
      "per-item rules (each) and aggregate computations (sum) interact on the same",
      "collection — the verification engine needs to reason about every possible",
      "collection size simultaneously, which can exceed its capabilities.",
      "",
      "--- What to do ---",
      "  1. If per-item and aggregate rules can stand alone, try splitting them",
      "     into separate .aral files and verifying each independently",
      "  2. If the rules genuinely need to be together (the aggregate depends on",
      "     per-item constraints), this is a current limitation — the engine",
      "     cannot yet prove properties that require relating per-item guarantees",
      "     to aggregate outcomes",
      s!"  3. If the problem persists, run with --debug and report the issue{debugHint}"
    ])
  | _other =>
    let debugHint := if debug then "" else " Run with --debug for more detail."
    pure ("\n".intercalate [
      "INCOMPLETE VERIFICATION",
      "",
      s!"Function: {ctx.funName}",
      s!"Verification could not be completed for this function and rules combination.{debugHint}",
      "",
      "--- What to do ---",
      "  1. Check that field names in your rules match the function's input fields",
      "  2. Try simplifying — split collection rules (sum, each) into separate .aral files",
      "  3. If the problem persists, run with --debug and report the issue"
    ])
  let warningSection := match warnings with
    | some w => w ++ "\n\n"
    | none => ""
  pure (warningSection ++ debugSection ++ report)
