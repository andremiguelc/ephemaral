/-
  Ephemaral — Diagnostic Layer
  Parses Z3 output, classifies counterexamples, and formats actionable reports.

  Layer 2: interpretation code, not proved. Lives outside the proof boundary.
  Uses `partial` for parser functions (no termination proof needed).

  This module has NO imports from the compiler — it only knows about
  DiagnosticInput, a display-ready struct built by the pipeline.
-/

/-- A single variable assignment from Z3's model. -/
structure ModelEntry where
  name  : String
  value : String   -- raw Z3 value string (e.g., "0.0", "(/ 1.0 2.0)")
  deriving Repr

/-- Parsed Z3 output. -/
structure Z3Result where
  verdict : String              -- "sat", "unsat", "unknown"
  model   : List ModelEntry     -- populated only when sat
  deriving Repr

/-- Display-ready input for the diagnostic layer.
    Built by the pipeline from compiled structures + CLI data.
    All names are clean (no in-, out-, inv- prefixes). -/
structure DiagnosticInput where
  funName        : String                    -- function name
  inputType      : String                    -- the type being transformed
  inputFields    : List (String × String)    -- (field name, value)
  outputFields   : List (String × String)    -- (field name, value)
  params         : List (String × String)    -- (param name, value)
  assignedFields : List (String × String)    -- (field name, value) — fields the function computed
  ruleNames      : List String               -- original invariant names
  ruleComments   : List (String × String)    -- (name, comment) — from .aral file
  invSourceFiles : List (String × String) := [] -- (rule name, source basename) pairs
  -- Fields needed for classification
  paramNames     : List String               -- all parameter names
  usedInputFields: List String               -- input fields used in assignments
  constrainedFields : List String            -- fields that appear in any invariant
  constrainedParams : List String := []      -- params constrained by typed param invariants
  paramPrecondRules : List (String × String) := [] -- (param name, rule name) from typed param invariants
  deriving Repr

-- Z3 model parser

/-- Parse Z3 model entries from the output lines (after "sat").
    Z3 format (each define-fun is exactly 2 lines):
      (define-fun NAME () Real
        VALUE)
    where VALUE) has one trailing ) closing the define-fun.

    For simple values: "0.0)"
    For compound:     "(/ 1.0 2.0))" or "(- (/ 1.0 2.0)))"
    Partial: line-based recursion on Z3 output; bounded by input length but not proved.
    Outside proof boundary — display layer only, doesn't affect verdicts. -/
private partial def parseModelEntries (lines : List String) : List ModelEntry :=
  match lines with
  | [] => []
  | l :: rest =>
    let trimmed := l.trimAscii.toString
    -- Look for lines starting with "(define-fun"
    if trimmed.startsWith "(define-fun " then
      -- Extract name: everything between "define-fun " and " ()"
      let afterPrefix := (trimmed.drop "(define-fun ".length).trimAscii.toString
      let name := afterPrefix.takeWhile (· != ' ')
      -- Value is on the next line, with one trailing ) for the define-fun close
      match rest with
      | [] => []
      | valueLine :: rest' =>
        let rawValue := valueLine.trimAscii.toString
        -- Strip exactly one trailing ) — it closes the define-fun, not the value
        let value := if rawValue.endsWith ")" then
          stripOneClose rawValue
        else rawValue
        { name := name.toString, value := value } :: parseModelEntries rest'
    else
      parseModelEntries rest
where
  /-- Strip one trailing ')' that belongs to the define-fun wrapper.
      Uses paren counting: if closes > opens, strip one. -/
  stripOneClose (s : String) : String :=
    let chars := s.toList
    let opens := chars.filter (· == '(') |>.length
    let closes := chars.filter (· == ')') |>.length
    if closes > opens then
      let trimmed := s.dropEnd 1
      trimmed.toString.trimAscii.toString
    else
      s

/-- Parse complete Z3 output into a Z3Result. -/
def parseZ3Output (output : String) : Z3Result :=
  let lines := output.trimAscii.toString.splitOn "\n"
  match lines with
  | [] => { verdict := "empty", model := [] }
  | verdictLine :: rest =>
    let verdict := verdictLine.trimAscii.toString
    if verdict == "sat" then
      let entries := parseModelEntries rest
      { verdict := "sat", model := entries }
    else
      { verdict := verdict, model := [] }

-- Value prettifier

/-- Prettify a Z3 value for human display.
    "0.0" → "0"
    "(/ 1.0 2.0)" → "1/2"
    "(- (/ 1.0 2.0))" → "-1/2"
    "(- 5.0)" → "-5"
    Partial: string parsing with nested S-expressions; bounded by input length
    but not proved. Outside proof boundary — display layer only. -/
partial def prettifyValue (s : String) : String :=
  let s := s.trimAscii.toString
  -- Try to simplify common patterns
  -- Pattern: (- INNER)
  if s.startsWith "(- " && s.endsWith ")" then
    let inner := ((s.drop 3).dropEnd 1).toString.trimAscii.toString
    "-" ++ prettifyValue inner
  -- Pattern: (/ NUM.0 DEN.0)
  else if s.startsWith "(/ " && s.endsWith ")" then
    let inner := ((s.drop 3).dropEnd 1).toString.trimAscii.toString
    let parts := inner.splitOn " "
    match parts with
    | [num, den] => stripDotZero num ++ "/" ++ stripDotZero den
    | _ => s
  -- Pattern: NUM.0 (simple real)
  else
    stripDotZero s
where
  stripDotZero (v : String) : String :=
    let v := v.trimAscii.toString
    if v.endsWith ".0" then (v.dropEnd 2).toString else v

-- Source file lookup + rule formatting

/-- Look up source file for a rule name. -/
def lookupSourceFile (name : String) (input : DiagnosticInput) : String :=
  match input.invSourceFiles.find? (fun (n, _) => n == name) with
  | some (_, f) => f
  | none => ""

/-- Get comma-separated list of all unique source files. -/
def allSourceFiles (input : DiagnosticInput) : String :=
  let files := input.invSourceFiles.map (·.2) |>.eraseDups
  ", ".intercalate files

/-- Format a rule name with source file (ESLint-style). -/
def formatRule (name : String) (input : DiagnosticInput) : String :=
  let src := lookupSourceFile name input
  if src.isEmpty then s!"  {name}" else s!"  {name} ({src})"

-- Counterexample formatter

/-- Annotate presence flag values for human readability.
    "has-discount = 0" → "has-discount = 0 (discount was not provided)"
    "has-discount = 1" → "has-discount = 1 (discount was provided)" -/
private def annotatePresence (name : String) (value : String) : String :=
  if name.startsWith "has-" then
    let fieldName := (name.drop 4).toString
    if value == "0" then s!"{value} ({fieldName} was not provided)"
    else s!"{value} ({fieldName} was provided)"
  else value

/-- Format a list of (name, value) pairs as aligned lines. -/
private def formatFields (fields : List (String × String)) (indent : String) : String :=
  let lines := fields.map (fun (name, value) =>
    s!"{indent}{name} = {annotatePresence name value}")
  "\n".intercalate lines

/-- Format the counterexample section of the diagnostic report. -/
def formatCounterexample (input : DiagnosticInput) : String :=
  let sections := [
    "COUNTEREXAMPLE FOUND",
    "",
    s!"Function: {input.funName}",
    "This function can produce output that violates the rules below.",
    "Here are the concrete values that cause the violation:",
    "",
    "--- Values ---",
    "Input:"
  ]
  ++ [formatFields input.inputFields "  "]
  ++ ["Output:"]
  ++ [formatFields input.outputFields "  "]
  ++ (if input.params.isEmpty then [] else
    ["Parameters:"] ++ [formatFields input.params "  "])
  ++ ["", "Rules checked:"]
  ++ input.ruleNames.map (fun n => formatRule n input)
  "\n".intercalate sections

-- Classification

/-- Find unconstrained parameters — those not mentioned by any invariant
    and not constrained by typed parameter invariants. -/
def findUnconstrainedParams (input : DiagnosticInput) : List String :=
  input.paramNames.filter (fun p =>
    !input.constrainedFields.contains p && !input.constrainedParams.contains p)

/-- Find input fields used in assignments that have no dedicated invariant.
    Excludes presence keys (has-*) — these are infrastructure for optional fields,
    not business fields that need independent invariants. -/
def findUncoveredInputFields (input : DiagnosticInput) : List String :=
  input.usedInputFields.filter (fun f =>
    !input.constrainedFields.contains f && !f.startsWith "has-")

/-- Look up a field's value from the params or fields lists. -/
def lookupValue (name : String) (input : DiagnosticInput) : String :=
  match input.params.find? (fun (n, _) => n == name) with
  | some (_, v) => v
  | none =>
    match input.inputFields.find? (fun (n, _) => n == name) with
    | some (_, v) => v
    | none => "unknown"

/-- Look up a comment for a rule name. -/
def lookupComment (name : String) (input : DiagnosticInput) : Option String :=
  match input.ruleComments.find? (fun (n, _) => n == name) with
  | some (_, c) => if c.isEmpty then none else some c
  | none => none

/-- Generate the diagnosis and fix suggestions section.
    Classification priority:
    1. Unconstrained parameters (most common, easiest to fix)
    2. Invariant gap (field used in computation has no invariant)
    3. Rule conflict (everything is constrained, function logic conflicts with rules) -/
def formatDiagnosis (input : DiagnosticInput) : String :=
  let root := if input.inputType.isEmpty then "input" else input.inputType.toLower
  let unconstrainedParams := findUnconstrainedParams input
  let uncoveredFields := findUncoveredInputFields input
  -- Priority 1: unconstrained parameters
  if !unconstrainedParams.isEmpty then
    let paramLines := unconstrainedParams.map (fun p =>
      s!"  '{p}' was {lookupValue p input} — no rule constrains this parameter.")
    "\n".intercalate ([
      "--- Diagnosis ---",
      "Category: UNCONSTRAINED_PARAMETER",
      s!"The function '{input.funName}' accepts parameters that have no rules limiting their values.",
      "Verification found values that are technically valid inputs but break the output rules."
    ] ++ paramLines ++ [
      "",
      "--- Suggested Fixes ---"
    ] ++ unconstrainedParams.map (fun p => "\n".intercalate [
      s!"For '{p}':",
      s!"  1. Add a guard in '{input.funName}': reject or clamp '{p}' before using it",
      s!"  2. Require the caller to validate '{p}' before passing it"
    ]))
  -- Priority 2: invariant gap
  else if !uncoveredFields.isEmpty then
    let fieldLines := uncoveredFields.map (fun f =>
      s!"  '{f}' was {lookupValue f input} — the function reads this field but no rule bounds it.")
    "\n".intercalate ([
      "--- Diagnosis ---",
      "Category: INVARIANT_GAP",
      s!"The function '{input.funName}' may be correct, but the rules are incomplete.",
      "Some input fields used in the computation have no rules limiting their values,",
      "so valid-looking inputs can produce outputs that break other rules."
    ] ++ fieldLines ++ [
      "",
      "--- Suggested Fixes ---"
    ] ++ uncoveredFields.map (fun f =>
      "\n".intercalate [
      s!"For '{f}':",
      s!"  1. Add a rule: {root}.{f} >= 0 and {root}.{f} <= <max value>",
      s!"  2. If '{f}' is computed from other fields, add a rule expressing that relationship"
    ]))
  -- Priority 3: rule conflict
  else
    let ruleList := input.ruleNames.map (fun n => formatRule n input)
    let assignLines := input.assignedFields.map (fun (field, value) =>
      s!"  '{field}' was set to {value}")
    let sourceFilesNote := let sf := allSourceFiles input
      if sf.isEmpty then ""
      else s!"  If these rules no longer reflect the business intent, update them in {sf}."
    -- Note which typed params were constrained by preconditions
    let paramConstraintNote := if input.paramPrecondRules.isEmpty then []
      else
        let grouped := input.constrainedParams.filterMap fun pn =>
          let rules := input.paramPrecondRules.filter (·.1 == pn) |>.map (·.2)
          if rules.isEmpty then none
          else some (s!"Even assuming '{pn}' satisfies:" ++ "\n" ++
            "\n".intercalate (rules.map fun rn => formatRule rn input))
        if grouped.isEmpty then [] else grouped ++ [""]
    "\n".intercalate ([
      "--- Diagnosis ---",
      "Category: RULE_CONFLICT"
    ] ++ paramConstraintNote ++ [
      s!"The function '{input.funName}' produces output that conflicts with these rules:"
    ] ++ ruleList ++ [
      "",
      "The function computed:"
    ] ++ assignLines ++ [
      "",
      "--- Suggested Fixes ---",
      s!"  1. Check the computation in '{input.funName}' — compare the input and output values above",
      s!"  2. Rewrite '{input.funName}' so the output satisfies the rules above",
      "  3. Re-run ephemaral on the function and invariants to verify the fix"
    ] ++ (if sourceFilesNote.isEmpty then [] else [sourceFilesNote]))

/-- Format a complete diagnostic report for a sat result. -/
def formatDiagnosticReport (input : DiagnosticInput) : String :=
  let counterexample := formatCounterexample input
  let diagnosis := formatDiagnosis input
  counterexample ++ "\n\n" ++ diagnosis

/-- Format the verified (unsat) result. -/
def formatVerified (input : DiagnosticInput) : String :=
  let ruleLines := input.ruleNames.map (fun n => formatRule n input)
  -- Note parameter assumptions when typed param preconditions were applied
  let paramAssumptions := if input.paramPrecondRules.isEmpty then []
    else
      let paramsWithRules := input.constrainedParams.filterMap fun pn =>
        let rules := input.paramPrecondRules.filter (·.1 == pn) |>.map (·.2)
        if rules.isEmpty then none
        else some (s!"  '{pn}' constrained by:" ++ "\n" ++
          "\n".intercalate (rules.map fun rn => formatRule rn input))
      if paramsWithRules.isEmpty then []
      else ["", "Assuming valid parameters:"] ++ paramsWithRules
  "\n".intercalate ([
    "VERIFIED",
    "",
    s!"Function: {input.funName}",
    "No valid input can make this function break the rules below.",
    "",
    "Rules checked:"
  ] ++ ruleLines ++ paramAssumptions)
