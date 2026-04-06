/-
  Ephemaral — Compilation Pipeline
  Wires together parser → compiler → renderer into a single function.
  This is what Main.lean calls.
-/
import Proofs.Invariant.Parser
import Proofs.Invariant.Compile
import Proofs.Invariant.Render

/-- Full pipeline for a single invariant: parse + compile + render. -/
def compileToSmt (text : String) : Option String := do
  let inv ← parseInvariant text
  let frag := compile inv
  pure (renderSmt frag)

/-- Try to compile a single block. Returns Some fragment on success, None on skip. -/
def tryCompileBlock (text : String) : Option CompiledInvariant := do
  let inv ← parseInvariant text
  pure (compile inv)

/-- Diagnose why a block failed to parse. Inspects the body text for common issues.
    Returns a human-readable reason string. -/
def diagnoseSkipReason (block : String) : String :=
  let lines := cleanLines block
  if lines.length < 2 then "empty or malformed block"
  else
    let bodyLine := lines[1]!
    let tokens := tokenize bodyLine
    -- Check for parent field refs (root.field) inside sum/each body
    let hasCollectionKw := tokens.contains "sum" || tokens.contains "each"
    if hasCollectionKw then
      match tokens.findIdx? (· == ",") with
      | some commaIdx =>
        let bodyTokens := tokens.drop (commaIdx + 1)
        let dottedInBody := bodyTokens.filter (·.contains '.')
        match dottedInBody.head? with
        | some ref =>
          s!"collection body can only use item fields — found '{ref}' (parent field references inside sum/each are not yet supported)"
        | none => "not yet supported"
      | none => "not yet supported"
    else "not yet supported"

/-- Compile all parseable invariants from blocks into a joint SMT-LIB file. -/
def compileFileToSmt (blocks : List String) : Option String := do
  let frags := blocks.filterMap tryCompileBlock
  guard (!frags.isEmpty)
  pure (renderSmtFile frags)
