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

/-- Compile all parseable invariants from blocks into a joint SMT-LIB file. -/
def compileFileToSmt (blocks : List String) : Option String := do
  let frags := blocks.filterMap tryCompileBlock
  guard (!frags.isEmpty)
  pure (renderSmtFile frags)
