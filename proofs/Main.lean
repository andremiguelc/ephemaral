/-
  Ephemaral — Verification CLI

  Two modes:
    ephemaral <function.aral-fn.json> <inv1.aral> [inv2.aral ...]   — verify function against invariants
    ephemaral [--debug] <function.aral-fn.json> <inv1.aral> [...]   — verify with SMT-LIB + Z3 output
    ephemaral <inv.aral> [inv2.aral ...]                            — compile invariants to SMT-LIB

  The function representation is language-agnostic JSON (Aral-fn format).
  Use an external parser (ts-to-ephemaral, etc.) to produce it.
  Multiple .aral files can be provided — each targets a type via its root prefix.
-/
import Proofs.Function.Pipeline
import Proofs.Function.Deserialize
import Proofs.Util

/-- Extract invariant name → comment mapping from raw blocks.
    Looks for "# comment" line before "invariant name:" line. -/
def extractComments (blocks : List String) : List (String × String) :=
  blocks.filterMap fun block =>
    let lines := block.splitOn "\n" |>.map (·.trimAscii.toString)
    let commentLines := lines.filter (·.startsWith "#")
    let declLine := lines.find? (·.startsWith "invariant ")
    match (commentLines.head?, declLine) with
    | (some commentLine, some decl) =>
      let comment := (commentLine.drop 1).trimAscii.toString
      let afterPrefix := (decl.drop 10).trimAscii.toString
      if afterPrefix.endsWith ":" then
        let name := (afterPrefix.dropEnd 1).trimAscii.toString
        some (name, comment)
      else none
    | _ => none

/-- Extract invariant name → source file mapping from raw blocks.
    Tags each rule name with the basename of its source .aral file. -/
def extractRuleSources (blocks : List String) (basename : String) : List (String × String) :=
  blocks.filterMap fun block =>
    let lines := block.splitOn "\n" |>.map (·.trimAscii.toString)
    let declLine := lines.find? (·.startsWith "invariant ")
    match declLine with
    | some decl =>
      let afterPrefix := (decl.drop 10).trimAscii.toString
      if afterPrefix.endsWith ":" then
        some ((afterPrefix.dropEnd 1).trimAscii.toString, basename)
      else none
    | none => none

/-- Read and merge blocks + comments + source file mapping from multiple .aral files. -/
def readInvariantFiles (invPaths : List String)
    : IO (List String × List (String × String) × List (String × String)) := do
  let mut allBlocks : List String := []
  let mut allComments : List (String × String) := []
  let mut allSourceFiles : List (String × String) := []
  for path in invPaths do
    let invText ← IO.FS.readFile path
    let blocks := splitBlocks invText
    let comments := extractComments blocks
    let basename := System.FilePath.fileName ⟨path⟩ |>.getD path
    let sources := extractRuleSources blocks basename
    allBlocks := allBlocks ++ blocks
    allComments := allComments ++ comments
    allSourceFiles := allSourceFiles ++ sources
  return (allBlocks, allComments, allSourceFiles)

def runVerify (fnPath : String) (invPaths : List String) (debug : Bool) : IO Unit := do
  -- Read and parse the Aral-fn JSON
  let fnResult ← readAralFn fnPath
  let funRepr ← match fnResult with
    | .ok r => pure r
    | .error e =>
      IO.eprintln s!"Error reading {fnPath}: {e}"
      IO.Process.exit 1
  -- Read all invariant files
  let (blocks, comments, invSourceFiles) ← readInvariantFiles invPaths
  -- Verify
  try
    let report ← verifyAndDiagnose funRepr blocks debug comments invSourceFiles
    IO.println report
  catch e =>
    IO.eprintln s!"Error: {e}"
    IO.Process.exit 1

/-- Compile-only mode: read .aral files and emit SMT-LIB to stdout. -/
def runCompile (aralPaths : List String) : IO Unit := do
  let mut allBlocks : List String := []
  for path in aralPaths do
    let text ← IO.FS.readFile path
    let blocks := splitBlocks text
    -- Report skipped invariants with specific diagnostics
    let skipped := blocks.filter fun block => (tryCompileBlock block).isNone
    for block in skipped do
      let name := block.splitOn "\n"
        |>.map (fun l => l.trimAscii.toString)
        |>.filter (·.startsWith "invariant ")
        |>.head?
        |>.map (fun s => ((s.drop 10).trimAscii.toString.dropEnd 1).toString)
        |>.getD "unknown"
      let reason := diagnoseSkipReason block
      IO.eprintln s!"; [skipped] {name} — {reason}"
    allBlocks := allBlocks ++ blocks
  match compileFileToSmt allBlocks with
  | some smt => IO.println smt
  | none => IO.eprintln "Error: no invariants could be compiled"

/-- Check if a path looks like an Aral-fn JSON file. -/
def isAralFnJson (path : String) : Bool :=
  path.endsWith ".aral-fn.json"

def printUsage : IO Unit :=
  IO.eprintln "Usage: ephemaral [--debug] <function.aral-fn.json> <inv1.aral> [inv2.aral ...]\n       ephemaral <inv.aral> [inv2.aral ...]"

def ephemaralVersion : String := "0.1.4"

def main (args : List String) : IO Unit := do
  -- Version flag
  if args.any (· ∈ ["--version", "--ver", "-v"]) then
    IO.println s!"ephemaral {ephemaralVersion}"
    return
  match args with
  | [] =>
    printUsage
    IO.Process.exit 1
  | allArgs =>
    -- Strip --debug flag
    let debug := allArgs.contains "--debug"
    let paths := allArgs.filter (· != "--debug")
    if paths.isEmpty then
      printUsage
      IO.Process.exit 1
    -- Detect mode: if any path is .aral-fn.json, it's verify mode
    let fnPaths := paths.filter isAralFnJson
    let aralPaths := paths.filter (!isAralFnJson ·)
    if fnPaths.isEmpty then
      -- Compile-only mode: all args are .aral files
      runCompile paths
    else
      match fnPaths with
      | [fnPath] =>
        if aralPaths.isEmpty then
          IO.eprintln "Error: verify mode requires at least one .aral file"
          printUsage
          IO.Process.exit 1
        runVerify fnPath aralPaths debug
      | _ =>
        IO.eprintln "Error: only one .aral-fn.json file can be provided"
        printUsage
        IO.Process.exit 1
