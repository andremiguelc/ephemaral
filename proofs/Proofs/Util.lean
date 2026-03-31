/-
  Ephemaral — Shared Utilities
  Small helpers used by the CLI entry point (FunMain.lean).
-/

/-- Split a file into invariant blocks (separated by blank lines). -/
def splitBlocks (text : String) : List String :=
  let lines := text.splitOn "\n"
  let rec go (acc : List String) (current : List String) : List String → List String
    | [] =>
      let block := ("\n".intercalate current.reverse).trimAscii.toString
      if block.isEmpty then acc.reverse else (block :: acc).reverse
    | l :: rest =>
      if l.trimAscii.toString.isEmpty && !current.isEmpty then
        let block := ("\n".intercalate current.reverse).trimAscii.toString
        go (block :: acc) [] rest
      else
        go acc (l :: current) rest
  go [] [] lines
