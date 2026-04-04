/-
  Ephemaral — Parser
  Reads DSL text into Invariant structures.
-/
import Proofs.Types

/-- Try to parse a CompOp from a string token. -/
def parseOp (s : String) : Option CompOp :=
  match s with
  | "==" => some .eq
  | "!=" => some .neq
  | ">"  => some .gt
  | "<"  => some .lt
  | ">=" => some .gte
  | "<=" => some .lte
  | _    => none

/-- List of comparison operator strings, used to find the operator in a token list. -/
def compOpTokens : List String := ["==", "!=", ">=", "<=", ">", "<"]

/-- Strip leading/trailing whitespace and filter out comment/blank lines. -/
def cleanLines (text : String) : List String :=
  text.splitOn "\n"
    |>.map (fun l => (l.trimAscii).toString)
    |>.filter fun l => !l.isEmpty && !l.startsWith "#"

/-- Tokenize a string by splitting on spaces, then further splitting on
    parentheses and commas as separate tokens. -/
def tokenize (s : String) : List String :=
  let spaceTokens := s.splitOn " " |>.filter (!·.isEmpty)
  spaceTokens.flatMap fun tok =>
    -- Split a single token around '(', ')', ',' preserving delimiters
    let rec split (chars : List Char) (acc : List String) (current : List Char) : List String :=
      match chars with
      | [] =>
        let cur := String.ofList current.reverse
        if cur.isEmpty then acc else acc ++ [cur]
      | c :: rest =>
        if c == '(' || c == ')' || c == ',' then
          let cur := String.ofList current.reverse
          let acc' := if cur.isEmpty then acc else acc ++ [cur]
          split rest (acc' ++ [String.ofList [c]]) []
        else
          split rest acc (c :: current)
    split tok.toList [] []

/-- Parse a single simple expression token (field reference or literal). -/
def parseSimpleExpr (token : String) (root : String) : Option Expr := do
  -- Try as integer literal first
  match token.toInt? with
  | some n => pure (.lit (n : Rat))
  | none =>
    -- Try as field reference: root.field
    let parts := token.splitOn "."
    guard (parts.length == 2)
    guard (parts[0]! == root)
    pure (.field (.simple parts[1]!))

/-- Parse a bare field name (no root prefix) as an item field reference.
    Used inside sum() for per-item expressions. -/
def parseItemExpr (token : String) : Option Expr := do
  match token.toInt? with
  | some n => pure (.lit (n : Rat))
  | none =>
    guard (!token.isEmpty)
    guard (!token.contains '.')
    pure (.field (.simple token))

/-- Find the rightmost operator at parenthesis depth 0.
    Skips operators inside parenthesized expressions (e.g., sum(...)).
    Right-to-left scan gives left-associativity. -/
def findRightmostOp (tokens : List String) (ops : List String) : Option Nat :=
  let len := tokens.length
  let rec go (i : Nat) (depth : Nat) (best : Option Nat) : Option Nat :=
    if i >= len then best
    else
      let tok := tokens[i]!
      let newDepth := if tok == "(" then depth + 1
                      else if tok == ")" then depth - 1
                      else depth
      let newBest := if depth == 0 && ops.contains tok then some i else best
      go (i + 1) newDepth newBest
  go 0 0 none

-- Parse an expression over item fields (bare names, no root prefix).
-- Recursive descent with operator precedence. Termination: every recursive
-- call is on a strictly shorter token sublist (via List.take / List.drop).
mutual
  def parseItemBodyExpr (tokens : List String) : Option Expr := do
    guard (!tokens.isEmpty)
    match findRightmostOp tokens ["+", "-"] with
    | some idx =>
      if _h_pos : idx > 0 then
        if h_bound : idx + 1 < tokens.length then
          let left ← parseItemBodyExpr (tokens.take idx)
          let right ← parseItemBodyTerm (tokens.drop (idx + 1))
          let op := if tokens[idx]! == "+" then ArithOp.add else ArithOp.sub
          pure (.arith op left right)
        else none
      else none
    | none => parseItemBodyTerm tokens
  termination_by tokens.length
  decreasing_by all_goals simp [List.length_take]; omega

  def parseItemBodyTerm (tokens : List String) : Option Expr := do
    match findRightmostOp tokens ["*", "/"] with
    | some idx =>
      if _h_pos : idx > 0 then
        if h_bound : idx + 1 < tokens.length then
          let left ← parseItemBodyTerm (tokens.take idx)
          let right ← parseItemExpr tokens[idx + 1]!
          let op := if tokens[idx]! == "*" then ArithOp.mul else ArithOp.div
          pure (.arith op left right)
        else none
      else none
    | none =>
      match tokens with
      | [t] => parseItemExpr t
      | _ => none
  termination_by tokens.length
  decreasing_by all_goals simp [List.length_take]; omega
end

/-- Parse a sum expression from tokens starting after "sum".
    Expects: "(" collection "," body-tokens ")"
    Returns the sumExpr and the number of tokens consumed (including sum). -/
def parseSumExpr (tokens : List String) (root : String) : Option (Expr × Nat) := do
  -- tokens[0] should be "("
  guard (tokens.length >= 5)  -- at minimum: ( coll , field )
  guard (tokens[0]! == "(")
  -- Find the comma
  let commaIdx ← tokens.findIdx? (· == ",")
  -- Find the closing paren
  let closeIdx ← tokens.findIdx? (· == ")")
  guard (closeIdx > commaIdx)
  -- Parse collection: tokens between ( and ,
  let collTokens := tokens.toArray[1:commaIdx].toArray.toList
  guard (collTokens.length == 1)
  let collStr := collTokens[0]!
  let collParts := collStr.splitOn "."
  guard (collParts.length == 2)
  guard (collParts[0]! == root)
  let collRef := FieldRef.simple collParts[1]!
  -- Parse body: tokens between , and )
  let bodyTokens := tokens.toArray[commaIdx + 1:closeIdx].toArray.toList
  guard (!bodyTokens.isEmpty)
  let body ← parseItemBodyExpr bodyTokens
  -- Tokens consumed: everything from "(" through ")" (caller handles "sum")
  pure (.sumExpr collRef body, closeIdx + 1)

-- Parse an expression with operator precedence (recursive descent).
-- Level 1 (lowest): + and -    Level 2: * and /    Level 3 (highest): atoms
-- Termination: every recursive call is on a strictly shorter token sublist.
mutual
  def parseExpr (tokens : List String) (root : String) : Option Expr := do
    guard (!tokens.isEmpty)
    -- If the entire expression is a standalone sum, return it directly.
    -- If sum appears inside arithmetic (e.g., sum(...) + tax), fall through
    -- to the arithmetic path which handles sum as an atom.
    if tokens[0]! == "sum" then
      if let some (sumE, consumed) := parseSumExpr (tokens.drop 1) root then
        if consumed == tokens.length - 1 then
          return sumE
        -- else: sum doesn't consume all tokens — fall through to arithmetic
    -- Level 1: scan for rightmost + or - (outside parens) → left-associative
    match findRightmostOp tokens ["+", "-"] with
    | some idx =>
      if _h_pos : idx > 0 then
        if h_bound : idx + 1 < tokens.length then
          let left ← parseExpr (tokens.take idx) root
          let right ← parseTerm (tokens.drop (idx + 1)) root
          let op := if tokens[idx]! == "+" then ArithOp.add else ArithOp.sub
          pure (.arith op left right)
        else none
      else none
    | none => parseTerm tokens root
  termination_by tokens.length
  decreasing_by all_goals simp [List.length_take]; omega

  /-- Level 2: * and / -/
  def parseTerm (tokens : List String) (root : String) : Option Expr := do
    match findRightmostOp tokens ["*", "/"] with
    | some idx =>
      if _h_pos : idx > 0 then
        if h_bound : idx + 1 < tokens.length then
          let left ← parseTerm (tokens.take idx) root
          let right ← parseSimpleExpr tokens[idx + 1]! root
          let op := if tokens[idx]! == "*" then ArithOp.mul else ArithOp.div
          pure (.arith op left right)
        else none
      else none
    | none =>
      match tokens with
      | [t] => parseSimpleExpr t root
      -- Handle sum(...) as an atom
      | "sum" :: rest =>
        let (sumE, _) ← parseSumExpr rest root
        pure sumE
      | _ => none
  termination_by tokens.length
  decreasing_by all_goals simp [List.length_take]; omega
end

/-- Find the index of the comparison operator in a token list. -/
def findCompOpIdx (tokens : List String) : Option Nat :=
  tokens.findIdx? fun t => compOpTokens.contains t

/-- Parse a single comparison from tokens: `<expr> <op> <expr>` → BoolExpr.cmp -/
def parseCmpExpr (tokens : List String) (root : String) : Option BoolExpr := do
  let opIdx ← findCompOpIdx tokens
  let op ← parseOp tokens[opIdx]!
  let lhsTokens := tokens.take opIdx
  let rhsTokens := tokens.drop (opIdx + 1)
  let lhs ← parseExpr lhsTokens root
  let rhs ← parseExpr rhsTokens root
  pure (.cmp op lhs rhs)

/-- Find the index of a comparison operator in item-scoped tokens. -/
def findItemCompOpIdx (tokens : List String) : Option Nat :=
  tokens.findIdx? fun t => compOpTokens.contains t

/-- Parse a comparison over item fields (bare names, no root prefix). -/
def parseItemCmpExpr (tokens : List String) : Option BoolExpr := do
  let opIdx ← findItemCompOpIdx tokens
  let op ← parseOp tokens[opIdx]!
  let lhs ← parseItemBodyExpr (tokens.take opIdx)
  let rhs ← parseItemBodyExpr (tokens.drop (opIdx + 1))
  pure (.cmp op lhs rhs)

/-- Parse a boolean expression over item fields.
    Splits on `and`/`or` connectives, then parses each half as a comparison.
    Item fields are bare names (no root prefix). -/
partial def parseItemBoolExpr (tokens : List String) : Option BoolExpr := do
  match tokens.findIdx? (· == "and") with
  | some idx =>
    let left ← parseItemCmpExpr (tokens.take idx)
    let right ← parseItemBoolExpr (tokens.drop (idx + 1))
    pure (.logic .and left right)
  | none =>
    match tokens.findIdx? (· == "or") with
    | some idx =>
      let left ← parseItemCmpExpr (tokens.take idx)
      let right ← parseItemBoolExpr (tokens.drop (idx + 1))
      pure (.logic .or left right)
    | none => parseItemCmpExpr tokens

/-- Parse an each expression from tokens starting after "each".
    Expects: "(" collection "," body-bool-tokens ")"
    Returns the eachExpr BoolExpr. -/
def parseEachExpr (tokens : List String) (root : String) : Option BoolExpr := do
  guard (tokens.length >= 5)
  guard (tokens[0]! == "(")
  let commaIdx ← tokens.findIdx? (· == ",")
  -- Find matching close paren (last ")" at depth 0)
  let closeIdx ← tokens.findIdx? (· == ")")
  guard (closeIdx > commaIdx)
  let collTokens := tokens.toArray[1:commaIdx].toArray.toList
  guard (collTokens.length == 1)
  let collStr := collTokens[0]!
  let collParts := collStr.splitOn "."
  guard (collParts.length == 2)
  guard (collParts[0]! == root)
  let collRef := FieldRef.simple collParts[1]!
  let bodyTokens := tokens.toArray[commaIdx + 1:closeIdx].toArray.toList
  guard (!bodyTokens.isEmpty)
  let body ← parseItemBoolExpr bodyTokens
  pure (.eachExpr collRef body)

/-- Parse a boolean expression from tokens.
    Checks for `each` first (must be before and/or splitting since each body can contain and/or),
    then splits on `and` / `or` (lowest precedence), then parses each half as a comparison. -/
def parseBoolExpr (tokens : List String) (root : String) : Option BoolExpr := do
  -- Check for each(...) — must come before and/or splitting
  if tokens[0]! == "each" then
    if let some eachE := parseEachExpr (tokens.drop 1) root then
      return eachE
  match tokens.findIdx? (· == "and") with
  | some idx =>
    let left ← parseCmpExpr (tokens.take idx) root
    let right ← parseCmpExpr (tokens.drop (idx + 1)) root
    pure (.logic .and left right)
  | none =>
    match tokens.findIdx? (· == "or") with
    | some idx =>
      let left ← parseCmpExpr (tokens.take idx) root
      let right ← parseCmpExpr (tokens.drop (idx + 1)) root
      pure (.logic .or left right)
    | none => parseCmpExpr tokens root

/-- Extract root object from first field reference in tokens. -/
def extractRoot (tokens : List String) : Option String := do
  let firstFieldRef ← tokens.find? fun t => t.contains '.'
  let parts := firstFieldRef.splitOn "."
  guard (parts.length == 2)
  pure parts[0]!

/-- Parse an invariant from DSL text.
    Expected format (after stripping comments):
      Line 1: "invariant <name>:"
      Line 2: "<expr> <op> <expr>" or "<cmp> and/or <cmp>"
    Where <expr> is a field ref, literal, or simple arithmetic (a * b). -/
def parseInvariant (text : String) : Option Invariant := do
  let lines := cleanLines text
  guard (lines.length == 2)

  -- Parse declaration line: "invariant <name>:"
  let declLine := lines[0]!
  guard (declLine.startsWith "invariant ")
  let afterInvariant := (declLine.drop 10).trimAscii.toString
  guard (afterInvariant.endsWith ":")
  let name := (afterInvariant.dropEnd 1).trimAscii.toString

  -- Parse body line (tokenize splits on parens/commas for function call syntax)
  let bodyLine := lines[1]!
  let tokens := tokenize bodyLine

  let root ← extractRoot tokens
  let body ← parseBoolExpr tokens root

  pure { name, root, body }
