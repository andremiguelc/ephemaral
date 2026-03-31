/-
  Ephemaral — SMT-LIB Renderer
  Turns CompiledInvariant structures into SMT-LIB text strings.
-/
import Proofs.Types

/-- Render a CompOp as its SMT-LIB string. -/
def compOpToSmt (op : CompOp) : String :=
  match op with
  | .eq  => "="
  | .neq => "distinct"
  | .gt  => ">"
  | .lt  => "<"
  | .gte => ">="
  | .lte => "<="

/-- Format a Rat as an SMT-LIB Real literal.
    Integers (denominator 1) render as `42.0`.
    Proper fractions render as `(/ num.0 den.0)`. -/
def formatReal (n : Rat) : String :=
  if n.den == 1 then
    -- Integer value
    if n.num < 0 then
      s!"(- {Int.natAbs n.num}.0)"
    else
      s!"{n.num}.0"
  else
    -- Proper fraction: emit as SMT-LIB division
    let numStr := if n.num < 0 then s!"(- {Int.natAbs n.num}.0)" else s!"{n.num}.0"
    let denStr := s!"{n.den}.0"
    s!"(/ {numStr} {denStr})"

/-- Render an ArithOp as its SMT-LIB string. -/
def arithOpToSmt (op : ArithOp) : String :=
  match op with
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .div => "/"

/-- Render a LogicOp as its SMT-LIB string. -/
def logicOpToSmt (op : LogicOp) : String :=
  match op with
  | .and => "and"
  | .or  => "or"

mutual
  /-- Render an SmtExpr as SMT-LIB text. -/
  def renderSmtExpr : SmtExpr → String
    | .lit n           => formatReal n
    | .const name      => name
    | .arith op l r    =>
      let lStr := renderSmtExpr l
      let rStr := renderSmtExpr r
      match op with
      | .div => s!"(ite (= {rStr} 0.0) 0.0 (/ {lStr} {rStr}))"
      | _    => s!"({arithOpToSmt op} {lStr} {rStr})"
    | .condExpr c t e   => s!"(ite {renderSmtBoolExpr c} {renderSmtExpr t} {renderSmtExpr e})"
    | .roundExpr mode e =>
      let eStr := renderSmtExpr e
      match mode with
      | .floor  => s!"(to_real (to_int {eStr}))"
      | .ceil   => s!"(ite (= (to_real (to_int {eStr})) {eStr}) (to_real (to_int {eStr})) (to_real (+ (to_int {eStr}) 1)))"
      | .halfUp => s!"(to_real (to_int (+ {eStr} (/ 1.0 2.0))))"
    | .sumExpr collKey _body =>
      -- Rendered as a call to the recursive sum function.
      -- The define-fun-rec definition is emitted separately by collectSumExprs + renderSumDef.
      let fnName := "sum-" ++ collKey
      let lenConst := collKey ++ "-len"
      s!"({fnName} {lenConst})"

  /-- Render an SmtBoolExpr as SMT-LIB text. -/
  def renderSmtBoolExpr : SmtBoolExpr → String
    | .cmp op l r =>
      let lhs := renderSmtExpr l
      let rhs := renderSmtExpr r
      match op with
      | .neq => s!"(not (= {lhs} {rhs}))"
      | op   => s!"({compOpToSmt op} {lhs} {rhs})"
    | .logic op l r =>
      s!"({logicOpToSmt op} {renderSmtBoolExpr l} {renderSmtBoolExpr r})"
    | .neg b =>
      s!"(not {renderSmtBoolExpr b})"
end

-- Collection rendering support

mutual
  def renderSmtExprIndexed (collKey : String) (idxVar : String) : SmtExpr → String
    | .lit n           => formatReal n
    | .const name      => s!"({collKey}-{name} (- {idxVar} 1))"
    | .arith op l r    =>
      let lStr := renderSmtExprIndexed collKey idxVar l
      let rStr := renderSmtExprIndexed collKey idxVar r
      match op with
      | .div => s!"(ite (= {rStr} 0.0) 0.0 (/ {lStr} {rStr}))"
      | _    => s!"({arithOpToSmt op} {lStr} {rStr})"
    | .condExpr c t e   =>
      s!"(ite {renderSmtBoolExprIndexed collKey idxVar c} {renderSmtExprIndexed collKey idxVar t} {renderSmtExprIndexed collKey idxVar e})"
    | .roundExpr mode e =>
      let eStr := renderSmtExprIndexed collKey idxVar e
      match mode with
      | .floor  => s!"(to_real (to_int {eStr}))"
      | .ceil   => s!"(ite (= (to_real (to_int {eStr})) {eStr}) (to_real (to_int {eStr})) (to_real (+ (to_int {eStr}) 1)))"
      | .halfUp => s!"(to_real (to_int (+ {eStr} (/ 1.0 2.0))))"
    | .sumExpr nestedCollKey _body =>
      -- Nested sum in accessor — just emit the call
      s!"(sum-{nestedCollKey} {nestedCollKey}-len)"

  def renderSmtBoolExprIndexed (collKey : String) (idxVar : String) : SmtBoolExpr → String
    | .cmp op l r =>
      let lhs := renderSmtExprIndexed collKey idxVar l
      let rhs := renderSmtExprIndexed collKey idxVar r
      match op with
      | .neq => s!"(not (= {lhs} {rhs}))"
      | op   => s!"({compOpToSmt op} {lhs} {rhs})"
    | .logic op l r =>
      s!"({logicOpToSmt op} {renderSmtBoolExprIndexed collKey idxVar l} {renderSmtBoolExprIndexed collKey idxVar r})"
    | .neg b =>
      s!"(not {renderSmtBoolExprIndexed collKey idxVar b})"
end

/-- A sum definition extracted from an SmtExpr tree. -/
structure SumDef where
  collKey : String
  body    : SmtExpr
  deriving Repr

mutual
  /-- Collect all sumExpr nodes from an SmtExpr. -/
  def collectSumExprs : SmtExpr → List SumDef
    | .lit _            => []
    | .const _          => []
    | .arith _ l r      => collectSumExprs l ++ collectSumExprs r
    | .condExpr c t e   => collectSumBoolExprs c ++ collectSumExprs t ++ collectSumExprs e
    | .roundExpr _ e    => collectSumExprs e
    | .sumExpr collKey body => [⟨collKey, body⟩] ++ collectSumExprs body

  /-- Collect all sumExpr nodes from an SmtBoolExpr. -/
  def collectSumBoolExprs : SmtBoolExpr → List SumDef
    | .cmp _ l r   => collectSumExprs l ++ collectSumExprs r
    | .logic _ l r => collectSumBoolExprs l ++ collectSumBoolExprs r
    | .neg b       => collectSumBoolExprs b
end

mutual
  def collectBodyConsts : SmtExpr → List String
    | .lit _            => []
    | .const name       => [name]
    | .arith _ l r      => collectBodyConsts l ++ collectBodyConsts r
    | .condExpr c t e   => collectBodyBoolConsts c ++ collectBodyConsts t ++ collectBodyConsts e
    | .roundExpr _ e    => collectBodyConsts e
    | .sumExpr _ body   => collectBodyConsts body

  def collectBodyBoolConsts : SmtBoolExpr → List String
    | .cmp _ l r   => collectBodyConsts l ++ collectBodyConsts r
    | .logic _ l r => collectBodyBoolConsts l ++ collectBodyBoolConsts r
    | .neg b       => collectBodyBoolConsts b
end

/-- Render a SumDef as SMT-LIB declarations + define-fun-rec. -/
def renderSumDef (sd : SumDef) : List String :=
  let fields := (collectBodyConsts sd.body).eraseDups
  let fnName := "sum-" ++ sd.collKey
  let idxVar := "i"
  -- declare-fun for each item accessor
  let accessorDecls := fields.map fun f =>
    s!"(declare-fun {sd.collKey}-{f} (Int) Real)"
  -- declare-const for collection length
  let lenDecl := s!"(declare-const {sd.collKey}-len Int)"
  let lenAssert := s!"(assert (>= {sd.collKey}-len 0))"
  -- the recursive function
  let bodyStr := renderSmtExprIndexed sd.collKey idxVar sd.body
  let recDef := s!"(define-fun-rec {fnName} (({idxVar} Int)) Real\n  (ite (<= {idxVar} 0) 0.0\n    (+ {bodyStr}\n       ({fnName} (- {idxVar} 1)))))"
  accessorDecls ++ [lenDecl, lenAssert, recDef]

/-- Render a single CompiledInvariant as SMT-LIB text (standalone). -/
def renderSmt (frag : CompiledInvariant) : String :=
  let constDecls := frag.consts.map (fun c => s!"(declare-const {c} Real)")
  let body := renderSmtBoolExpr frag.body
  let defFun := s!"(define-fun {frag.invName} () Bool\n  {body})"
  let header := s!"; Invariant: {frag.invName}"
  "\n".intercalate (header :: constDecls ++ [defFun])

/-- Sanitize an invariant name to a valid SMT-LIB identifier for :named. -/
def sanitizeName (name : String) : String :=
  name.map fun c => if c == '-' then '_' else c

/-- Render multiple CompiledInvariants as a single SMT-LIB file.
    All invariants are conjoined — asserted together for joint consistency checking.
    Uses named asserts for unsat core extraction when invariants conflict. -/
def renderSmtFile (frags : List CompiledInvariant) : String :=
  -- Collect sum definitions from all fragments (dedup by collKey to avoid duplicate accessors)
  let rawSumDefs := (frags.flatMap fun frag => collectSumBoolExprs frag.body)
  let sumDefs := rawSumDefs.foldl (fun acc sd =>
    if acc.any (·.collKey == sd.collKey) then acc else acc ++ [sd]) []
  -- Constants declared by sum defs (len + body fields) — exclude from regular decls
  let sumDeclaredConsts : List String := sumDefs.flatMap fun sd =>
    [sd.collKey ++ "-len"] ++ (collectBodyConsts sd.body).eraseDups.map (sd.collKey ++ "-" ++ ·)
  -- Collect and deduplicate all constants across fragments, excluding sum-declared ones
  let allConsts : List String := (frags.flatMap (·.consts)).eraseDups
  let scalarConsts := allConsts.filter fun c => !sumDeclaredConsts.contains c
  let constDecls := scalarConsts.map (fun c => s!"(declare-const {c} Real)")
  let sumDecls := sumDefs.flatMap renderSumDef
  -- Render each invariant as a define-fun
  let defFuns := frags.map fun frag =>
    let body := renderSmtBoolExpr frag.body
    s!"(define-fun {frag.invName} () Bool\n  {body})"
  -- Named asserts for each invariant
  let asserts := frags.map fun frag =>
    let label := sanitizeName frag.invName
    s!"(assert (! {frag.invName} :named {label}))"
  let header := "; Ephemaral — Joint invariant consistency check"
  let sections := [header]
    ++ [""]
    ++ constDecls
    ++ (if sumDecls.isEmpty then [] else [""] ++ sumDecls)
    ++ [""]
    ++ defFuns
    ++ [""]
    ++ asserts
    ++ ["", "(check-sat)"]
  "\n".intercalate sections
