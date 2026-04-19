/-
  Ephemaral — Aral-fn JSON Deserialization
  Reads the public Aral-fn JSON format into FunctionRepr.
  This is the proof boundary entry point: untrusted JSON comes in,
  validated FunctionRepr comes out.

  Layer 1: language-agnostic. Any parser (TS, Python, LLM) can produce
  Aral-fn JSON. The proved compiler works on the resulting FunctionRepr.
-/
import Lean.Data.Json
import Proofs.Types
import Proofs.Function.Types

open Lean (Json FromJson ToJson)

/-- Parse an ArithOp from its JSON string representation. -/
instance : FromJson ArithOp where
  fromJson?
    | .str "add" => .ok .add
    | .str "sub" => .ok .sub
    | .str "mul" => .ok .mul
    | .str "div" => .ok .div
    | j => .error s!"expected ArithOp (\"add\", \"sub\", \"mul\", \"div\"), got {j}"

/-- Parse a CompOp from its JSON string representation. -/
instance : FromJson CompOp where
  fromJson?
    | .str "eq"  => .ok .eq
    | .str "neq" => .ok .neq
    | .str "gt"  => .ok .gt
    | .str "lt"  => .ok .lt
    | .str "gte" => .ok .gte
    | .str "lte" => .ok .lte
    | j => .error s!"expected CompOp (\"eq\", \"neq\", \"gt\", \"lt\", \"gte\", \"lte\"), got {j}"

/-- Parse a RoundingMode from its JSON string representation. -/
instance : FromJson RoundingMode where
  fromJson?
    | .str "floor"   => .ok .floor
    | .str "ceil"    => .ok .ceil
    | .str "half_up" => .ok .halfUp
    | j => .error s!"expected RoundingMode (\"floor\", \"ceil\", \"half_up\"), got {j}"

/-- Parse a LogicOp from its JSON string representation. -/
instance : FromJson LogicOp where
  fromJson?
    | .str "and" => .ok .and
    | .str "or"  => .ok .or
    | j => .error s!"expected LogicOp (\"and\", \"or\"), got {j}"

mutual
  /-- Parse an Expr from JSON.
      Variants:
      - `{"lit": 42}` → Expr.lit 42
      - `{"field": {"name": "total"}}` → Expr.field (.simple "total")
      - `{"field": {"qualifier": "discount", "name": "percent"}}` → Expr.field (.qualified ...)
      - `{"arith": {"op": "sub", "left": ..., "right": ...}}` → Expr.arith ...
      - `{"ite": {"cond": <BoolExpr>, "then": <Expr>, "else": <Expr>}}` → Expr.condExpr ...
      Partial: mutual recursion on JSON depth; terminates on well-formed input
      but not proved. Outside proof boundary — JSON is the inspectable contract. -/
  partial def exprFromJson (j : Json) : Except String Expr :=
    -- Try lit
    match j.getObjValAs? Int "lit" with
    | .ok n => .ok (.lit (n : Rat))
    | .error _ =>
    -- Try field (structured FieldRef)
    match j.getObjVal? "field" with
    | .ok fieldVal =>
      match fieldVal.getObjValAs? String "name" with
      | .ok name =>
        match fieldVal.getObjValAs? String "qualifier" with
        | .ok qual => .ok (.field (.qualified qual name))
        | .error _ => .ok (.field (.simple name))
      | .error _ => .error s!"field object must have a \"name\" key, got {fieldVal}"
    | .error _ =>
    -- Try arith
    match j.getObjVal? "arith" with
    | .ok arithObj => do
      let op ← arithObj.getObjValAs? ArithOp "op"
      let leftJson ← arithObj.getObjVal? "left"
      let left ← exprFromJson leftJson
      let rightJson ← arithObj.getObjVal? "right"
      let right ← exprFromJson rightJson
      return .arith op left right
    | .error _ =>
    -- Try ite (if-then-else)
    match j.getObjVal? "ite" with
    | .ok iteObj => do
      let condJson ← iteObj.getObjVal? "cond"
      let cond ← boolExprFromJson condJson
      let thenJson ← iteObj.getObjVal? "then"
      let thenB ← exprFromJson thenJson
      let elseJson ← iteObj.getObjVal? "else"
      let elseB ← exprFromJson elseJson
      return .condExpr cond thenB elseB
    | .error _ =>
    -- Try round
    match j.getObjVal? "round" with
    | .ok roundObj => do
      let mode ← roundObj.getObjValAs? RoundingMode "mode"
      let exprJson ← roundObj.getObjVal? "expr"
      let expr ← exprFromJson exprJson
      return .roundExpr mode expr
    | .error _ =>
    -- Try sum
    match j.getObjVal? "sum" with
    | .ok sumObj => do
      let collName ← sumObj.getObjValAs? String "collection"
      let bodyJson ← sumObj.getObjVal? "body"
      let body ← exprFromJson bodyJson
      return .sumExpr (.simple collName) body
    | .error _ =>
    .error s!"expected Expr (lit, field, arith, ite, round, or sum), got {j}"

  /-- Parse a BoolExpr from JSON.
      Variants:
      - `{"cmp": {"op": "gt", "left": <Expr>, "right": <Expr>}}` → BoolExpr.cmp ...
      - `{"logic": {"op": "and", "left": <BoolExpr>, "right": <BoolExpr>}}` → BoolExpr.logic ...
      - `{"not": <BoolExpr>}` → BoolExpr.neg ...
      Partial: mutual recursion on JSON depth; terminates on well-formed input
      but not proved. Outside proof boundary — JSON is the inspectable contract. -/
  partial def boolExprFromJson (j : Json) : Except String BoolExpr :=
    -- Try cmp
    match j.getObjVal? "cmp" with
    | .ok cmpObj => do
      let op ← cmpObj.getObjValAs? CompOp "op"
      let leftJson ← cmpObj.getObjVal? "left"
      let left ← exprFromJson leftJson
      let rightJson ← cmpObj.getObjVal? "right"
      let right ← exprFromJson rightJson
      return .cmp op left right
    | .error _ =>
    -- Try logic
    match j.getObjVal? "logic" with
    | .ok logicObj => do
      let op ← logicObj.getObjValAs? LogicOp "op"
      let leftJson ← logicObj.getObjVal? "left"
      let left ← boolExprFromJson leftJson
      let rightJson ← logicObj.getObjVal? "right"
      let right ← boolExprFromJson rightJson
      return .logic op left right
    | .error _ =>
    -- Try not
    match j.getObjVal? "not" with
    | .ok innerJson => do
      let inner ← boolExprFromJson innerJson
      return .neg inner
    | .error _ =>
    -- Try isPresent
    match j.getObjVal? "isPresent" with
    | .ok fieldVal =>
      match fieldVal.getObjValAs? String "name" with
      | .ok name =>
        match fieldVal.getObjValAs? String "qualifier" with
        | .ok qual => .ok (.isPresent (.qualified qual name))
        | .error _ => .ok (.isPresent (.simple name))
      | .error _ => .error s!"isPresent object must have a \"name\" key, got {fieldVal}"
    | .error _ =>
    .error s!"expected BoolExpr (cmp, logic, not, or isPresent), got {j}"
end

instance : FromJson Expr where
  fromJson? := exprFromJson

instance : FromJson BoolExpr where
  fromJson? := boolExprFromJson

/-- Parse a FieldAssign from JSON.
    `{"fieldName": "total", "value": <Expr>}` -/
instance : FromJson FieldAssign where
  fromJson? j := do
    let fieldName ← j.getObjValAs? String "fieldName"
    let value ← j.getObjValAs? Expr "value"
    return ⟨fieldName, value⟩

/-- Parse a TypedParam from JSON. `{"name": "scale", "type": "ScaledAmount"}` -/
def typedParamFromJson (j : Json) : Except String TypedParam := do
  let name ← j.getObjValAs? String "name"
  let type ← j.getObjValAs? String "type"
  return ⟨name, type⟩

instance : FromJson TypedParam where
  fromJson? := typedParamFromJson

/-- Parse a FunctionRepr from JSON (the Aral-fn format). -/
instance : FromJson FunctionRepr where
  fromJson? j := do
    let name ← j.getObjValAs? String "name"
    let inputType ← j.getObjValAs? String "inputType"
    let inputFields ← j.getObjValAs? (List String) "inputFields"
    let params ← j.getObjValAs? (List String) "params"
    let assigns ← j.getObjValAs? (List FieldAssign) "assigns"
    -- typedParams is optional, defaults to []
    let typedParams : List TypedParam :=
      match j.getObjValAs? (List TypedParam) "typedParams" with
      | Except.ok tps => tps
      | Except.error _ => []
    -- optionalFields is optional, defaults to []
    let optionalFields : List String :=
      match j.getObjValAs? (List String) "optionalFields" with
      | Except.ok fs => fs
      | Except.error _ => []
    return ⟨name, inputType, inputFields, params, assigns, typedParams, optionalFields⟩

mutual
  /-- Collect all field references in an Expr (as resolved keys). -/
  def collectExprFields : Expr → List String
    | .lit _ => []
    | .field ref => [ref.toKey]
    | .arith _ l r => collectExprFields l ++ collectExprFields r
    | .condExpr c t e => collectBoolExprFields c ++ collectExprFields t ++ collectExprFields e
    | .roundExpr _ e => collectExprFields e
    | .sumExpr _coll _body => []
      -- Sum expressions reference collection-derived names (collKey-len, item fields)
      -- that are generated by the pipeline, not declared in inputFields/params.
      -- Skip validation — the renderer handles these declarations.

  /-- Collect all field references in a BoolExpr. -/
  def collectBoolExprFields : BoolExpr → List String
    | .cmp _ l r     => collectExprFields l ++ collectExprFields r
    | .logic _ l r   => collectBoolExprFields l ++ collectBoolExprFields r
    | .neg b         => collectBoolExprFields b
    | .isPresent ref => ["has-" ++ ref.toKey]
    | .eachExpr _coll _body => []
      -- Each expressions reference collection-derived names (collKey-len, item fields)
      -- that are generated by the pipeline, not declared in inputFields/params.
end

mutual
  /-- Collect the simple-ref field names of every isPresent node in an Expr tree.
      Qualified refs (on typed parameters) are checked via the params channel,
      not against optionalFields. -/
  def collectIsPresentNames : Expr → List String
    | .lit _ => []
    | .field _ => []
    | .arith _ l r => collectIsPresentNames l ++ collectIsPresentNames r
    | .condExpr c t e =>
        collectIsPresentNamesBool c ++ collectIsPresentNames t ++ collectIsPresentNames e
    | .roundExpr _ e => collectIsPresentNames e
    | .sumExpr _coll _body => []

  def collectIsPresentNamesBool : BoolExpr → List String
    | .cmp _ l r => collectIsPresentNames l ++ collectIsPresentNames r
    | .logic _ l r => collectIsPresentNamesBool l ++ collectIsPresentNamesBool r
    | .neg b => collectIsPresentNamesBool b
    | .isPresent (.simple name) => [name]
    | .isPresent (.qualified _ _) => []
    | .eachExpr _coll _body => []
end

/-- Validate a FunctionRepr for semantic consistency.
    Runs after JSON structural parsing.
    Checks:
    - All assigned field names are in inputFields
    - isPresent on simple refs only targets fields listed in optionalFields
    - All field references in expressions refer to known fields or params
    - No duplicate assignments -/
def validateFunctionRepr (f : FunctionRepr) : Except String FunctionRepr := do
  -- Presence keys for optional fields are valid references (pipeline adds them to inputFields later)
  let presenceKeys := f.optionalFields.map ("has-" ++ ·)
  let knownNames := f.inputFields ++ f.params ++ presenceKeys
  -- Check assigned fields are in inputFields
  for a in f.assigns do
    unless f.inputFields.contains a.fieldName do
      .error s!"assigned field '{a.fieldName}' is not in inputFields {f.inputFields}"
  -- Check for duplicate assignments
  let assignedFields := f.assigns.map (·.fieldName)
  let dups := assignedFields.filter fun fld =>
    (assignedFields.filter (· == fld)).length > 1
  if !dups.eraseDups.isEmpty then
    .error s!"duplicate assignments for field(s): {dups.eraseDups}"
  -- Check isPresent targets declared optional fields (clearer error than the generic check below)
  for a in f.assigns do
    let ipNames := collectIsPresentNames a.value
    for name in ipNames do
      unless f.optionalFields.contains name do
        .error s!"in assignment to '{a.fieldName}': isPresent({name}) requires '{name}' to be listed in optionalFields. Add '{name}' to optionalFields if it's an optional field on the input type, or remove the presence check if the field is always provided."
  -- Check all field references in expressions resolve
  for a in f.assigns do
    let refs := collectExprFields a.value
    for ref in refs do
      unless knownNames.contains ref do
        .error s!"in assignment to '{a.fieldName}': found '{a.fieldName}: {ref}' but '{ref}' is not a known input or parameter. If this is a local variable, the parser couldn't resolve its declaration. Known: inputFields={f.inputFields}, params={f.params}"
  .ok f

/-- Read, parse, and validate an Aral-fn JSON file into a FunctionRepr. -/
def readAralFn (path : System.FilePath) : IO (Except String FunctionRepr) := do
  let contents ← IO.FS.readFile path
  let json ← match Json.parse contents with
    | .ok j => pure j
    | .error e => return .error s!"JSON parse error: {e}"
  match FromJson.fromJson? json (α := FunctionRepr) with
  | .ok repr => return (validateFunctionRepr repr)
  | .error e => return .error s!"Aral-fn format error: {e}"
