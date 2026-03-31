/-
  Ephemaral — Function Compiler
  The core transformation: FunctionRepr → SMT-LIB structures.
  Layer 1: language-agnostic.
-/
import Proofs.Types
import Proofs.Function.Types
import Proofs.Invariant.Compile

/-- Prefix a field name for input context. -/
def inField (f : String) : String := "in-" ++ f

/-- Prefix a field name for output context. -/
def outField (f : String) : String := "out-" ++ f

mutual
  /-- Expr → SmtExpr for function context. Input fields get "in-" prefix; parameters stay bare.
      Sum bodies use compileInvExpr (item fields don't get prefixed). -/
  def compileFunExpr (inputFields : List String) : Expr → SmtExpr
    | .lit n            => .lit n
    | .field ref        => if inputFields.contains ref.toKey then .const (inField ref.toKey)
                           else .const ref.toKey
    | .arith op l r     => .arith op (compileFunExpr inputFields l)
                                      (compileFunExpr inputFields r)
    | .condExpr c t e   => .condExpr (compileFunBoolExpr inputFields c)
                                      (compileFunExpr inputFields t)
                                      (compileFunExpr inputFields e)
    | .roundExpr mode e => .roundExpr mode (compileFunExpr inputFields e)
    | .sumExpr coll body =>
      -- Body uses compileInvExpr (item fields stay bare). Collection key gets "in-" prefix.
      .sumExpr (inField coll.toKey) (compileInvExpr body)

  /-- BoolExpr → SmtBoolExpr for function context. isPresent resolved same as compileInvBoolExpr. -/
  def compileFunBoolExpr (inputFields : List String) : BoolExpr → SmtBoolExpr
    | .cmp op l r   => .cmp op (compileFunExpr inputFields l)
                                (compileFunExpr inputFields r)
    | .logic op l r => .logic op (compileFunBoolExpr inputFields l)
                                  (compileFunBoolExpr inputFields r)
    | .neg b        => .neg (compileFunBoolExpr inputFields b)
    | .isPresent ref =>
        let presKey := "has-" ++ ref.toKey
        let smtConst := if inputFields.contains presKey
                         then SmtExpr.const (inField presKey)
                         else SmtExpr.const presKey
        .cmp .neq smtConst (.lit 0)
end

/-- Compute the list of fields unchanged by the function (spread fields).
    These are input fields not appearing in any assignment. -/
def unchangedFields (f : FunctionRepr) : List String :=
  let changedFields := f.assigns.map (·.fieldName)
  f.inputFields.filter (fun fld => !changedFields.contains fld)

/-- The compiled result of function encoding.
    Contains everything needed to render the verification SMT-LIB. -/
structure CompiledFunction where
  inConsts     : List String                -- input field constants
  outConsts    : List String                -- output field constants
  paramConsts  : List String                -- extra parameter constants
  unchangedEqs : List (String × String)     -- (out-field, in-field) equalities
  assignDefs   : List (String × SmtExpr)    -- (out-field, compiled expression)
  deriving Repr

/-- Compile a FunctionRepr into a CompiledFunction.
    Produces the SMT-LIB constants, unchanged-field equalities,
    and assignment definitions. -/
def compileFun (f : FunctionRepr) : CompiledFunction :=
  { inConsts     := f.inputFields.map inField
  , outConsts    := f.inputFields.map outField
  , paramConsts  := f.params
  , unchangedEqs := (unchangedFields f).map (fun fld => (outField fld, inField fld))
  , assignDefs   := f.assigns.map (fun a =>
      (outField a.fieldName, compileFunExpr f.inputFields a.value))
  }
