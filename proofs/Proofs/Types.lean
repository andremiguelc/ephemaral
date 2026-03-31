/-
  Ephemaral — Shared Types
  The vocabulary shared by parser, compiler, codegen, semantics, and proofs.
-/

/-- Comparison operators in the invariant DSL. -/
inductive CompOp where
  | eq | neq | gt | lt | gte | lte
  deriving DecidableEq, Repr

/-- Arithmetic operators in the invariant DSL. -/
inductive ArithOp where
  | add | sub | mul
  | div  -- total: a / 0 = 0
  deriving DecidableEq, Repr

/-- Rounding modes for financial arithmetic. -/
inductive RoundingMode where
  | floor | ceil | halfUp
  deriving DecidableEq, Repr

/-- Logical operators in the invariant DSL. -/
inductive LogicOp where
  | and | or
  deriving DecidableEq, Repr

/-- A field reference, preserving the qualifier/field boundary from source code.
    Simple refs are fields on the input type (e.g., `total`).
    Qualified refs are fields on a parameter or bound variable (e.g., `discount.percent`). -/
inductive FieldRef where
  | simple    (name : String)                        -- field on input type
  | qualified (qualifier : String) (name : String)   -- field on parameter/bound variable
  deriving DecidableEq, Repr

/-- Resolve a FieldRef to the environment key used for evaluation. -/
def FieldRef.toKey : FieldRef → String
  | .simple name => name
  | .qualified qual name => qual ++ "-" ++ name

mutual
  inductive Expr where
    | lit       (n : Rat)
    | field     (ref : FieldRef)
    | arith     (op : ArithOp) (l r : Expr)
    | condExpr  (cond : BoolExpr) (thenB : Expr) (elseB : Expr)
    | roundExpr (mode : RoundingMode) (e : Expr)
    | sumExpr   (collection : FieldRef) (body : Expr)

  inductive BoolExpr where
    | cmp       (op : CompOp) (l r : Expr)
    | logic     (op : LogicOp) (l r : BoolExpr)
    | neg       (inner : BoolExpr)
    | isPresent (ref : FieldRef)
end

deriving instance Repr for Expr
deriving instance Repr for BoolExpr

/-- A parsed invariant: name + root object + boolean body.
    Produced by parseInvariant, consumed by compile. -/
structure Invariant where
  name  : String     -- invariant name (e.g., "total_non_negative")
  root  : String     -- root object (e.g., "order") — stripped during codegen
  body  : BoolExpr   -- the boolean expression
  deriving Repr

mutual
  inductive SmtExpr where
    | lit       (n : Rat)
    | const     (name : String)
    | arith     (op : ArithOp) (l r : SmtExpr)
    | condExpr  (cond : SmtBoolExpr) (thenB : SmtExpr) (elseB : SmtExpr)
    | roundExpr (mode : RoundingMode) (e : SmtExpr)
    | sumExpr   (collKey : String) (body : SmtExpr)

  inductive SmtBoolExpr where
    | cmp   (op : CompOp) (l r : SmtExpr)
    | logic (op : LogicOp) (l r : SmtBoolExpr)
    | neg   (inner : SmtBoolExpr)
end

deriving instance Repr for SmtExpr
deriving instance Repr for SmtBoolExpr

/-- The SMT-LIB fragment produced by compilation. -/
structure CompiledInvariant where
  consts  : List String    -- constants that need (declare-const ... Real)
  body    : SmtBoolExpr    -- compiled boolean expression
  invName : String         -- SMT-LIB function name (e.g., "inv-total-non-negative")
  deriving Repr
