/-
  Ephemaral — Compiler
  The core transformation: Invariant → CompiledInvariant.
-/
import Proofs.Types

mutual
  /-- Expr → SmtExpr for invariant context. Each DSL node maps to one SMT node.
      Proved correct in Correctness.lean. -/
  def compileInvExpr : Expr → SmtExpr
    | .lit n            => .lit n
    | .field ref        => .const ref.toKey
    | .arith op l r     => .arith op (compileInvExpr l) (compileInvExpr r)
    | .condExpr c t e   => .condExpr (compileInvBoolExpr c) (compileInvExpr t) (compileInvExpr e)
    | .roundExpr mode e => .roundExpr mode (compileInvExpr e)
    | .sumExpr coll body => .sumExpr coll.toKey (compileInvExpr body)

  /-- BoolExpr → SmtBoolExpr for invariant context. isPresent becomes (neq has-field 0). -/
  def compileInvBoolExpr : BoolExpr → SmtBoolExpr
    | .cmp op l r    => .cmp op (compileInvExpr l) (compileInvExpr r)
    | .logic op l r  => .logic op (compileInvBoolExpr l) (compileInvBoolExpr r)
    | .neg b         => .neg (compileInvBoolExpr b)
    | .isPresent ref => .cmp .neq (.const ("has-" ++ ref.toKey)) (.lit 0)
    | .eachExpr coll body => .eachExpr coll.toKey (compileInvBoolExpr body)
end

mutual
  /-- Collect all field names referenced in an expression. -/
  def collectFields : Expr → List String
    | .lit _            => []
    | .field ref        => [ref.toKey]
    | .arith _ l r      => collectFields l ++ collectFields r
    | .condExpr c t e   => collectFieldsBool c ++ collectFields t ++ collectFields e
    | .roundExpr _ e    => collectFields e
    | .sumExpr coll _body => [coll.toKey ++ "-len"]
      -- Body fields are item-scoped (declared as accessor funs by renderer), not scalar consts

  /-- Collect all field names referenced in a boolean expression. -/
  def collectFieldsBool : BoolExpr → List String
    | .cmp _ l r     => collectFields l ++ collectFields r
    | .logic _ l r   => collectFieldsBool l ++ collectFieldsBool r
    | .neg b         => collectFieldsBool b
    | .isPresent ref => ["has-" ++ ref.toKey]
    | .eachExpr coll _body => [coll.toKey ++ "-len"]
end

/-- Invariant → CompiledInvariant: collect constants, compile body, generate SMT-LIB name. -/
def compile (inv : Invariant) : CompiledInvariant :=
  { consts  := (collectFieldsBool inv.body).eraseDups
  , body    := compileInvBoolExpr inv.body
  , invName := "inv-" ++ inv.name.map fun c => if c == '_' then '-' else c
  }
