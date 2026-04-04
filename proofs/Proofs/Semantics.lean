/-
  Ephemaral — Semantics
  Formal definitions of what DSL expressions and SMT-LIB fragments MEAN.
  These definitions are what the proofs reason about.
-/
import Proofs.Types

/-- An environment maps field names to rational values.
    Represents "the current state of the data" — one particular
    assignment of values to fields.
    Rat matches SMT-LIB's Real sort for all algebraic operations.
    Business logic has no irrational numbers. -/
abbrev Env := String → Rat

/-- What ==, !=, >, <, >=, <= mean on rationals.
    Used by evalBoolExpr and evalSmtBoolExpr. -/
def evalCompOp (op : CompOp) (a b : Rat) : Bool :=
  match op with
  | .eq  => a == b
  | .neq => a != b
  | .gt  => a > b
  | .lt  => a < b
  | .gte => a >= b
  | .lte => a <= b

/-- What +, -, *, / mean on rationals. Division is total: a / 0 = 0. -/
def evalArithOp (op : ArithOp) (a b : Rat) : Rat :=
  match op with
  | .add => a + b
  | .sub => a - b
  | .mul => a * b
  | .div => if b ≠ 0 then a / b else 0

/-- Apply floor/ceil/halfUp to a Rat, returning Rat (via Int cast).
    Matches SMT-LIB to_int/to_real encoding. -/
def evalRound (mode : RoundingMode) (q : Rat) : Rat :=
  match mode with
  | .floor  => ↑q.floor
  | .ceil   => ↑q.ceil
  | .halfUp => ↑(q + 1/2).floor

/-- What and/or mean on booleans. Used by evalBoolExpr and evalSmtBoolExpr. -/
def evalLogicOp (op : LogicOp) (a b : Bool) : Bool :=
  match op with
  | .and => a && b
  | .or  => a || b

/-- Sum f(i) for i = 0..n-1. Used by both evalExpr and evalSmtExpr,
    so the correctness proof reduces to showing f agrees per item. -/
def sumN (f : Nat → Rat) : Nat → Rat
  | 0     => 0
  | n + 1 => f n + sumN f n

/-- Conjoin f(i) for i = 0..n-1. Boolean analog of sumN.
    Used by both evalBoolExpr and evalSmtBoolExpr for `each`. -/
def allN (f : Nat → Bool) : Nat → Bool
  | 0     => true
  | n + 1 => f n && allN f n

/-- Build a per-item environment for collection items.
    Maps field name "x" to env("collKey-i-x") so the body expression
    evaluates in the context of the i-th collection item. -/
def itemEnvAt (env : Env) (collKey : String) (i : Nat) : Env :=
  fun name => env (collKey ++ "-" ++ toString i ++ "-" ++ name)

mutual
  def evalExpr (env : Env) : Expr → Rat
    | .lit n            => n
    | .field ref        => env ref.toKey
    | .arith op l r     => evalArithOp op (evalExpr env l) (evalExpr env r)
    | .condExpr c t e   => if evalBoolExpr env c then evalExpr env t else evalExpr env e
    | .roundExpr mode e => evalRound mode (evalExpr env e)
    | .sumExpr coll body =>
      -- Collection length stored as "{collKey}-len" in the environment.
      -- Item fields at index i accessed via itemEnvAt: "field" → env("{collKey}-{i}-{field}").
      let collKey := coll.toKey
      let len := (env (collKey ++ "-len")).floor.toNat
      sumN (fun i => evalExpr (itemEnvAt env collKey i) body) len

  def evalBoolExpr (env : Env) : BoolExpr → Bool
    | .cmp op l r     => evalCompOp op (evalExpr env l) (evalExpr env r)
    | .logic op l r   => evalLogicOp op (evalBoolExpr env l) (evalBoolExpr env r)
    | .neg b          => !(evalBoolExpr env b)
    | .isPresent ref  => env ("has-" ++ ref.toKey) != 0
    | .eachExpr coll body =>
      let collKey := coll.toKey
      let len := (env (collKey ++ "-len")).floor.toNat
      allN (fun i => evalBoolExpr (itemEnvAt env collKey i) body) len
end

mutual
  def evalSmtExpr (env : Env) : SmtExpr → Rat
    | .lit n            => n
    | .const name       => env name
    | .arith op l r     => evalArithOp op (evalSmtExpr env l) (evalSmtExpr env r)
    | .condExpr c t e   => if evalSmtBoolExpr env c then evalSmtExpr env t else evalSmtExpr env e
    | .roundExpr mode e => evalRound mode (evalSmtExpr env e)
    | .sumExpr collKey body =>
      let len := (env (collKey ++ "-len")).floor.toNat
      sumN (fun i => evalSmtExpr (itemEnvAt env collKey i) body) len

  def evalSmtBoolExpr (env : Env) : SmtBoolExpr → Bool
    | .cmp op l r   => evalCompOp op (evalSmtExpr env l) (evalSmtExpr env r)
    | .logic op l r => evalLogicOp op (evalSmtBoolExpr env l) (evalSmtBoolExpr env r)
    | .neg b        => !(evalSmtBoolExpr env b)
    | .eachExpr collKey body =>
      let len := (env (collKey ++ "-len")).floor.toNat
      allN (fun i => evalSmtBoolExpr (itemEnvAt env collKey i) body) len
end

/-- Evaluate an Invariant's body in an environment. -/
def dslSemantics (env : Env) (inv : Invariant) : Bool :=
  evalBoolExpr env inv.body

/-- Evaluate a CompiledInvariant's body in an environment.
    compile_preserves_semantics proves dslSemantics = smtSemantics. -/
def smtSemantics (env : Env) (frag : CompiledInvariant) : Bool :=
  evalSmtBoolExpr env frag.body
