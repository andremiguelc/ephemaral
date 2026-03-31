/-
  Ephemaral — Function Semantics
  Formal definitions of what function expressions mean in the
  input/output context. These definitions are what the proofs reason about.

  Layer 1: language-agnostic.
-/
import Proofs.Types
import Proofs.Semantics

/-- Resolve a field name in function context.
    Input fields are looked up with "in-" prefix in the environment.
    Parameters (anything else) are looked up as-is.

    This is the DSL-side interpretation: when the source code says
    `order.subtotal`, we look up `env ("in-" ++ "subtotal")`. -/
def funEnv (env : Env) (inputFields : List String) (name : String) : Rat :=
  if inputFields.contains name then env ("in-" ++ name)
  else env name

/-- inputFields contain only simple field names, never collection-indexed
    compound names like "lineItems-0-price" or "lineItems-len".
    This is true by construction: inputFields come from JSON field names,
    which are simple identifiers. Without this, funEnv would incorrectly
    prefix collection accessor names with "in-", breaking the sum encoding. -/
def CollectionSafe (inputFields : List String) : Prop :=
  ∀ (k : String) (i : Nat) (name : String),
    inputFields.contains (k ++ "-" ++ toString i ++ "-" ++ name) = false
    ∧ inputFields.contains (k ++ "-len") = false

/-- Collection pass-through: the environment maps bare collection names
    to the same values as their "in-" prefixed counterparts.
    This models the SMT-LIB assertions the pipeline generates
    for pass-through collections (out-x = in-x for unchanged fields). -/
def CollectionPassthrough (env : Env) : Prop :=
  ∀ (k : String) (suffix : String),
    env (k ++ suffix) = env ("in-" ++ k ++ suffix)
