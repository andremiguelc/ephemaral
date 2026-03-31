/-
  Ephemaral — Function Representation Types
  The proof boundary for function encoding.
  Layer 1: language-agnostic. Any language parser produces these types.
-/
import Proofs.Types

/-- A field assignment: one output field defined by an expression.
    Example: `total = subtotal - discountAmount` becomes
    `{ fieldName := "total", value := .arith .sub (.field (.simple "subtotal")) (.field (.simple "discountAmount")) }` -/
structure FieldAssign where
  fieldName : String   -- which output field is being set
  value     : Expr     -- expression computing the new value (reuses DSL Expr)
  deriving Repr

/-- A typed parameter: name + type, used for routing .aral invariants as preconditions.
    The .aral file's root prefix is matched case-insensitively against the type name. -/
structure TypedParam where
  name : String   -- parameter name (must also appear in FunctionRepr.params)
  type : String   -- type name (e.g., "ScaledAmount")
  deriving Repr

/-- The proof boundary for function encoding. Produced by any language parser (via JSON),
    consumed by compileFun. Captures: input type, its fields, extra params, and which
    fields the function changes (spread + override pattern). -/
structure FunctionRepr where
  name        : String           -- function name
  inputType   : String           -- the type being transformed (e.g., "Order")
  inputFields : List String      -- all fields on the input type relevant to verification
  params      : List String      -- extra parameters beyond the input object
  assigns     : List FieldAssign -- which fields change and to what expression
  typedParams    : List TypedParam := []  -- typed parameters for cross-type invariant routing
  optionalFields : List String := []     -- nullable fields: pipeline generates has-{field} presence flags
  deriving Repr
