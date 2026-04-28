# Aral-fn — Function Representation Format

Aral-fn is the JSON format for describing function behavior to the ephemaral verification tool. It sits at the **proof boundary**: everything before it (parsers, LLMs) is unproved and can be written in any language. Everything after it (compilation, SMT-LIB generation, Z3 verification) is proved correct in Lean 4.

## What it describes

A pure data transformation: a function that takes a typed input (plus optional parameters) and returns a value of the same type. Each output field is either explicitly assigned by an expression (listed in `assigns`) or preserved unchanged from the input (every field not listed).

```typescript
function adjustValue(record: Record, delta: number): Record {
  return {
    ...record,
    value: delta > 0 ? record.value - delta : record.value,
  };
}
```

becomes:

```json
{
  "name": "adjustValue",
  "inputType": "Record",
  "inputFields": ["value"],
  "params": ["delta"],
  "assigns": [
    {
      "fieldName": "value",
      "value": {
        "ite": {
          "cond": { "cmp": { "op": "gt", "left": { "field": { "name": "delta" } }, "right": { "lit": 0 } } },
          "then": { "arith": { "op": "sub", "left": { "field": { "name": "value" } }, "right": { "field": { "name": "delta" } } } },
          "else": { "field": { "name": "value" } }
        }
      }
    }
  ]
}
```

## How to use it

```bash
# Run verification
ephemaral func.aral-fn.json rules.aral

# Parse source to Aral-fn JSON (using a parser), then verify
npx tsx src/index.ts myFunction.ts > /tmp/func.aral-fn.json
ephemaral /tmp/func.aral-fn.json rules.aral
```

## Schema

The formal JSON Schema is at `aral-fn.schema.json`.

## Fields

| Field | Type | Description |
|-------|------|-------------|
| `name` | string | Function name (for diagnostics) |
| `inputType` | string | The type being transformed (matched against the invariant's type-binding prefix) |
| `inputFields` | string[] | Fields on the type relevant to verification |
| `params` | string[] | Extra parameters (free variables in verification) |
| `assigns` | FieldAssign[] | Which fields change and to what expression |
| `typedParams` | TypedParam[]? | Typed parameters for cross-type invariant routing |
| `optionalFields` | string[]? | Nullable fields — pipeline generates `has-{field}` presence constants |

### FieldAssign

| Field | Type | Description |
|-------|------|-------------|
| `fieldName` | string | Which output field is being set |
| `value` | Expr | Expression computing the new value |

### Expr

Expressions are recursive. Six variants:

| Variant | JSON | Example | Description |
|---------|------|---------|-------------|
| Literal | `{"lit": 42}` | `{"lit": 0}` | Numeric constant (converted to Rat internally). Convention: `1` = true, `0` = false for boolean fields. |
| Field (simple) | `{"field": {"name": "x"}}` | `{"field": {"name": "value"}}` | Field on the input type or a scalar parameter |
| Field (qualified) | `{"field": {"qualifier": "q", "name": "x"}}` | `{"field": {"qualifier": "config", "name": "rate"}}` | Field on a typed parameter (e.g., `config.rate`) |
| Arithmetic | `{"arith": {"op": "sub", "left": ..., "right": ...}}` | see above | +, -, *, / (total: a/0=0) |
| If-then-else | `{"ite": {"cond": <BoolExpr>, "then": <Expr>, "else": <Expr>}}` | see above | Conditional assignment |
| Rounding | `{"round": {"expr": <Expr>, "mode": "floor"}}` | `{"round": {"expr": ..., "mode": "half_up"}}` | floor (→−∞), ceil (→+∞), half_up (standard rounding) |

Arithmetic operators: `"add"`, `"sub"`, `"mul"`, `"div"` (total: division by zero returns 0).

Rounding modes: `"floor"`, `"ceil"`, `"half_up"`.

Field references use `FieldRef` — a structured type with two variants:
- **Simple** `{"field": {"name": "value"}}` — resolved by the compiler: if the name is in `inputFields`, it refers to the input value (becomes `in-value` in SMT-LIB); otherwise, it's a parameter (stays as `value`).
- **Qualified** `{"field": {"qualifier": "config", "name": "rate"}}` — a field on a typed parameter. The compiler joins them: `config-rate` in SMT-LIB. The qualifier/field boundary is preserved structurally in the IR; the compiler (proved correct) decides the SMT constant name.

### BoolExpr

Boolean expressions are used as conditions in `ite`. Four variants:

| Variant | JSON | Example | Description |
|---------|------|---------|-------------|
| Comparison | `{"cmp": {"op": "gt", "left": <Expr>, "right": <Expr>}}` | `{"cmp": {"op": "gt", "left": {"field": {"name": "delta"}}, "right": {"lit": 0}}}` | >, <, >=, <=, ==, != |
| Logic | `{"logic": {"op": "and", "left": <BoolExpr>, "right": <BoolExpr>}}` | compound conditions | and, or |
| Negation | `{"not": <BoolExpr>}` | `{"not": {"cmp": {"op": "eq", ...}}}` | boolean not |
| Presence | `{"isPresent": {"name": "x"}}` | `{"isPresent": {"name": "bonus"}}` | nullable field presence check |

Comparison operators: `"eq"` (==), `"neq"` (!=), `"gt"` (>), `"lt"` (<), `"gte"` (>=), `"lte"` (<=).

## How fields work

Fields not listed in `assigns` are preserved from the input by default. If the input has fields `[value, label]` and only `value` is assigned, the output's `label` equals the input's `label` automatically.

`inputFields` should include all fields that:
- Are assigned in `assigns`
- Are referenced in assignment expressions (including inside `ite` conditions)
- Are referenced by applicable invariants

## Writing a parser

A parser reads source code in some language and produces Aral-fn JSON. The parser:

1. Identifies the function signature (name, input type, parameters, return type)
2. Identifies which fields are modified and how
3. Builds the expression tree for each assignment (including ternary → ite conversion)
4. Outputs JSON conforming to the schema

The parser does NOT need to be in Lean. It does NOT need proofs. It is empirically validated — if it produces correct JSON, the proved compiler guarantees the verification is faithful.

Example parsers:
- TypeScript: [ts-to-ephemaral](https://github.com/andremiguelc/ts-to-ephemaral) — covers the full IR expression vocabulary: arithmetic with precedence, const-inlining, if/else→ite lowering, division, rounding, ternary, comparisons, boolean logic, null coalescing → `isPresent` + `ite`
- LLM-as-parser: give an LLM the schema + source code, ask for JSON output
- Any tool that produces valid Aral-fn JSON works

## What happens after

```
Aral-fn JSON ──→ [PROOF BOUNDARY] ──→ Deserialize ──→ FunctionRepr
                                                          │
.aral file ──→ Invariant Parser ──→ CompiledInvariants          │
                                        │                  │
                                        └──→ Compile ──→ SMT-LIB ──→ Z3 ──→ Diagnostic
                                                  │               │
                                            proved correct    trusted solver
```

The Lean proofs (`compileFunExpr_preserves` + `compileFunBoolExpr_preserves`) guarantee: if the Aral-fn JSON faithfully represents the function, then the SMT-LIB faithfully represents the verification question. Z3 then decides whether any valid input can break the invariants.

## Future evolution

The Expr type will grow to support more patterns:
- Collection aggregation — `sum`, `count` via bounded unrolling

`FieldRef` will grow to support new qualifier kinds:
- `bound` — lambda-bound variables in collection operations
- `state` — pre/post state references in state machine transitions

Each addition requires one new Lean proof case per theorem but benefits ALL parsers automatically.
