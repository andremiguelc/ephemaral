# Aral — Language Specification

A formal specification for a language that describes **what must always be true about data**. Each construct is added only after it has been compiled to SMT-LIB and proved correct in Lean 4.

---

## Design Principles

1. **Invariants describe data, not code.** An invariant says what must be true about a value of a type. It never references how the code works, only what the data looks like.

2. **Field names are the shared vocabulary.** The invariant says `record.amount`. The type has `Record.amount`. The SMT-LIB constant is `amount`. Same name at every layer. This is how invariants bind to code — through types, not through functions.

3. **Restriction is a feature.** The language deliberately cannot express everything. What it *can* express is decidable and verifiable. What it *can't* express is out of scope for formal verification.

4. **Prove before you ship.** A construct is not part of the language until its compilation to SMT-LIB has been proved correct in Lean 4.

---

## How Invariants Bind to Code

An invariant references **types**, not variables or functions.

```
invariant amount_non_negative:
  record.amount >= 0
```

Here `record` is not a specific variable — it means "any value of type `Record`." The field `amount` is a field on that type. When a function has signature `f(record: Record): Record`, the verification asks:

> If the input `Record` satisfies all invariants, does the output `Record` also satisfy them?

The invariant compiler produces the constraint shape: `(>= amount 0.0)`. The function encoder produces `in-amount` and `out-amount` constants from the function's type signature, and plugs the invariant constraint into both sides.

**The root prefix is the type binding.** The root (`record` in `record.amount`) is the type name, matched case-insensitively to the function's input/output type. Convention: the root should be the lowercase of the type name (`record` for `Record`, `entry` for `Entry`). The pipeline validates this match and warns on mismatch, but proceeds — the field-level overlap filter handles the actual matching.

**Field names are the contract.** If the invariant says `record.amount` but the type has `Record.value`, nothing connects. The binding fails at compile time — before verification starts.

**Current limitation:** The function must take and return the same type (`f(x: T, ...): T`). Functions with output-only types, multiple typed inputs, or cross-type transformations are not yet supported.

---

## File Format

An `.aral` file contains one or more invariant declarations, separated by blank lines. Lines starting with `#` are comments.

```
# <human-readable explanation>
invariant <name>:
  <expression>

# <another explanation>
invariant <another_name>:
  <expression>
```

- **Comments** are for humans. The compiler ignores them.
- **Names** use `snake_case`. They become SMT-LIB function names with `inv-` prefix and hyphens: `amount_non_negative` → `inv-amount-non-negative`.
- **Expressions** are indented under the declaration. The expression is the machine-checkable part.

---

## Formal Grammar

EBNF-style grammar for `.aral` files. Every production corresponds to a proved construct below.

```ebnf
(* ─── File structure ─── *)
file           = { comment | invariant | blank_line } ;
comment        = "#" , { any_char } , newline ;
invariant      = "invariant" , name , ":" , newline , indent , expr ;
name           = letter , { letter | digit | "_" } ;

(* ─── Expressions ─── *)
expr           = comparison
               | expr , ( "and" | "or" ) , expr
               | "if" , root , "." , field , "exists" , ":" , expr
               | "each" , "(" , root , "." , collection , "," , item_pred , ")"
               | "sum"  , "(" , root , "." , collection , "," , item_expr , ")"
               | "transition" , "(" , root , "." , field , ")" , ":" , transition_list ;

comparison     = arith_expr , cmp_op , arith_expr ;
cmp_op         = ">=" | "<=" | ">" | "<" | "==" | "!=" ;

arith_expr     = term , { ( "+" | "-" ) , term } ;
term           = factor , { ( "*" | "/" ) , factor } ;
factor         = number
               | root , "." , field
               | "round" , "(" , arith_expr , "," , round_mode , ")"
               | "(" , arith_expr , ")" ;
round_mode     = "floor" | "ceil" | "halfUp" ;

(* ─── Collection bodies ─── *)
item_expr      = item_factor , { ( "+" | "-" | "*" | "/" ) , item_factor } ;
item_factor    = number | field_name ;
item_pred      = item_comparison , { ( "and" | "or" ) , item_comparison } ;
item_comparison = item_expr , cmp_op , item_expr ;

(* ─── Transitions ─── *)
transition_list = transition_rule , { newline , indent , transition_rule } ;
transition_rule = state , "->" , state ;
state          = identifier ;

(* ─── Terminals ─── *)
root           = identifier ;            (* lowercase of type name *)
field          = identifier ;
field_name     = identifier ;            (* bare name, item-scoped *)
collection     = identifier ;
number         = [ "-" ] , digit , { digit } , [ "." , digit , { digit } ] ;
identifier     = letter , { letter | digit | "_" } ;
```

**Key scoping rule:** Inside `sum()` and `each()` bodies, field names are bare (no root prefix). `sum(order.items, quantity * price)` means `item.quantity * item.price` — the collection accessor provides the scope.

---

## Primitives

| Primitive | Syntax | SMT-LIB | Example |
|-----------|--------|---------|---------|
| Field reference | `<root>.<field>` | Root stripped, field becomes `(declare-const field Real)` | `record.amount` |
| Numeric literal | `0`, `100`, `-5` | Real literal with `.0` suffix | `100` → `100.0` |
| Comparisons | `==` `!=` `>` `<` `>=` `<=` | Direct mapping (`!=` → `(not (= ...))`) | `record.amount >= 0` |

---

## Constructs

Each construct has: syntax, SMT-LIB translation, and Lean 4 proof status.

### `field_cmp` — Field Comparison ✓

```
<expr> <comparison_op> <expr>
```

```
invariant amount_non_negative:
  record.amount >= 0
```

SMT-LIB: `(define-fun inv-amount-non-negative () Bool (>= amount 0.0))`

Proof: `compile_preserves_semantics` in `proofs/Proofs/Invariant/Correctness.lean`.

### `arith` — Arithmetic (+, -, *, /) ✓

```
<expr> + <expr>      <expr> * <expr>
<expr> - <expr>      <expr> / <expr>
```

Multi-term arithmetic with correct precedence and left-associativity. `*`/`/` bind tighter than `+`/`-`.

```
invariant margin_non_negative:
  record.revenue - record.cost >= 0

invariant total_equals_components:
  record.total == record.base + record.adjustment - record.reduction

invariant computed_value:
  record.result == record.quantity * record.rate + record.offset
```

SMT-LIB: `(define-fun inv-margin-non-negative () Bool (>= (- revenue cost) 0.0))`

**Division:** Total — `a / 0 = 0`. Rendered as `(ite (= b 0.0) 0.0 (/ a b))`.

**Solver complexity:** `+`/`-` are QF_LRA (linear, polynomial-time). `*`/`/` between variables enter QF_NRA (nonlinear, decidable but slower).

Proof: `compileInvExpr_preserves` in `proofs/Proofs/Invariant/Correctness.lean`.

### `logic` — Boolean Connectives (and, or) ✓

```
<comparison> and <comparison>
<comparison> or <comparison>
```

```
invariant bounded_value:
  record.amount >= 0 and record.amount <= 10000
```

SMT-LIB: `(and (>= amount 0.0) (<= amount 10000.0))`

One connective per expression — no mixed `and`/`or` (ambiguous without precedence). No `not` (invert comparisons directly: `>= 0` → `< 0`). No `implies` (deferred to `optional` construct).

Proof: `compileInvBoolExpr_preserves` in `proofs/Proofs/Invariant/Correctness.lean`.

### Per-File Conjunction

**Status:** Implemented ✓

All invariants in a single `.aral` file are automatically AND-ed for joint consistency checking. Separate files are checked independently.

The compiler emits a single SMT-LIB file with:
1. Deduplicated `declare-const` across all invariants
2. A `define-fun` per invariant
3. Named `assert` per invariant (enables unsat core extraction)
4. `(check-sat)` — `sat` = consistent, `unsat` = contradictory

```lisp
(assert (! inv-amount-non-negative :named inv_amount_non_negative))
(assert (! inv-bounded-value :named inv_bounded_value))
(check-sat)
```

### `round` — Rounding Modes

**Status:** Proved correct in Lean 4 ✓

Apply a rounding mode to an expression. Used in function bodies for calculations that require integer results.

**Rounding modes:**

| Mode | Meaning | Lean semantics | SMT-LIB encoding |
|------|---------|----------------|-------------------|
| `floor` | Round toward −∞ | `↑q.floor` | `(to_real (to_int x))` |
| `ceil` | Round toward +∞ | `↑q.ceil` | Conditional on whether `x` is integral |
| `halfUp` | Round half toward +∞ (standard rounding) | `↑(q + 1/2).floor` | `(to_real (to_int (+ x (/ 1.0 2.0))))` |

**In function IR (Aral-fn JSON):**

```json
{ "round": { "expr": <Expr>, "mode": "floor" | "ceil" | "half_up" } }
```

**Lean proof:** `compileInvExpr_preserves` and `compileFunExpr_preserves` each gained one case. The proof shows `evalRound mode (evalExpr env e) = evalRound mode (evalSmtExpr env (compile e))` — rounding is a function applied to the compiled sub-expression.

**Note:** Rounding is meaningful because the semantics use `Rat` (exact rationals). `floor(7/2) = 3` in both Lean and Z3. Z3 can reason through rounding — it proves `floor(value)` preserves non-negativity when `value >= 0`.

### `optional` — Nullable Field Handling (isPresent)

**Status:** Proved correct in Lean 4 ✓

Invariants on optional fields are **implicitly guarded by presence**. Write the invariant as if the field always exists — the compiler wraps it in a presence implication automatically.

```
# percentage is optional on the record. This rule means:
# "when percentage IS present, it must be non-negative."
invariant percentage_non_negative:
  record.percentage >= 0
```

SMT-LIB (generated by the pipeline for optional fields):
```lisp
(declare-const in-has-percentage Real)
(assert (or (= in-has-percentage 0.0) (= in-has-percentage 1.0)))
(assert (=> (not (= in-has-percentage 0.0)) (>= in-percentage 0.0)))
```

**In function IR (Aral-fn JSON):**

Parsers lower null-coalescing expressions (e.g., `x ?? default`) to `ite(isPresent(x), x, default)`:
```json
{
  "ite": {
    "cond": { "isPresent": { "name": "percentage" } },
    "then": { "field": { "name": "percentage" } },
    "else": { "lit": 0 }
  }
}
```

The `optionalFields` array on `FunctionRepr` tells the pipeline which fields are nullable. For each, it generates presence constants (`has-{field}`) constrained to 0 or 1, and guards invariants with `(=> has-field ...)`.

**Design decision:** Invariants bind to types, not states. `percentage >= 0` is a statement about what the value *means* — the system handles when it exists. No new DSL syntax needed.

**Lean proof:** `compileFunBoolExpr_preserves` gained one case for `isPresent`: the presence key resolves through `funEnv` identically to a field reference — `simp` + `split` closes it.

### `sum` — Collection Aggregation

**Status:** Proved correct in Lean 4 (invariant side) ✓. Function side: 2 naming-convention sorry's pending.

Sum a per-item expression across all items in a collection. Two arguments: the collection, and the per-item expression.

```
sum(<root>.<collection>, <per-item expression>)
```

```
invariant total_matches_items:
  record.total == sum(record.entries, amount)

invariant total_with_adjustment:
  record.total == sum(record.entries, quantity * rate) + record.adjustment
```

`sum(record.entries, amount)` reads as: "sum the `amount` field across all `entries`." Field names after the comma are implicitly item-scoped — no arrows, lambdas, or path repetition needed.

**SMT-LIB:** Compiled to `define-fun-rec` with per-item accessor functions:
```lisp
(declare-fun entries-amount (Int) Real)
(declare-const entries-len Int)
(define-fun-rec sum-entries ((i Int)) Real
  (ite (<= i 0) 0.0
    (+ (entries-amount (- i 1)) (sum-entries (- i 1)))))
```

No hardcoded bound — the collection length is symbolic. Z3 explores different lengths during solving.

**Constraints:**
- Per-item expression supports arithmetic only (`quantity * rate` ✓, conditionals ✗)
- All fields after the comma are item fields (no parent fields)
- No nested sums
- Collection must be a simple field reference

**Function verification:** For pass-through collections (items not modified by the function), the output invariant reuses input accessor functions. The sum is a component inside scalar invariants — its value comes from catching functions that break the relationship.

**Lean proof:** `compileInvExpr_preserves` handles `sumExpr` with `congr 1` + `funext` + recursive application — both sides share the same `sumN` structure, so the proof reduces to showing per-item body compilation is correct. Function-side proof has 2 sorry's: the assumption that collection-indexed names never appear in `inputFields` — true by naming convention but needs a formal precondition.

### `each` — Universal Quantifier over Collections

**Status:** ✓ Proved (invariant + function + render + parser)

Assert that a boolean predicate holds for every item in a collection. The boolean analog of `sum` — same recursion scheme, same item environment, different algebra (`Bool/∧/true` instead of `Rat/+/0`).

```
each(<root>.<collection>, <per-item predicate>)
```

```
invariant items_positive:
  record.total == sum(record.items, amount)

invariant all_items_valid:
  each(record.items, value > 0 and value <= 1000)
```

`each(record.items, value > 0)` reads as: "for every item in `items`, `value > 0`." The body is a `BoolExpr` (comparison, `and`/`or`, or nested `each`), not a numeric `Expr`.

**SMT-LIB encoding:**

```smt2
(declare-fun items-value (Int) Real)
(declare-const items-len Int)
(assert (>= items-len 0))
(define-fun-rec each-items ((i Int)) Bool
  (ite (<= i 0) true
    (and (> (items-value (- i 1)) 0.0)
         (each-items (- i 1)))))
```

Same `define-fun-rec` strategy as `sum`. Base case `true`, combiner `and`, return sort `Bool`.

**Constraints:**
- Body is a boolean predicate (comparisons + `and`/`or`)
- Item fields are bare names — scoped by accessor functions
- No `any` keyword yet — expressible as `not each(coll, not P)`
- No `count` keyword — expressible as `sum(coll, 1)`

**Function verification:** Same pass-through model as `sum`. Collections not modified by the function reuse input accessor functions for the output invariant.

**Lean proof:** `compileInvBoolExpr_preserves` handles `eachExpr` with `congr 1` + `funext` + recursive application on `allN` — structurally identical to the `sumExpr` proof in `compileInvExpr_preserves`. Function-side proof uses the same `CollectionSafe` + `CollectionPassthrough` preconditions.

---

## Verification Workflow

```
.aral file
      │
      ▼
┌─────────────┐     ┌───────────────────────────────┐
│  Invariant   │     │  Lean 4 proof:                │
│  Compiler    │◄────│  compilation preserves        │
│  (Lean 4)    │     │  semantics for each construct │
└──────┬──────┘     └───────────────────────────────┘
       │
       ▼
   .smt2 fragment
   (invariant assertions)
       │
       │  + function encoding
       ▼
   complete .smt2 file
       │
       ▼
┌─────────────┐
│     Z3      │──► unsat (proved) / sat (counterexample)
└─────────────┘
```
