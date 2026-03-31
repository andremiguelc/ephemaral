# ephemaral

Formally verified business logic verification. Checks that your functions preserve data invariants, with the verification compiler proved correct in Lean 4.

The Lean proofs guarantee that if the function representation is faithful, the verification question sent to Z3 is semantics-preserving.

## Quick start

### Prerequisites

- **Lean 4** (v4.28.0) — install via [elan](https://github.com/leanprover/elan) (macOS / Linux / Windows)
- **Z3** — `brew install z3` (macOS) / `apt install z3` (Ubuntu) / [GitHub releases](https://github.com/Z3Prover/z3/releases) (Windows / all platforms)

### Build

```bash
git clone https://github.com/andremiguelc/ephemaral.git
cd ephemaral/proofs
lake build ephemaral
```

The binary lands at `proofs/.lake/build/bin/ephemaral`.

## Usage

**Verify a function against invariants:**

```bash
ephemaral <function.aral-fn.json> <inv1.aral> [inv2.aral ...]
```

The tool reads a function representation (`.aral-fn.json`) and one or more invariant files (`.aral`). It compiles both into an SMT-LIB query, runs Z3, and reports either `VERIFIED` or a counterexample with exact failing values.

**Compile invariants to SMT-LIB:**

```bash
ephemaral <inv.aral> [inv2.aral ...]
```

When given only `.aral` files (no `.aral-fn.json`), outputs the compiled SMT-LIB to stdout.

## Writing invariants

Invariants are written in `.aral` files — a small language for expressing what must always be true about data. The root prefix binds the invariant to a type. The tool checks: if the input satisfies all invariants, does the output also satisfy them?

See [dsl/LANGUAGE.md](dsl/LANGUAGE.md) for the full language specification.

## The Aral-fn format

Functions are represented as `.aral-fn.json` files — a JSON format describing what a function computes. This is the **proof boundary**: everything before it (parsers, LLMs) is unproved. Everything after it (compilation, SMT-LIB generation, verification) is proved correct in Lean 4.

You can produce `.aral-fn.json` files using a deterministic parser (like [ts-to-ephemaral](https://github.com/andremiguelc/ts-to-ephemaral) for TypeScript) or hand-craft them. Any tool that produces valid JSON works.

See [ir/README.md](ir/README.md) for the format specification and [ir/aral-fn.schema.json](ir/aral-fn.schema.json) for the JSON Schema.

## What can it verify?

Supported constructs in function bodies:

- Arithmetic (add, subtract, multiply, divide)
- Conditional expressions (if-then-else from guard clauses and ternary operators)
- Division with rounding (floor, ceil, half-up)
- Typed parameter preconditions (invariants on parameter types applied automatically)
- Null-safe field access (nullable fields with defaults)
- Collection sums (reduce-to-sum patterns)

This covers approximately 78% of CRUD functions across 6 surveyed production codebases.

## Architecture

The verification pipeline:

```
Source code  ──→  Parser (unproved)  ──→  Aral-fn JSON
                                            │
                                     [proof boundary]
                                            │
.aral files ──→  Invariant compiler ──→  SMT-LIB query  ──→  Z3  ──→  Result
                  (proved correct)       (proved correct)
```

**Inside the proof boundary (machine-checked in Lean 4):**
- Invariant parser, compiler, and renderer
- Function compiler and pipeline routing
- SMT-LIB assembly and format preservation

**Outside the proof boundary (empirically validated):**
- Source code parsers (any language)
- JSON deserialization
- Z3 solver (trusted external tool)
- Diagnostic message formatting

The Lean proofs are in [proofs/Proofs/](proofs/Proofs/).

## Running tests

```bash
# Set up Python environment
python3 -m venv .venv && source .venv/bin/activate
pip install pytest jsonschema

# Compiler + diagnostic tests
pytest proofs/tests/ -v

# Schema validation tests
pytest ir/tests/ -v
```

## License

Apache-2.0 — see [LICENSE](LICENSE).
