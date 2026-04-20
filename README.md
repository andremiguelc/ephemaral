# ephemaral

Formally verified business logic verification. Checks that your functions preserve data invariants, with the verification compiler proved correct in Lean 4.

## Quick Start

### 1. Install

**Z3** (SMT solver): `brew install z3` (macOS) / `apt install z3` (Ubuntu) / [GitHub releases](https://github.com/Z3Prover/z3/releases)

**ephemaral binary**: download from [GitHub Releases](https://github.com/andremiguelc/ephemaral/releases/latest):

```bash
mkdir -p .ephemaral/bin
# macOS (Apple Silicon)
curl -L -o .ephemaral/bin/ephemaral https://github.com/andremiguelc/ephemaral/releases/latest/download/ephemaral-macos-arm64
# Linux (x86_64)
curl -L -o .ephemaral/bin/ephemaral https://github.com/andremiguelc/ephemaral/releases/latest/download/ephemaral-linux-x86_64
chmod +x .ephemaral/bin/ephemaral
```

### 2. Write an invariant

Create `.ephemaral/rules/record.aral`:

```
# The computed value must be non-negative
invariant value_non_negative:
  record.value >= 0

# The total must equal base plus adjustment
invariant total_correct:
  record.total == record.base + record.adjustment
```

### 3. Run verification

```bash
# Verify a function against invariants
.ephemaral/bin/ephemaral .ephemaral/parsed/function.aral-fn.json .ephemaral/rules/record.aral

# Compile invariants to SMT-LIB (inspect what the compiler produces)
.ephemaral/bin/ephemaral .ephemaral/rules/record.aral
```

Output: `VERIFIED` (safe for all inputs) or `COUNTEREXAMPLE FOUND` (with exact failing values and a diagnosis).

## How It Works

```
Source code  ──→  Parser (unproved)  ──→  .aral-fn.json
                                            │
                                     [proof boundary]
                                            │
.aral files ──→  Invariant compiler ──→  SMT-LIB query  ──→  Z3  ──→  Result
                  (proved in Lean 4)     (proved correct)
```

Everything below the proof boundary is machine-checked in Lean 4. The Lean proofs guarantee that if the function representation is faithful, the verification question sent to Z3 is semantics-preserving.

## Writing Invariants

Invariants are written in `.aral` files — a small language for expressing what must always be true about data. The identifier before the dot binds the invariant to a type (`record.value` binds to type `Record`).

**Common patterns:**

```
# Non-negativity
invariant value_non_negative:
  record.value >= 0

# Bounded range
invariant value_bounded:
  record.value >= 0 and record.value <= 10000

# Relationship between fields
invariant total_correct:
  record.total == record.base + record.adjustment

# Collection sum
invariant total_matches_items:
  record.total == sum(record.items, value)

# Per-item constraint
invariant items_valid:
  each(record.items, value > 0 and value <= 1000)
```

See [dsl/LANGUAGE.md](dsl/LANGUAGE.md) for the full language specification and formal grammar.

## The Aral-fn Format

Functions are represented as `.aral-fn.json` files — a JSON format describing what a function computes. This is the **proof boundary**: everything before it (parsers) is unproved, everything after it (compilation, verification) is proved correct in Lean 4.

Produce `.aral-fn.json` files using a language parser (see [ts-to-ephemaral](https://github.com/andremiguelc/ts-to-ephemaral) for TypeScript).

See [ir/README.md](ir/README.md) for the format specification and [ir/aral-fn.schema.json](ir/aral-fn.schema.json) for the JSON Schema.

## Project Setup

```
.ephemaral/
├── bin/
│   └── ephemaral          # binary (gitignored)
├── parsed/                # .aral-fn.json files (gitignored, regenerable)
└── rules/                 # .aral invariant files (checked in, one per type)
    └── <type>.aral
```

Add to `.gitignore`:
```
.ephemaral/bin/
.ephemaral/parsed/
```

## Building & Testing

### Build from source

Requires **Lean 4** (v4.28.0) via [elan](https://github.com/leanprover/elan).

```bash
cd proofs && lake build ephemaral
# Binary at: .lake/build/bin/ephemaral
```

### Running tests

```bash
python3 -m venv .venv && source .venv/bin/activate
pip install pytest jsonschema
pytest proofs/tests/ -v    # compiler + diagnostics
pytest ir/tests/ -v        # schema validation
```

### CI and releases

Every push runs CI (`.github/workflows/ci.yml`) — builds the Lean project and confirms all proofs compile with zero sorry's. Releases are triggered by pushing a version tag (`git tag v<version> && git push --tags`).

## License

Apache-2.0 — see [LICENSE](LICENSE).
