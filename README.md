# ephemaral

Formally verified business logic verification. Checks that your functions preserve data invariants, with the verification compiler proved correct in Lean 4.

The Lean proofs guarantee that if the function representation is faithful, the verification question sent to Z3 is semantics-preserving.

## Install

### Prerequisites

- **Z3** — `brew install z3` (macOS) / `apt install z3` (Ubuntu) / [GitHub releases](https://github.com/Z3Prover/z3/releases) (all platforms)

### Option A: Download a pre-built binary

Grab the latest binary for your platform from [GitHub Releases](https://github.com/andremiguelc/ephemaral/releases/latest) and place it in your project's `.ephemaral/bin/` directory:

```bash
mkdir -p .ephemaral/bin

# macOS (Apple Silicon)
curl -L -o .ephemaral/bin/ephemaral https://github.com/andremiguelc/ephemaral/releases/latest/download/ephemaral-macos-arm64

# Linux (x86_64)
curl -L -o .ephemaral/bin/ephemaral https://github.com/andremiguelc/ephemaral/releases/latest/download/ephemaral-linux-x86_64

chmod +x .ephemaral/bin/ephemaral
```

Add `.ephemaral/bin/` to your `.gitignore`.

### Option B: Build from source

Requires **Lean 4** (v4.28.0) via [elan](https://github.com/leanprover/elan).

```bash
git clone https://github.com/andremiguelc/ephemaral.git
cd ephemaral/proofs
lake build ephemaral
# Binary at: proofs/.lake/build/bin/ephemaral
```

### The .ephemaral directory

When using ephemaral in a project, the `.ephemaral/` directory holds all verification artifacts:

```
.ephemaral/
├── bin/
│   └── ephemaral               # binary (gitignored)
├── parsed/                     # parser output (gitignored, regenerable)
│   └── function.aral-fn.json
└── rules/                      # invariant files (checked in)
    └── inv1.aral
```

- **bin/** — the ephemaral binary. Gitignore this.
- **parsed/** — `.aral-fn.json` files produced by parsers. Gitignore this (regenerable from source).
- **rules/** — `.aral` invariant files. Check these in — they're your business rules.

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
- Collection predicates (universal quantifier — every item satisfies a condition)

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

## CI and Releases

### Continuous integration

Every push runs the CI workflow (`.github/workflows/ci.yml`), which builds the full Lean project and confirms all proofs compile with zero sorry's.

### Releasing a new version

Releases are triggered by pushing a version tag. The release workflow (`.github/workflows/release.yml`) builds binaries for Linux x86_64 and macOS arm64 and attaches them to a GitHub Release.

```bash
# 1. Merge your branch into main
git checkout main
git merge v0.1.1

# 2. Tag the release
git tag v0.1.1

# 3. Push (tag triggers the release workflow)
git push origin main --tags
```

GitHub Actions will:
1. Build the `ephemaral` executable on both platforms via `lake build`
2. Create a GitHub Release with auto-generated release notes
3. Attach the binaries (`ephemaral-linux-x86_64`, `ephemaral-macos-arm64`)

Users can then download the binary from the [Releases page](https://github.com/andremiguelc/ephemaral/releases).

## License

Apache-2.0 — see [LICENSE](LICENSE).
