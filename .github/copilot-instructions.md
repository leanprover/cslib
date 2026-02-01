# Copilot Instructions for CSLib

## Repository Overview

**CSLib** is the Lean library for Computer Science (CS), formalising CS theories and tools in the Lean programming language. It provides APIs for formal verification, certified software, and connecting different CS developments.

- **Language:** Lean 4
- **Build System:** Lake
- **Primary Dependency:** Mathlib (leanprover-community/mathlib4)
- **Project Type:** Lean library

## Build & Validation Commands

**Always run commands from the repository root.** The project uses `lake`.

### Essential Commands (in order of typical usage)

| Command | Purpose | When to Use |
|---------|---------|-------------|
| `lake build` | Build the library | After any code change |
| `lake build --wfail --iofail` | Build with CI strictness (fails on warnings) | **Always use before committing** |
| `lake test` | Run all tests (builds CslibTests + checks init imports) | After changes to verify correctness |
| `lake lint` | Run environment linters (Batteries/Mathlib) | Before committing |
| `lake exe lint-style` | Run text-based style linters | Before committing |
| `lake exe mk_all --module --check` | Verify Cslib.lean imports all modules | After adding new files |
| `lake exe mk_all --module` | Auto-update Cslib.lean imports | After adding new files |

### Full CI Validation Sequence

Run these commands **in order** to replicate CI checks locally:

```bash
lake build --wfail --iofail
lake exe mk_all --module --check
lake test
lake lint
lake exe lint-style
```

### Additional Commands

| Command | Purpose |
|---------|---------|
| `lake clean` | Remove build outputs (use if build state is corrupted) |
| `lake update` | Update dependencies (rarely needed) |
| `lake exe lint-style --fix` | Auto-fix style errors |
| `lake exe shake Cslib` | Check for minimized imports |

## Project Structure

```
/
├── Cslib.lean           # Root module (imports all library files)
├── CslibTests.lean      # Root test module
├── CONTRIBUTING.md      # Contribution guidelines
├── lakefile.toml        # Lake configuration (linters, dependencies)
├── lean-toolchain       # Lean version specification
├── lake-manifest.json   # Locked dependency versions
├── Cslib/               # Main library source
│   ├── Init.lean        # Must be imported by all Cslib modules
│   ├── Foundations/     # General-purpose definitions (semantics, data types, etc.)
│   ├── Computability/   # Automata and computability theory
│   ├── Languages/       # Programming language formalisations (e.g., Calculus of Communicating Systems, Lambda Calculus)
│   └── Logics/          # Logic formalisations (e.g., Linear Logic, Hennessy-Milner Logic)
├── CslibTests/          # Test files
├── scripts/             # Build and maintenance scripts
│   ├── noshake.json     # Import exceptions for shake tool
│   └── nolints.json     # Lint exceptions
└── .github/workflows/   # CI workflows
```

## Critical Requirements

### 1. All Cslib Modules Must Import Cslib.Init
Every file in `Cslib/` must transitively import `Cslib/Init.lean`. This sets up default linters and tactics. The test suite verifies this.

**Exceptions** (documented in `scripts/CheckInitImports.lean`):
- `Cslib.Foundations.Lint.Basic` (circular dependency)
- `Cslib.Init` itself

### 2. New Files Must Be Added to Cslib.lean
When creating a new `.lean` file in `Cslib/`, add its import to `Cslib.lean`. Run:
```bash
lake exe mk_all --module
```

### 3. PR Title Convention
PR titles **must** follow the format: `type(scope): description`

Valid types: `feat`, `fix`, `doc`, `style`, `refactor`, `test`, `chore`, `perf`

Examples:
- `feat(LTS): add weak bisimulation`
- `fix(Lambda): correct substitution lemma`
- `doc: improve README`

### 4. File Headers
Every `.lean` file must have a copyright header:
```lean
/-
Copyright (c) $YEAR $AUTHOR_NAME. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: $LIST_OF_AUTHORS
-/
```

## Code Style

- Follow everything written in /CONTRIBUTING.md
- Follow [Mathlib style guide](https://leanprover-community.github.io/contribute/style.html)
- Use domain-specific variable names (e.g., `State` for state types, `μ` for transition labels)
- Keep proofs readable; golfing is welcome if proofs remain clear
- Use existing typeclasses for common concepts (transitions, reductions)
- Use `module` keyword at the start of files with `public import` statements

## Linter Configuration

Linters are configured in `lakefile.toml`.

## Common Patterns

### Creating a New Module
1. Create file in appropriate `Cslib/` subdirectory
2. Add `import Cslib.Init` (or import a module that imports it)
3. Run `lake exe mk_all --module`
4. Run `lake build --wfail --iofail`
5. Run `lake test` to verify init imports

### Adding Tests
1. Create or modify a file in `CslibTests/`
2. Add import to `CslibTests.lean` if new file
3. Run `lake test`

## Trust These Instructions

Only search for additional information if:
- A command fails with an unexpected error
- You need details about a specific module's API
- The instructions appear incomplete for your specific task
