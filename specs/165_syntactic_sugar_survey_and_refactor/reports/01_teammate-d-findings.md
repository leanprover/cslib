# Teammate D Findings: Strategic Analysis and Missing Notation

## Part 1: Missing Notation

### 1.1 Biconditional `↔` Missing from PL

**Gap found**: `Cslib/Logics/Propositional/Defs.lean` defines `Proposition.iff` (line 76) but declares NO scoped `↔` notation. Both Modal (`Basic.lean:87`) and Temporal (`Formula.lean:101`) have `↔` notation. PL uses `.iff` 10+ times in `NaturalDeduction/DerivedRules.lean` and `HilbertDerivedRules.lean`.

**Fix**: Add `@[inherit_doc] scoped infix:30 " ↔ " => Proposition.iff` after line 86 in `Defs.lean`.

### 1.2 Diamond `◇` — Fully Covered

All logics with modal operators have `◇` notation:
- Modal: `Basic.lean:86`
- Bimodal: `Formula.lean:86`
- PL and Temporal don't need it (no box primitive).

### 1.3 Top `⊤` — Partially Covered

PL has `instance : Top (Proposition Atom) := ⟨.top⟩` (line 80) and Temporal has `instance : Top (Formula Atom) := ⟨.top⟩` (line 117). The `⊤` notation from Lean's `Top` typeclass should work in expressions. **However**, Bimodal does NOT have a `Top` instance. Should add `instance : Top (Formula Atom) := ⟨.top⟩` to `Bimodal/Syntax/Formula.lean`.

Similarly, `Bot` instances exist for PL (line 79), Temporal (line 116), and Modal. **Bimodal should verify it has `Bot` instance.**

### 1.4 Foundations/Logic Level — No Notation (By Design)

`Cslib/Foundations/Logic/Theorems/` uses `HasImp.imp`/`HasBot.bot` 732 times. These are typeclass-polymorphic methods — they work over *any* formula type satisfying `HasBot`/`HasImp`.

**Recommendation**: DO NOT add notation at the Foundations level. Reasons:
1. These names already serve as the "notation" for the polymorphic layer — they're unambiguous
2. Adding generic `→` notation for `HasImp.imp` would conflict with Lean's function arrow
3. Adding `⊥` via `Bot` instance for the polymorphic `F` type would require `[Bot F]` constraint everywhere
4. The Foundations layer is intentionally lower-level — explicit typeclass calls are clearer here
5. Files like `Combinators.lean` and `BigConj.lean` need to manipulate these at a syntactic level

**Exception**: If a `LukasiewiczDerived` instance is ever activated (currently intentionally uninstantiated per docstring), it could bring abbreviations. But that's a separate design decision.

### 1.5 Temporal `△` and `▽` — Fully Covered

Both Temporal (`Formula.lean:446,449`, precedence 80) and Bimodal (`Formula.lean:102,103`, precedence 40) have `△`/`▽` notation. The precedence difference (80 vs 40) is a minor inconsistency but shouldn't cause issues.

### 1.6 Bimodal — Fully Covered

`Bimodal/Syntax/Formula.lean` declares notation for all operators: `¬ ∧ ∨ → □ ◇ U S F G P H △ ▽`. No gaps found.

**Note on conflicts**: Bimodal uses single-letter prefixes `F`, `G`, `P`, `H` while Temporal uses bold Unicode `𝐅`, `𝐆`, `𝐏`, `𝐇`. Three files explicitly avoid opening the Bimodal/Temporal namespace to prevent notation conflicts with these single-letter identifiers:
- `Bimodal/Theorems/Perpetuity/Helpers.lean`
- `Bimodal/ProofSystem/Instances.lean`
- `Temporal/ProofSystem/Instances.lean`

These files CANNOT use notation and must keep raw constructors. This is an important constraint for the refactoring.

## Part 2: Upstream Alignment

### 2.1 Upstream CSLib Style

The upstream `leanprover/cslib` main branch (Modal/Basic.lean) uses notation **in definitions**:
```lean
def Proposition.or (φ₁ φ₂) := ¬(¬φ₁ ∧ ¬φ₂)    -- uses ¬ and ∧ notation
def Proposition.impl (φ₁ φ₂) := ¬φ₁ ∨ φ₂         -- uses ¬ and ∨ notation
def Proposition.box (φ) := ¬◇¬φ                   -- uses ¬ and ◇ notation
```

The local fork's definitions use raw constructors:
```lean
abbrev Proposition.or (φ₁ φ₂) := .imp (.imp φ₁ .bot) φ₂
abbrev Proposition.and (φ₁ φ₂) := .imp (.imp φ₁ (.imp φ₂ .bot)) .bot
```

This is because the local fork changed the primitives to `{bot, imp, box}` (Lukasiewicz style), so derived connectives like `or` are defined in terms of primitives *before* their own notation exists. This is correct: you can't use `∧` notation in the definition of `∧` itself. The reviewer's comment applies to *usage sites*, not definition sites.

### 2.2 No Formal Style Guide

There is no explicit style guide in cslib for notation vs constructors. However, the reviewer comment on PR #633 establishes the implicit convention: **use notation wherever it's available and unambiguous**.

### 2.3 Relationship to FormalizedFormalLogic/Foundation

The project cites Foundation for the connective typeclass hierarchy design. Foundation uses a similar pattern where derived connectives use notation and only primitive-level code uses raw constructors.

### 2.4 Open PRs to Coordinate With

Three open PRs touch files relevant to this refactoring:
1. **PR #633** (`pr1/foundations-logic`): Foundations/Logic + Propositional — 39 files. This is the PR with the review comment. The syntactic sugar fixes should be applied to this PR's files first.
2. **PR #635** (`refactor/proposition-lukasiewicz`): Refactoring Proposition to bot/imp primitives.
3. **PR #637** (`refactor/modal-primitives`): Refactoring Modal to bot/imp/box primitives.

PRs #635 and #637 are actively changing Modal primitives from `{not, and, diamond}` to `{bot, imp, box}`. The syntactic sugar refactoring for Modal should wait until those land, or be coordinated with them.

## Part 3: Refactoring Strategy

### 3.1 PR Strategy

**Recommendation**: Split into 4-5 PRs, ordered by dependency and risk:

| PR | Scope | Files | Rationale |
|----|-------|-------|-----------|
| 1 | PL notation fix + PL sugar | ~22 | Add missing `↔`, fix PR #633 reviewer comment, low risk |
| 2 | Modal sugar | ~57 | Depends on PRs #635/#637 landing first |
| 3 | Temporal sugar | ~38 | Independent, can go in parallel with #1 |
| 4 | Bimodal sugar | ~127 | Largest, highest risk, most impactful |
| 5 | Bimodal `Bot`/`Top` instances | ~2 | Small, adds missing typeclass instances |

**Alternative**: Single PR if the reviewer prefers "one big cleanup". But this is risky for a 260-file project.

### 3.2 Refactoring Order Within Each PR

1. **Add missing notation/instances** first (e.g., PL `↔`, Bimodal `Bot`/`Top`)
2. **Definition files** (Defs.lean, Basic.lean, Formula.lean) — but only usage within body, not where notation is being defined
3. **ProofSystem files** — axioms, derivation, instances
4. **Metalogic files** — soundness, completeness, MCS
5. **Semantics files** — satisfaction, Kripke models
6. **NaturalDeduction/Embedding files** — most downstream

### 3.3 Files to NOT Touch

1. **Pattern match arms**: `| .imp A B =>`, `| .bot =>` etc. MUST stay as raw constructors
2. **Notation definition sites**: The `abbrev` definitions of derived connectives use primitives by necessity
3. **Files with namespace conflict warnings**: `Perpetuity/Helpers.lean`, `ProofSystem/Instances.lean` (both Temporal and Bimodal) explicitly avoid opening the namespace
4. **Foundations/Logic/**: All 732 `HasImp.imp`/`HasBot.bot` usages should stay as-is (polymorphic layer)

### 3.4 New Notation Timing

Add missing notation **in the same PR** as the sugar refactoring for that logic level. Adding `↔` to PL and then using it in the same PR is clean and keeps the change atomic.

## Part 4: Bimodal Survey

### Scale Assessment

Bimodal is the largest target with 127 files and massive raw constructor usage:

| Constructor | Count | Notation | Replaceable (est.) |
|-------------|-------|----------|-------------------|
| `.imp` | 1906 | `→` | ~1800 (95%) |
| `.bot` | 757 | `⊥` | ~700 (93%) |
| `.neg` | 2430 | `¬` | ~2400 (99%) |
| `.and` | 1216 | `∧` | ~1200 (99%) |
| `.or` | 425 | `∨` | ~420 (99%) |
| `.box` | 513 | `□` | ~500 (97%) |
| `.diamond` | 92 | `◇` | ~90 (98%) |
| `.untl` | 1217 | `U` | ~1100 (90%) |
| `.snce` | 983 | `S` | ~900 (92%) |
| `.someFuture` | 342 | `F` | ~300 (88%) |
| `.allFuture` | 416 | `G` | ~370 (89%) |
| `.somePast` | 278 | `P` | ~250 (90%) |
| `.allPast` | 359 | `H` | ~320 (89%) |
| `.always` | 32 | `△` | ~30 (94%) |
| `.sometimes` | 11 | `▽` | ~10 (91%) |

**Total estimated replaceable**: ~10,390 out of ~10,977 instances

### Key Risk Areas in Bimodal

1. **`F`/`G`/`P`/`H` vs identifiers**: Single-letter notation can clash with variable names. Files that avoid namespace opening (3 identified) cannot use this notation.
2. **Precedence**: `U` and `S` at precedence 40 may cause ambiguity with `→` at precedence 30 in complex expressions.
3. **`unfold` dependencies**: Some proofs use `unfold Formula.neg` or `unfold Formula.and` — if notation is used in the goal, the `unfold` target changes. This needs case-by-case verification.
4. **`simp` lemmas**: Some `simp` lemmas are keyed on constructor patterns. Changing to notation should be transparent (since notation is just sugar), but regression testing is essential.

## Confidence Level

**High** for the analysis of missing notation and strategic recommendations.
**Medium** for the replacement count estimates (actual numbers depend on context-specific pattern match detection).
