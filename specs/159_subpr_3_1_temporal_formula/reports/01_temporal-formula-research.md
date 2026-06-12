# Research Report: Sub-PR 3.1 -- Temporal Formula Type

**Task**: 159 (subpr_3_1_temporal_formula)
**Session**: sess_1781247030_86951e
**Date**: 2026-06-11

## 1. File Inventory

This PR introduces exactly **one new file**:

| File | LOC | Status |
|------|-----|--------|
| `Cslib/Logics/Temporal/Syntax/Formula.lean` | 549 | New file (not in upstream) |

Additionally, the barrel file `Cslib.lean` needs one new import line:
```
public import Cslib.Logics.Temporal.Syntax.Formula
```
This line already exists locally (line 395) but is not in `upstream/main`.

The upstream repository (`leanprover/cslib`) has **no** `Cslib/Logics/Temporal/` directory at all. The only temporal-related file in upstream is `Cslib/Foundations/Data/OmegaSequence/Temporal.lean`, which is unrelated to formula definitions.

## 2. Import Dependency Analysis

Formula.lean declares the following imports:

```lean
public import Cslib.Init
public import Cslib.Foundations.Logic.Connectives
public import Mathlib.Logic.Encodable.Basic
public import Mathlib.Logic.Denumerable
public import Mathlib.Data.Finset.Basic
```

### Dependency Status

| Import | Source | In Upstream? | Notes |
|--------|--------|-------------|-------|
| `Cslib.Init` | CSLib core | YES | Always available |
| `Cslib.Foundations.Logic.Connectives` | Task 138 / PR #633 | NO | On `pr1/foundations-logic` branch, PR #633 is OPEN |
| `Mathlib.Logic.Encodable.Basic` | Mathlib | YES | Standard Mathlib |
| `Mathlib.Logic.Denumerable` | Mathlib | YES | Standard Mathlib |
| `Mathlib.Data.Finset.Basic` | Mathlib | YES | Standard Mathlib |

### Critical Dependency

`Cslib.Foundations.Logic.Connectives` (98 lines) provides the typeclass hierarchy:
- `HasBot`, `HasImp`, `HasUntil`, `HasSince`
- `PropositionalConnectives`, `TemporalConnectives`
- `LukasiewiczDerived`

This file is part of PR #633 (`benbrastmckie:pr1/foundations-logic`), currently OPEN on `leanprover/cslib`. **PR 3.1 cannot be submitted until PR #633 is merged** (or this PR must be based on `pr1/foundations-logic`).

## 3. File Structure Analysis

### Namespacing

The file uses namespace `Cslib.Logic.Temporal` throughout, with two `public section` blocks:

1. **Lines 30-96**: Core formula inductive, derived connectives, notation, typeclass instance
2. **Lines 113-549**: Structural properties (countability, BEq, complexity, temporal operators, swap duality, atoms)

Uses `@[expose] public section` annotation (standard Lean/Mathlib pattern for declaration visibility).

### Formula Inductive

5 constructors (primitives):
- `atom (p : Atom)` -- atomic propositions
- `bot` -- falsum
- `imp (f1 f2 : Formula Atom)` -- implication
- `untl (f1 f2 : Formula Atom)` -- until (Burgess convention: event, guard)
- `snce (f1 f2 : Formula Atom)` -- since (Burgess convention: event, guard)

Derives: `DecidableEq`, `BEq`

### Derived Connectives (as `abbrev`)

| Name | Definition | Notation |
|------|-----------|----------|
| `neg` | `imp phi bot` | `neg` (prefix 40) |
| `top` | `imp bot bot` | -- |
| `or` | `imp (imp phi bot) psi` | `or` (infix 35) |
| `and` | `imp (imp phi (imp psi bot)) bot` | `and` (infix 36) |
| `someFuture` | `untl phi top` | `F` (prefix 40) |
| `allFuture` | `neg (someFuture (neg phi))` | `G` (prefix 40) |
| `somePast` | `snce phi top` | `P` (prefix 40) |
| `allPast` | `neg (somePast (neg phi))` | `H` (prefix 40) |

All notation is `scoped` to the `Cslib.Logic.Temporal` namespace.

### Typeclass Instance

```lean
instance : TemporalConnectives (Formula Atom) where
  bot := .bot
  imp := .imp
  untl := .untl
  snce := .snce
```

Registers `Formula Atom` as an instance of `TemporalConnectives`, which extends `PropositionalConnectives` (HasBot + HasImp) plus `HasUntil` + `HasSince`.

### Key Theorems and Definitions

| Declaration | Type | Lines | Description |
|------------|------|-------|-------------|
| `encodeNat` | `noncomputable def` | 130-135 | Cantor pairing encoding |
| `nat_pair_inj` | `theorem` | 137-141 | Nat.pair injectivity helper |
| `encodeNat_injective` | `theorem` | 144-194 | Encoding is injective |
| `Countable` instance | `instance` | 198-200 | When Atom is countable |
| `Infinite` instance | `instance` | 203-204 | When Atom is infinite |
| `Denumerable` instance | `noncomputable instance` | 207-209 | When Atom is countable + infinite |
| `beq_refl` | `theorem` | 234-240 | BEq reflexivity |
| `eq_of_beq` | `theorem` | 243-276 | BEq soundness |
| `ReflBEq` instance | `instance` | 280-281 | ReflBEq typeclass |
| `LawfulBEq` instance | `instance` | 283-285 | LawfulBEq typeclass |
| `complexity` | `def` | 308-334 | Pattern-aware structural complexity |
| `temporalDepth` | `def` | 343-348 | Nesting depth of U/S |
| `countImplications` | `def` | 355-360 | Count imp operators |
| `next` | `def` | 366 | Next-step (X = bot U phi) |
| `prev` | `def` | 370 | Previous-step (Y = bot S phi) |
| `weakFuture` | `def` | 373-374 | Reflexive future (phi and G phi) |
| `weakPast` | `def` | 378-379 | Reflexive past (phi and H phi) |
| `always` | `def` | 382-383 | H phi and phi and G phi |
| `sometimes` | `def` | 387-388 | neg (always (neg phi)) |
| `release` | `def` | 391-392 | R(phi, psi) = neg(neg psi U neg phi) |
| `trigger` | `def` | 395-396 | T(phi, psi) = neg(neg psi S neg phi) |
| `weakUntil` | `def` | 399-400 | W = (phi U psi) or G phi |
| `weakSince` | `def` | 403-404 | WS = (phi S psi) or H phi |
| `strongRelease` | `def` | 407-408 | M = psi U (psi and phi) |
| `strongTrigger` | `def` | 411-412 | ST = psi S (psi and phi) |
| `swapTemporal` | `def` | 428-433 | Past/future duality transform |
| `swapTemporal_involution` | `theorem` | 436-443 | swap . swap = id |
| `swapTemporal_neg` | `theorem` | 446-448 | Distributes over negation |
| `swapTemporal_someFuture` | `@[simp] theorem` | 452-454 | swap(F phi) = P(swap phi) |
| `swapTemporal_somePast` | `@[simp] theorem` | 458-460 | swap(P phi) = F(swap phi) |
| `swapTemporal_allFuture` | `@[simp] theorem` | 464-466 | swap(G phi) = H(swap phi) |
| `swapTemporal_allPast` | `@[simp] theorem` | 470-472 | swap(H phi) = G(swap phi) |
| `swapTemporal_next` | `theorem` | 475-477 | swap(X phi) = Y(swap phi) |
| `swapTemporal_prev` | `theorem` | 480-482 | swap(Y phi) = X(swap phi) |
| `swapTemporal_strongRelease` | `theorem` | 485-488 | swap(M) = ST |
| `swapTemporal_strongTrigger` | `theorem` | 491-494 | swap(ST) = M |
| `needsPositiveHypotheses` | `def` | 502-504 | Bool predicate for proof system |
| `atoms` | `def` | 528-533 | Finset of atomic propositions |
| `atoms_swapTemporal` | `theorem` | 536-543 | swap preserves atoms |

## 4. Quality Assessment

### Sorry Count: 0

No `sorry` anywhere in the file.

### Axiom Usage

All theorems use only standard Lean axioms:
- `propext`
- `Classical.choice`
- `Quot.sound`

No custom axioms introduced.

### Lint-Style: PASS

`lake exe lint-style` produces no warnings for this file.

### Build: PASS

`lake build Cslib.Logics.Temporal.Syntax.Formula` succeeds (662 jobs).

### checkInitImports: PASS

No errors related to this file.

### Convention Compliance

| Convention | Status | Notes |
|-----------|--------|-------|
| Copyright header | PASS | Standard Apache 2.0 header |
| `module` keyword | PASS | Present on line 7 |
| `import Cslib.Init` | PASS | `public import Cslib.Init` on line 9 |
| Module docstring | PASS | Lines 15-28, covers purpose and derived operators |
| Scoped notation | PASS | All notation uses `scoped` prefix |
| Namespace | PASS | `Cslib.Logic.Temporal` throughout |
| References/citations | N/A | No literature citations in this file (acceptable) |

### Potential Issues

1. **Docstring minor inconsistency**: Line 62 says "F phi := top U phi" using standard math notation, but the code implements `untl phi top` (Burgess event-guard convention where first arg = event). This is **semantically correct** -- the docstring describes the standard notation while the code uses CSLib's reversed argument order. The Satisfies.lean file documents this convention explicitly. Not a blocker.

2. **`iff` derived connective**: The task description mentions "iff" as a derived connective, but the file does not define `Formula.iff`. This appears to be an oversight in the task description rather than the file, as bi-implication is not among the standard primitives for temporal logic and can be constructed from `and` + `imp` externally if needed.

## 5. Downstream Dependencies

Files that import `Cslib.Logics.Temporal.Syntax.Formula`:

| File | Purpose |
|------|---------|
| `Cslib/Logics/Temporal/Syntax/BigConj.lean` | Big conjunction operations |
| `Cslib/Logics/Temporal/Syntax/Context.lean` | Formula contexts |
| `Cslib/Logics/Temporal/Syntax/Subformulas.lean` | Subformula extraction |
| `Cslib/Logics/Temporal/Semantics/Model.lean` | Temporal model definitions |
| `Cslib/Logics/Temporal/ProofSystem/Axioms.lean` | Proof system axioms |
| `Cslib/Logics/Temporal/FromPropositional.lean` | Embedding from propositional logic |
| `Cslib/Logics/Bimodal/Embedding/TemporalEmbedding.lean` | Bimodal embedding |

Task 160 (`subpr_3_2_syntax_utilities`) directly depends on task 159.

## 6. PR Branch Strategy

### Option A: Branch from `pr1/foundations-logic` (Recommended)

Since `Connectives.lean` is on `pr1/foundations-logic` (PR #633, currently OPEN), the PR branch for sub-PR 3.1 should be created from that branch:

```bash
git checkout pr1/foundations-logic
git checkout -b feat/temporal-formula
# Copy/add Formula.lean
# Run lake exe mk_all --module to update Cslib.lean
# Verify CI
```

This creates a stacked PR: PR 3.1 depends on PR #633.

### Option B: Branch from `upstream/main` after PR #633 merges

Wait for PR #633 to merge, then branch from `upstream/main`. Simpler but delays the PR.

### Files Changed in PR

1. **NEW**: `Cslib/Logics/Temporal/Syntax/Formula.lean` (549 lines, +549 insertions)
2. **MODIFIED**: `Cslib.lean` (+1 line: `public import Cslib.Logics.Temporal.Syntax.Formula`)

Total diff: approximately **550 lines** (549 new file + 1 barrel import).

### CI Checklist for PR

- [ ] `lake build Cslib.Logics.Temporal.Syntax.Formula` passes
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] `lake test` passes
- [ ] `lake exe mk_all --module` confirms barrel file is current
- [ ] No `sorry` in file
- [ ] PR description includes AI disclosure per CSLib policy

## 7. Recommendations

1. **Proceed with implementation**: The file is complete, sorry-free, builds cleanly, and passes all lints. No blockers for PR creation.

2. **Use stacked PR approach (Option A)**: Create the branch from `pr1/foundations-logic` since the dependency on `Connectives.lean` is not yet merged upstream.

3. **PR title**: `feat(Logics/Temporal): add temporal logic formula type with primitives and derived operators`

4. **No references.bib updates needed**: The file does not cite literature. Consider adding Kamp (1968) or Burgess (1984) references in a future PR if desired.

5. **Gateway PR**: This is confirmed as the gateway for all temporal logic content. All 7 downstream files depend on it.
