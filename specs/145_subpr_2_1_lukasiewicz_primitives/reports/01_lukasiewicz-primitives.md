# Research Report: Sub-PR 2.1 Lukasiewicz Primitive Refactoring

## Summary

This PR refactors Modal/Basic.lean from `{atom, not, and, diamond}` primitives to `{atom, bot, imp, box}` primitives (Lukasiewicz convention), updates Modal/Denotation.lean for the new primitives, and replaces the upstream Modal/LogicalEquivalence.lean with a fork-native version. All `grind`-based proofs in Basic.lean and Denotation.lean are replaced with explicit term-mode proofs.

The fork's `main` branch already contains the completed refactoring. The work for this PR is to create a clean branch from `upstream/main` and cherry-pick/adapt the relevant changes for upstream submission.

## Current State Analysis

### Upstream (`upstream/main`) -- What exists today

**Basic.lean** (upstream): 4 primitive constructors
- `atom (p : Atom)` -- atomic proposition
- `not (phi : Proposition Atom)` -- negation (primitive)
- `and (phi1 phi2 : Proposition Atom)` -- conjunction (primitive)
- `diamond (phi : Proposition Atom)` -- possibility (primitive)

Derived connectives (as `def`, not `abbrev`):
- `or` := `not(not phi1 and not phi2)`
- `impl` := `not phi1 or phi2` (note: named `impl`, not `imp`)
- `iff` := `(phi1 impl phi2) and (phi2 impl phi1)`
- `box` := `not (diamond (not phi))` (derived!)

`Satisfies` matches on `{atom, not, and, diamond}`:
- `.atom p => m.v w p`
- `.not phi => not (Satisfies m w phi)`
- `.and phi1 phi2 => Satisfies m w phi1 and Satisfies m w phi2`
- `.diamond phi => exists w', m.r w w' and Satisfies m w' phi`

All axiom validity proofs (K, dual, T, B, 4, 5, D and their converses) use `grind`.

**Denotation.lean** (upstream): Matches on `{atom, not, and, diamond}`
- `.atom p => {w | m.v w p}`
- `.not phi => complement`
- `.and phi1 phi2 => intersection`
- `.diamond phi => {w | exists w', ...}`

All proofs use `grind` (3 theorems).

**LogicalEquivalence.lean** (upstream): 132 lines
- Defines `Proposition.Equiv S phi1 phi2` for model class `S`
- Defines `Proposition.Context` with constructors `{hole, not, andL, andR, diamond}` (matching old primitives)
- Proves `IsEquiv` and `Congruence` instances using `grind`
- Defines `Satisfies.Context` for judgemental contexts
- Instantiates `LogicalEquivalence` typeclass from `Cslib.Foundations.Logic.LogicalEquivalence`
- All proofs use `grind`

### Fork (`main`) -- What the refactoring produced

**Basic.lean** (fork): 4 primitive constructors (changed)
- `atom (p : Atom)` -- unchanged
- `bot` -- NEW (replaces `not`)
- `imp (phi1 phi2 : Proposition Atom)` -- NEW (replaces `and`)
- `box (phi : Proposition Atom)` -- NEW, now primitive (was derived)

Derived connectives (as `abbrev`, not `def`):
- `neg phi := imp phi bot` (negation)
- `top := imp bot bot` (verum)
- `or phi1 phi2 := imp (imp phi1 bot) phi2` (disjunction)
- `and phi1 phi2 := imp (imp phi1 (imp phi2 bot)) bot` (conjunction)
- `diamond phi := neg (box (neg phi))` (possibility, now derived)
- `iff phi1 phi2 := and (imp phi1 phi2) (imp phi2 phi1)` (bi-implication)

New additions in fork Basic.lean not in upstream:
- `import Cslib.Foundations.Logic.Connectives` (from task 138)
- `ModalConnectives` instance (from task 138)
- `instance : Bot (Proposition Atom) := <bot>` (new)
- `Satisfies.neg_iff`, `Satisfies.diamond_iff`, `Satisfies.and_iff`, `Satisfies.or_iff` -- explicit satisfaction theorems for derived connectives
- All axiom proofs rewritten as explicit term-mode proofs (no `grind`)

**Denotation.lean** (fork): Matches on `{atom, bot, imp, box}`
- All proofs rewritten with explicit structure (no `grind`)

**LogicalEquivalence.lean** (fork): 84 lines, completely rewritten
- Defines `Proposition.Context` with constructors `{hole, impL, impR, box}` (matching new primitives)
- Defines `LogicallyEquivalent` directly (not via typeclass)
- Proves `congruence` theorem
- Does NOT import `Cslib.Foundations.Logic.LogicalEquivalence` (no typeclass dependency)
- Does NOT instantiate any typeclass
- No `grind` usage

## Diff Analysis

The `git diff upstream/main` for the three files shows:
- **Basic.lean**: 303 lines changed (insertions + deletions)
- **Denotation.lean**: 52 lines changed
- **LogicalEquivalence.lean**: 176 lines changed
- **Total diffstat**: 317 insertions, 214 deletions = 531 diff lines

This exceeds the stated ~440 lines. The overcount comes from the fork's Basic.lean containing additional content not needed for this PR:
1. `import Cslib.Foundations.Logic.Connectives` -- depends on PR 1.1.1 (task 138)
2. `ModalConnectives` instance (lines 89-93) -- depends on PR 1.1.1
3. `DecidableEq, BEq` deriving on Proposition -- optional, may stay or be deferred

### What to include in the PR branch

The PR should contain only the primitive refactoring itself, without the Connectives dependency:

**Include**:
1. Primitive change: `{atom, not, and, diamond}` -> `{atom, bot, imp, box}`
2. Derived connectives as `abbrev`s (neg, top, or, and, diamond, iff)
3. New `Satisfies` definition matching new primitives
4. New explicit satisfaction theorems for derived connectives (neg_iff, diamond_iff, and_iff, or_iff)
5. All axiom validity proofs rewritten without `grind`
6. Denotation.lean updated for new primitives, no `grind`
7. LogicalEquivalence.lean rewritten for new Context constructors

**Exclude** (from later PRs):
1. `import Cslib.Foundations.Logic.Connectives` -- from task 138
2. `ModalConnectives` instance -- from task 138
3. `instance : Bot (Proposition Atom)` -- depends on Connectives

## grind Usage Inventory

### Basic.lean -- Proofs using `grind` as a tactic (upstream)

| Theorem | Line | grind usage | Replacement in fork |
|---------|------|-------------|---------------------|
| `not_satisfies` | - | `by grind` (main proof) | Renamed to `neg_satisfies`, uses `Satisfies.neg_iff` |
| `Satisfies.or_iff_or` | - | `by grind [Proposition.or]` | Uses `Satisfies.or_iff` |
| `Satisfies.impl_iff_impl` | - | `by grind [Proposition.impl]` | `Iff.rfl` (imp is now primitive) |
| `Satisfies.iff_iff_iff` | - | `by grind` | Removed (iff uses and_iff + imp directly) |
| `Satisfies.box_iff_forall` | - | `by grind [Proposition.box]` | `Iff.rfl` (box is now primitive) |
| `TheoryEq.ext_iff` | - | `by grind` | `by grind` (STILL uses grind in fork) |
| `satisfies_theory` | - | `by grind` | `by grind` (STILL uses grind in fork) |
| `not_theoryEq_satisfies` | - | `by grind [=_ not_satisfies]` | `by grind [=_ neg_satisfies]` (STILL uses grind) |
| `Satisfies.k` | - | `by grind` | Explicit: `change Satisfies ... ; simp only [Satisfies]; intro ...` |
| `Satisfies.dual` | - | `by grind only [...]` | Explicit: `change ...; rw [and_iff]; exact <id, id>` |
| `Satisfies.t` | - | `by grind [...]` | Explicit: `change ...; intro ...; rw [diamond_iff]; exact ...` |
| `Satisfies.t_refl` | - | `by grind` | Explicit term-mode proof |
| `Satisfies.t_box_diamond` | - | `by grind` | Explicit constructor/intro proof |
| `Satisfies.b` | - | `by grind` | Explicit: `change ...; intro ...; rw [diamond_iff]; exact ...` |
| `Satisfies.b_symm` | - | `by grind` | Explicit term-mode proof |
| `Satisfies.four` | - | via `simp + rcases` (partial grind) | Explicit: `change ...; rw [diamond_iff]; ...` |
| `Satisfies.four_trans` | - | `by grind` | Explicit term-mode proof |
| `Satisfies.five` | - | `by grind` | Explicit: `change ...; intro ...; rw [diamond_iff] at ...` |
| `Satisfies.five_rightEuclidean` | - | `by grind` | Explicit term-mode proof |
| `Satisfies.d` | - | `by grind` | Explicit: `change ...; intro ...; rw [diamond_iff]; ...` |
| `Satisfies.d_serial` | - | `by grind` | Explicit term-mode proof |

Note: Three theory-related proofs (`TheoryEq.ext_iff`, `satisfies_theory`, `not_theoryEq_satisfies`) STILL use `grind` in the fork. The task description says "replaces all grind-based proofs" -- these three may need explicit replacements for the PR or may be acceptable since they are `grind` on set membership (not on the changed Proposition constructors).

### Basic.lean -- `grind` as attributes (retained)

The following `@[scoped grind ...]` attributes are retained in the fork and should be kept:
- `@[scoped grind]` on `Satisfies` definition
- `@[simp, scoped grind =]` on `Satisfies.Bundled`
- `@[scoped grind =]` on `derivation_def`, `neg_satisfies`, `or_iff_or`, `impl_iff_impl`, `box_iff_forall`, `diamond_iff_exists`, `and_iff_and`
- `@[scoped grind ->]` on `satisfies_theory`
- `@[simp, scoped grind =]` on `Proposition.valid` and `logic`

These are fine -- they register lemmas for `grind` but the proofs themselves don't rely on `grind`.

### Denotation.lean -- grind usage (upstream)

| Theorem | grind usage | Replacement |
|---------|-------------|-------------|
| `satisfies_mem_denotation` | `by induction ... <;> grind` | Explicit case-by-case with `simp only`, `constructor`, `rcases` |
| `not_denotation` -> `neg_denotation` | `by grind [...]` | Explicit `simp only` + `push_neg` + case split |
| `theoryEq_denotation_eq` | `by Iff.intro <;> grind [...]` | Explicit constructor with `satisfies_mem_denotation` |

### LogicalEquivalence.lean -- grind usage (upstream)

All proofs in the upstream file use `grind`. The fork version is a complete rewrite with no `grind`.

## Import Dependency Analysis

### Modal/Basic.lean imports

Upstream imports:
```
public import Cslib.Init
public import Cslib.Foundations.Logic.InferenceSystem
public import Mathlib.Data.Set.Basic
public import Mathlib.Order.Defs.Unbundled
public import Cslib.Foundations.Data.Relation
public import Mathlib.Logic.Nonempty
```

Fork adds:
```
public import Cslib.Foundations.Logic.Connectives  -- EXCLUDE from this PR
```

### Who imports Basic.lean?

Files that `import Cslib.Logics.Modal.Basic`:
1. `Modal/Denotation.lean` -- in this PR scope
2. `Modal/LogicalEquivalence.lean` -- in this PR scope
3. `Modal/Cube.lean` -- NOT in PR scope, but uses `Satisfies.k`, `Satisfies.t` by name
4. `Modal/FromPropositional.lean` -- NOT in PR scope, references `.atom`, `.bot`, `.imp` constructors
5. `Modal/Metalogic/DerivationTree.lean` -- NOT in PR scope, references `Proposition` type
6. `Bimodal/Embedding/ModalEmbedding.lean` -- NOT in PR scope

### Who imports Denotation.lean?

No other file imports `Modal/Denotation.lean`.

### Who imports LogicalEquivalence.lean?

Only `Cslib.lean` (the barrel file) imports `Modal/LogicalEquivalence.lean`. No other source file depends on it.

### Who references LogicalEquivalence definitions?

No file outside `LogicalEquivalence.lean` references `Proposition.Context` (the modal version), `Context.fill`, `LogicallyEquivalent`, or `Proposition.Equiv`. These are purely self-contained.

## Risk Assessment

### Low Risk

1. **Denotation.lean**: Only imported by the barrel. Changes are mechanical (match new constructors, explicit proofs). No downstream breakage.

2. **LogicalEquivalence.lean**: Only imported by the barrel. Complete rewrite is safe since no other file references its definitions.

3. **grind attribute annotations**: Retained as-is. These do not affect proof correctness.

### Medium Risk

4. **Cube.lean references**: `Cube.lean` calls `Satisfies.k` and `Satisfies.t` in proofs (lines 131 and 136). These theorems are preserved with the same names and types in the fork, so no breakage. However, the Cube.lean proofs themselves use `grind` with these lemmas, and the changed Proposition structure could affect grind's ability to close these goals. **Mitigation**: Cube.lean is not in scope for this PR, but a build test would catch issues.

5. **FromPropositional.lean references**: This file maps PL constructors to Modal constructors (`.atom`, `.bot`, `.imp`). Since the fork already has these constructors, no breakage. But upstream `FromPropositional.lean` does not exist (it was added by the fork), so this is not a concern for the PR.

### Dependency Concern

6. **Connectives import**: The fork's Basic.lean imports `Cslib.Foundations.Logic.Connectives` which does not exist upstream. This import and the `ModalConnectives` instance must be **excluded** from Sub-PR 2.1. The `Connectives.lean` file is part of Sub-PR 1.1.1 (task 138). If Sub-PR 2.1 is meant to be independent of PR 1.x, this import cannot be included.

   **Resolution**: The PR branch should be created from `upstream/main` and should NOT include:
   - `import Cslib.Foundations.Logic.Connectives`
   - The `ModalConnectives` instance
   - `instance : Bot (Proposition Atom)`

## Implementation Strategy

### Approach: Branch from upstream/main

1. Create branch `refactor/modal-lukasiewicz` from `upstream/main`
2. Apply the refactoring to Basic.lean:
   - Change Proposition inductive constructors
   - Add derived connective `abbrev`s
   - Rewrite Satisfies to match new constructors
   - Add satisfaction theorems for derived connectives (neg_iff, diamond_iff, and_iff, or_iff)
   - Rewrite all axiom validity proofs as explicit term-mode
   - Optionally add `DecidableEq, BEq` deriving
3. Apply the refactoring to Denotation.lean:
   - Update denotation function for new constructors
   - Replace grind proofs with explicit ones
4. Rewrite LogicalEquivalence.lean:
   - New Context constructors matching `{imp, box}` (no `not`, `and`, `diamond`)
   - Rewrite proofs
5. Update Cslib.lean barrel if needed
6. Verify with `lake build`, CI pipeline

### Diff Budget

With the Connectives exclusion, the expected diff should be closer to the ~440 target:
- Basic.lean: ~250 lines (excluding Connectives import + ModalConnectives instance)
- Denotation.lean: ~52 lines
- LogicalEquivalence.lean: ~176 lines
- Total: ~478 lines (still slightly over 440 but within reasonable bounds)

### Theorems that still use grind

Three theorems in Basic.lean still use `grind` as a tactic (not just as an attribute):
1. `TheoryEq.ext_iff` -- `by grind` (set extensionality)
2. `satisfies_theory` -- `by grind` (set membership)
3. `not_theoryEq_satisfies` -- `by grind [=_ neg_satisfies]` (set membership + negation)

These grind usages operate on set-level reasoning, not on Proposition structure, so they are compatible with the new primitives. The task description says to replace "all grind-based proofs" but these three are benign. Decision needed: replace them too (cleaner, matches task description) or keep them (less diff, still correct).

**Recommendation**: Replace all three with explicit proofs to fully satisfy the task description. The replacements are straightforward:
- `TheoryEq.ext_iff`: `Set.ext_iff` or direct `Iff.intro` with `Set.mem_setOf_eq`
- `satisfies_theory`: direct `Set.mem_setOf_eq` or `id`
- `not_theoryEq_satisfies`: unfold + classical reasoning

## Cslib.lean Barrel Impact

The barrel file `Cslib.lean` imports `Cslib.Logics.Modal.LogicalEquivalence` (line 285). Since LogicalEquivalence.lean is being replaced (not deleted), this import remains valid. No barrel changes needed.

## PR Description Draft

**Title**: `refactor(Modal): Lukasiewicz primitive convention for modal propositions`

**Body**:
Refactors Modal/Basic.lean from `{atom, not, and, diamond}` primitives to `{atom, bot, imp, box}`, following the Lukasiewicz convention used in standard modal logic references (Blackburn, de Rijke, Venema 2001; Chagrov, Zakharyaschev 1997).

Key changes:
- Proposition inductive: `not`/`and`/`diamond` replaced by `bot`/`imp`/`box`
- Negation, conjunction, disjunction, diamond as `abbrev` derived connectives
- All `grind`-based proofs replaced with explicit term-mode proofs
- Denotation updated for new primitives
- LogicalEquivalence rewritten with new Context constructors

This aligns the modal logic formalization with the propositional convention established upstream and enables cleaner interaction with Hilbert-style proof systems.
