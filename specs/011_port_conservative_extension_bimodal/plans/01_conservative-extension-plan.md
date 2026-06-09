# Implementation Plan: Port Conservative Extension to Bimodal Module

- **Task**: 11 - Port Conservative Extension to Bimodal module
- **Status**: [NOT STARTED]
- **Effort**: 6 hours
- **Dependencies**: Task 4 (ProofSystem) -- merged and available
- **Research Inputs**: specs/011_port_conservative_extension_bimodal/reports/01_conservative-extension-research.md
- **Artifacts**: plans/01_conservative-extension-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

Port 4 files (1,599 lines) from BimodalLogic's `Theories/Bimodal/Metalogic/ConservativeExtension/` to cslib's `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/`. The conservative extension result proves that the BX axiom system extending temporal logic preserves all theorems of the base logic (`lift_derivation_qfree`). The porting is primarily mechanical (namespace/import renaming, axiom name changes) with the main adaptation being polymorphic `Atom` type parameterization requiring `[DecidableEq Atom]` and `[Infinite Atom]` constraints.

### Research Integration

Key findings from the research report:
- **1,599 actual lines** across 4 files with zero sorry occurrences
- **Polymorphic Atom** (HIGH IMPACT): cslib uses `Formula (Atom : Type u)` vs concrete `Atom` in source. Requires adding `[DecidableEq Atom]` throughout, `[Infinite Atom]` in Lifting.lean, and `[Countable Atom]` if deriving Countable
- **Axiom name renames** (MEDIUM IMPACT): `prop_k` -> `imp_k`, `prop_s` -> `imp_s`, `ex_falso` -> `efq` across 5 functions with 42-case match arms each
- **Namespace changes**: `Bimodal.Metalogic.ConservativeExtension` -> `Cslib.Logic.Bimodal.Metalogic.ConservativeExtension`
- **All external dependencies available**: ProofSystem (Task 4) fully merged, Mathlib imports present

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This plan advances the following roadmap item:
- PR 10 (ConservativeExtension, task 11): independent of Tasks 5-9, requires only Task 4 (ProofSystem)

## Goals & Non-Goals

**Goals**:
- Port all 4 ConservativeExtension files to cslib with zero sorry occurrences
- Adapt to cslib's polymorphic `Atom` type with appropriate typeclass constraints
- Rename axiom constructors to match cslib conventions (`imp_k`, `imp_s`, `efq`)
- Produce a clean `lake build` with no errors or warnings
- Follow cslib conventions: Apache 2.0 headers, `module` declarations, namespace patterns

**Non-Goals**:
- Refactoring the proof strategy (port as-is, not rewrite)
- Adding new theorems beyond what exists in the source
- Optimizing the 42-case match arms (mechanical but correct)
- Porting `always`/`sometimes` convenience definitions (unused in theorems)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Polymorphic Atom breaks type inference in complex proofs | M | M | Add explicit type annotations; follow cslib patterns from Derivation.lean |
| 42-case axiom matches have subtle name mismatches | M | L | Systematic find/replace for 3 known renames; verify each match arm compiles |
| `Countable ExtAtom` deriving fails with polymorphic Atom | L | M | Use explicit instance with `[Countable Atom]` constraint |
| Universe polymorphism mismatch in DerivationTree embedding | M | L | Follow existing cslib `Type u` patterns from ProofSystem |
| `Infinite Atom` constraint unavailable in Mathlib | L | L | Standard Mathlib class; verified available |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |

Phases are strictly sequential due to file-level import dependencies.

### Phase 1: Port ExtFormula.lean [COMPLETED]

**Goal**: Create `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/ExtFormula.lean` with the extended formula type parameterized over polymorphic `Atom`.

**Tasks**:
- [ ] Create directory `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/`
- [ ] Add Apache 2.0 copyright header
- [ ] Add `module` declaration and imports (`Cslib.Logics.Bimodal.Syntax.Formula`, `Mathlib.Data.Finset.Basic`)
- [ ] Port `ExtAtom` type alias: `abbrev ExtAtom (Atom : Type u) := Atom ⊕ Unit`
- [ ] Port `freshAtom : ExtAtom Atom := Sum.inr ()`
- [ ] Port `ExtFormula` inductive type mirroring `Formula` but over `ExtAtom Atom`
- [ ] Add `variable {Atom : Type u} [DecidableEq Atom]` section
- [ ] Port `embedAtom : Atom -> ExtAtom Atom := Sum.inl`
- [ ] Port `embedFormula : Formula Atom -> ExtFormula Atom` structural embedding
- [ ] Port all 14 simp lemmas for embedding preservation of derived operators (`neg`, `top`, `and`, `or`, `box`, `diamond`, `untl`, `snce`, `some_future`, `all_future`, `some_past`, `all_past`)
- [ ] Port `embedFormula_injective` theorem
- [ ] Port `fresh_not_in_embedFormula_atoms` freshness lemma
- [ ] Port `ExtFormula.atoms` definition (collecting atoms from extended formulas)
- [ ] Port `Hashable` instance for `ExtAtom` with `[Hashable Atom]` constraint
- [ ] Port `DecidableEq` and `BEq` instances or deriving for `ExtFormula`
- [ ] Verify: `lake build Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.ExtFormula`

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/ExtFormula.lean` - create new file (~353 lines)

**Verification**:
- `lake build Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.ExtFormula` passes
- `grep -c sorry ExtFormula.lean` returns 0

---

### Phase 2: Port ExtDerivation.lean [NOT STARTED]

**Goal**: Create `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/ExtDerivation.lean` with extended axiom schemas, derivation trees, and embedding functions.

**Tasks**:
- [ ] Add Apache 2.0 copyright header
- [ ] Add `module` declaration and imports (`ExtFormula`, `Cslib.Logics.Bimodal.ProofSystem.Derivation`)
- [ ] Port `ExtContext` type alias (`List (ExtFormula Atom)`)
- [ ] Port `ExtAxiom` inductive type with 42 constructors, applying renames: `prop_k` -> `imp_k`, `prop_s` -> `imp_s`, `ex_falso` -> `efq`
- [ ] Port `ExtAxiom.minFrameClass` function (42-case match)
- [ ] Port `ExtDerivationTree` inductive type with 7 inference rules, matching cslib's `DerivationTree` pattern
- [ ] Port `embedAxiom : Axiom phi -> ExtAxiom (embedFormula phi)` function (42-case match with 3 name renames)
- [ ] Port `embedDerivation : DerivationTree fc L phi -> ExtDerivationTree fc (L.map embedFormula) (embedFormula phi)` (7 recursive cases)
- [ ] Verify: `lake build Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.ExtDerivation`

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/ExtDerivation.lean` - create new file (~287 lines)

**Verification**:
- `lake build Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.ExtDerivation` passes
- `grep -c sorry ExtDerivation.lean` returns 0
- All 42 `ExtAxiom` constructors match cslib's `Axiom` constructors (with 3 renames)

---

### Phase 3: Port Substitution.lean [NOT STARTED]

**Goal**: Create `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/Substitution.lean` with the substitution `sigma[q -> bot]` and closure properties.

**Tasks**:
- [ ] Add Apache 2.0 copyright header
- [ ] Add `module` declaration and imports (`ExtFormula`, `ExtDerivation`)
- [ ] Port `substFormula : ExtFormula Atom -> ExtFormula Atom` replacing `freshAtom` with `bot`
- [ ] Port simp lemmas for `substFormula` on each `ExtFormula` constructor
- [ ] Port `substAxiom` function: axiom schema closure under substitution (42-case match with 3 name renames)
- [ ] Port `substFormula_preserves_qfree` -- q-free formulas are fixed points of substitution
- [ ] Port `substFormula_of_embedded` -- embedded formulas are unchanged by substitution
- [ ] Port `substFormula_idempotent` -- substitution is idempotent
- [ ] Port `substFormula_map_embedded` -- substitution distributes over map of embedded formulas
- [ ] Verify: `lake build Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.Substitution`

**Timing**: 1 hour

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/Substitution.lean` - create new file (~262 lines)

**Verification**:
- `lake build Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.Substitution` passes
- `grep -c sorry Substitution.lean` returns 0

---

### Phase 4: Port Lifting.lean [NOT STARTED]

**Goal**: Create `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/Lifting.lean` with the main conservative extension theorem `lift_derivation_qfree`. This is the most complex file (697 lines) and requires `[Infinite Atom]` for the freshness argument.

**Tasks**:
- [ ] Add Apache 2.0 copyright header
- [ ] Add `module` declaration and imports (`Substitution`, plus Mathlib's `Infinite` and `Finset`)
- [ ] Add `variable {Atom : Type u} [DecidableEq Atom] [Infinite Atom]`
- [ ] Port `unembedFormula : ExtFormula Atom -> Formula Atom` partial inverse
- [ ] Port `unembed_embed` left-inverse property
- [ ] Port `embed_unembed_qfree` right-inverse for q-free formulas
- [ ] Port `substFreshWith (a : Atom) : ExtFormula Atom -> ExtFormula Atom` parameterized substitution
- [ ] Port simp lemmas for `substFreshWith`
- [ ] Port `substAxiomFresh` -- axiom closure under parameterized substitution (42-case match with 3 name renames)
- [ ] Port `unembedAxiom` -- convert `ExtAxiom` to base `Axiom` (42-case match with 3 name renames)
- [ ] Port `collectDerivInl` -- collect all `Sum.inl` atoms from derivation tree
- [ ] Port `liftDerivationWith` -- combined lifting function (7 recursive cases)
- [ ] Port `exists_fresh_atom` -- uses `Infinite.exists_notMem_finset` (requires `[Infinite Atom]`)
- [ ] Port `lift_derivation_qfree` -- main conservative extension theorem
- [ ] Verify: `lake build Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.Lifting`

**Timing**: 1.5 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/Lifting.lean` - create new file (~697 lines)

**Verification**:
- `lake build Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.Lifting` passes
- `grep -c sorry Lifting.lean` returns 0
- `lift_derivation_qfree` type-checks with the expected signature

---

### Phase 5: Final Verification and Cleanup [NOT STARTED]

**Goal**: Run full project build, verify zero sorry occurrences, run linter, and clean up unused imports.

**Tasks**:
- [ ] Run `lake build` (full project) to verify no regressions
- [ ] Run `grep -r sorry Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/` to confirm zero sorry
- [ ] Run `lake exe shake` on each file to remove unused imports
- [ ] Set `set_option linter.all true` in each file and fix any warnings
- [ ] Verify all 4 files have Apache 2.0 copyright headers
- [ ] Verify `module` declarations are present where appropriate
- [ ] Create summary artifact

**Timing**: 0.5 hours

**Depends on**: 4

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/ExtFormula.lean` - linter fixes
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/ExtDerivation.lean` - linter fixes
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/Substitution.lean` - linter fixes
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/Lifting.lean` - linter fixes

**Verification**:
- `lake build` passes with zero errors
- Zero sorry occurrences across all 4 files
- Linter produces no warnings
- All copyright headers present

## Testing & Validation

- [ ] `lake build Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.ExtFormula` passes
- [ ] `lake build Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.ExtDerivation` passes
- [ ] `lake build Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.Substitution` passes
- [ ] `lake build Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.Lifting` passes
- [ ] `lake build` (full project) passes with zero errors
- [ ] `grep -r sorry Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/` returns nothing
- [ ] All 3 axiom name renames applied consistently across 5 functions with 42-case match arms
- [ ] `lift_derivation_qfree` type-checks with polymorphic `Atom` and `[Infinite Atom]` constraint

## Artifacts & Outputs

- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/ExtFormula.lean` (~353 lines)
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/ExtDerivation.lean` (~287 lines)
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/Substitution.lean` (~262 lines)
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/Lifting.lean` (~697 lines)
- `specs/011_port_conservative_extension_bimodal/plans/01_conservative-extension-plan.md` (this file)
- `specs/011_port_conservative_extension_bimodal/summaries/01_conservative-extension-summary.md` (post-implementation)

## Rollback/Contingency

If implementation fails at any phase:
- Delete the partially created `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/` directory
- The porting is additive (new files only), so no existing cslib code is modified
- If polymorphic Atom causes intractable type inference issues, fall back to explicit type ascriptions or consider using `variable (Atom : Type u)` at the file level instead of section variables
- If `Infinite Atom` is unavailable or problematic, the `exists_fresh_atom` lemma can be stated as a hypothesis rather than derived from the typeclass
