# Implementation Plan: Refactor Propositional Hilbert to Intuitionistic Base

- **Task**: 88 - Refactor propositional Hilbert system to intuitionistic base with uniform extension architecture
- **Status**: [NOT STARTED]
- **Effort**: 6 hours
- **Dependencies**: None
- **Research Inputs**: specs/088_refactor_propositional_hilbert_intuitionistic_base/reports/01_team-research.md
- **Artifacts**: plans/01_intuitionistic-base-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: formal
- **Lean Intent**: true

## Overview

Refactor the propositional Hilbert-style proof system from a single `PropositionalHilbert` bundle to a three-level typeclass hierarchy: `MinimalHilbert` (K, S, MP), `IntuitionisticHilbert` (+ EFQ), `ClassicalHilbert` (+ Peirce). This mirrors the existing ND hierarchy (MPL/IPL/CPL) and enables maximum theorem reuse at each strength level. The blast radius is approximately 15 files (4.5% of the codebase). The definition of done is a passing `lake build` with all existing theorems and instances intact under the new hierarchy.

### Research Integration

Team research (4 teammates) confirmed:
- All four researchers converge on the three-level hierarchy as the recommended architecture
- Theorem stratification is clean: Combinators.lean is purely minimal; Core.lean splits into intuitionistic (efq_axiom only) and classical; Connectives.lean is classical except contrapose_imp, contraposition, and iff_intro which are minimal
- The Lukasiewicz conjunction encoding makes lce_imp/rce_imp inherently classical (known limitation)
- FormalizedFormalLogic/Foundation validates this approach at scale (1,378 commits, 20+ logics)
- Modal/Temporal/Bimodal logics should keep extending ClassicalHilbert for now
- HasAxiomDNE is dead code -- clean up in this task
- MCS framework and deduction theorems are unaffected

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances the Foundations/Logic module infrastructure. It does not directly map to a specific ROADMAP.md item but improves the proof system architecture that underpins all logic modules.

## Goals & Non-Goals

**Goals**:
- Define `MinimalHilbert`, `IntuitionisticHilbert`, and `ClassicalHilbert` typeclasses in ProofSystem.lean
- Rename `PropositionalHilbert` to `ClassicalHilbert` with a temporary backward-compatibility alias
- Weaken Combinators.lean theorems from `[PropositionalHilbert S]` to `[MinimalHilbert S]`
- Correctly stratify Core.lean and Connectives.lean theorems to their minimal required strength level
- Update all downstream instance files (Propositional, Modal, Temporal, Bimodal)
- Add tag types `Propositional.HilbertMin` and `Propositional.HilbertInt`
- Clean up `HasAxiomDNE` dead code
- Achieve a passing `lake build` with no regressions

**Non-Goals**:
- Refactoring axiom inductives (sum types or nested embedding) -- deferred to follow-up task
- Adding primitive `HasAnd`/`HasOr` connective typeclasses for richer intuitionistic reasoning
- Moving modal/temporal logics to intuitionistic base (separate future task)
- Changing the Lukasiewicz encoding of conjunction/disjunction

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Typeclass resolution failures after hierarchy change | H | M | Introduce classes incrementally; build after each phase |
| Theorems classified at wrong level (compile failure) | M | L | Research audit is thorough; verify with lean_goal before committing |
| Backward-compatibility alias causes diamond inheritance | M | L | Use `abbrev` or `@[reducible] def` for alias; remove in final phase |
| Instance files have implicit PropositionalHilbert assumptions beyond extends | M | L | grep for all PropositionalHilbert references; update systematically |
| BigConj theorems use lce_imp/rce_imp (classical) | L | H | Leave BigConj at ClassicalHilbert for now; document as known limitation |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2, 3 |
| 4 | 5 | 4 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Define New Typeclasses and Tag Types [COMPLETED]

**Goal**: Introduce the three-level hierarchy in ProofSystem.lean without breaking any existing code.

**Tasks**:
- [ ] Add `MinimalHilbert` class extending `ModusPonens`, `HasAxiomImplyK`, `HasAxiomImplyS`
- [ ] Add `IntuitionisticHilbert` class extending `MinimalHilbert`, `HasAxiomEFQ`
- [ ] Rename `PropositionalHilbert` to `ClassicalHilbert` extending `IntuitionisticHilbert`, `HasAxiomPeirce`
- [ ] Add backward-compatibility alias: `abbrev PropositionalHilbert := ClassicalHilbert`
- [ ] Add tag types `Propositional.HilbertMin` and `Propositional.HilbertInt`
- [ ] Remove `HasAxiomDNE` dead code declaration (or add `-- deprecated` comment if keeping for future equivalence proof)
- [ ] Update module docstring to reflect three-level architecture
- [ ] Run `lake build Cslib.Foundations.Logic.ProofSystem` to verify

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/ProofSystem.lean` -- split bundled class, add tag types

**Verification**:
- `lake build Cslib.Foundations.Logic.ProofSystem` passes
- All downstream files still compile via the backward-compatibility alias

---

### Phase 2: Weaken Combinators.lean to MinimalHilbert [COMPLETED]

**Goal**: Change all theorems in Combinators.lean from `[PropositionalHilbert S]` to `[MinimalHilbert S]`, proving they need only K, S, and MP.

**Tasks**:
- [ ] Change the `variable` declaration from `[PropositionalHilbert S (F := F)]` to `[MinimalHilbert S (F := F)]`
- [ ] Update module docstring from "generic over [PropositionalHilbert S]" to "generic over [MinimalHilbert S]"
- [ ] Verify all theorems compile: `imp_trans`, `identity`, `b_combinator`, `flip`, `app1`, `app2`, `pairing`, `dni`, `combine_imp_conj`, `combine_imp_conj_3`
- [ ] Run `lake build Cslib.Foundations.Logic.Theorems.Combinators` to verify

**Timing**: 30 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Foundations/Logic/Theorems/Combinators.lean` -- change typeclass constraint

**Verification**:
- All theorems compile with `[MinimalHilbert S]`
- Downstream files still compile (they have `PropositionalHilbert` which extends `MinimalHilbert`)

---

### Phase 3: Stratify Core.lean and Connectives.lean [COMPLETED]

**Goal**: Classify theorems in Core.lean and Connectives.lean to their minimal required strength level (minimal, intuitionistic, or classical).

**Tasks**:
- [ ] In Core.lean, restructure into three sections:
  - Minimal section (`[MinimalHilbert S]`): `lem` (it is `identity` on negated formula -- purely minimal)
  - Intuitionistic section (`[IntuitionisticHilbert S]`): `efq_axiom`
  - Classical section (`[ClassicalHilbert S]`): `peirce_axiom`, `double_negation`, `rcp`, `lce_imp`, `rce_imp` *(deviation: altered -- `raa` and `efq_neg` moved to Intuitionistic section since they only require EFQ, not Peirce)*
- [ ] Update the outer `variable` block and add section-scoped variable declarations for each level
- [ ] In Connectives.lean, restructure into two sections:
  - Minimal section (`[MinimalHilbert S]`): `contrapose_imp`, `contraposition`, `iff_intro`, `iff_neg_intro`
  - Classical section (`[ClassicalHilbert S]`): `classical_merge`, `contrapose_iff`, `demorgan_conj_neg_forward`, `demorgan_conj_neg_backward`, `demorgan_conj_neg`, `demorgan_disj_neg_forward`, `demorgan_disj_neg_backward`, `demorgan_disj_neg`
- [ ] Update module docstrings to reflect stratification
- [ ] Run `lake build Cslib.Foundations.Logic.Theorems.Propositional` to verify

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Foundations/Logic/Theorems/Propositional/Core.lean` -- split into sections by strength level
- `Cslib/Foundations/Logic/Theorems/Propositional/Connectives.lean` -- split into sections by strength level

**Verification**:
- All theorems compile at their correct strength level
- No theorem requires a stronger level than assigned
- `lake build Cslib.Foundations.Logic.Theorems.Propositional` passes

---

### Phase 4: Update Downstream Extensions and BigConj [COMPLETED]

**Goal**: Update all downstream files that reference `PropositionalHilbert` to use the appropriate new class name, and update bundled class extends chains.

**Tasks**:
- [ ] Update `ModalHilbert` to extend `ClassicalHilbert` (instead of `PropositionalHilbert`)
- [ ] Update `TemporalBXHilbert` to extend `ClassicalHilbert` (instead of `PropositionalHilbert`)
- [ ] (BimodalTMHilbert extends ModalS5Hilbert and TemporalBXHilbert, which both extend ClassicalHilbert -- verify no changes needed)
- [ ] Update `Cslib/Logics/Propositional/ProofSystem/Instances.lean`: change `PropositionalHilbert` instance to `ClassicalHilbert` instance
- [ ] Update `Cslib/Logics/Temporal/ProofSystem/Instances.lean`: change `PropositionalHilbert` instance to `ClassicalHilbert` instance
- [ ] Update `Cslib/Logics/Bimodal/ProofSystem/Instances.lean`: change `PropositionalHilbert` instance to `ClassicalHilbert` instance
- [ ] Update `Cslib/Foundations/Logic/Theorems/BigConj.lean`: change `[PropositionalHilbert S]` to `[ClassicalHilbert S]` (BigConj uses lce_imp/rce_imp which are classical)
- [ ] Update `Cslib/Foundations/Logic/Theorems/Modal/Basic.lean`: change `[ModalHilbert S]` doc references if any mention PropositionalHilbert
- [ ] Update `Cslib/Foundations/Logic/Theorems.lean` (aggregator): update doc references
- [ ] Check `Cslib/Logics/Temporal/Metalogic/PropositionalHelpers.lean` for PropositionalHilbert references
- [ ] Remove the backward-compatibility alias `PropositionalHilbert` from ProofSystem.lean
- [ ] Run `lake build` (full project) to verify no remaining references break

**Timing**: 2 hours

**Depends on**: 2, 3

**Files to modify**:
- `Cslib/Foundations/Logic/ProofSystem.lean` -- update ModalHilbert, TemporalBXHilbert extends; remove alias
- `Cslib/Logics/Propositional/ProofSystem/Instances.lean` -- rename instance
- `Cslib/Logics/Temporal/ProofSystem/Instances.lean` -- rename instance
- `Cslib/Logics/Bimodal/ProofSystem/Instances.lean` -- rename instance
- `Cslib/Foundations/Logic/Theorems/BigConj.lean` -- change typeclass constraint
- `Cslib/Foundations/Logic/Theorems/Modal/Basic.lean` -- update doc references
- `Cslib/Foundations/Logic/Theorems/Modal/S5.lean` -- update doc references if needed
- `Cslib/Foundations/Logic/Theorems.lean` -- update doc references
- `Cslib/Logics/Temporal/Metalogic/PropositionalHelpers.lean` -- update references if needed

**Verification**:
- `lake build` (full project build) passes with zero errors
- No file contains `PropositionalHilbert` (verify with grep)
- All downstream instance files compile

---

### Phase 5: Final Verification and Documentation [COMPLETED]

**Goal**: Verify the complete refactoring, ensure no regressions, and update documentation.

**Tasks**:
- [ ] Run full `lake build` and confirm zero errors
- [ ] Run `grep -rn "PropositionalHilbert" --include="*.lean" Cslib/` to confirm no residual references
- [ ] Verify that `lean_verify` on key theorems shows no sorry usage
- [ ] Review the module docstring in ProofSystem.lean for accuracy
- [ ] Confirm the hierarchy: MinimalHilbert -> IntuitionisticHilbert -> ClassicalHilbert -> ModalHilbert -> ModalS5Hilbert and ClassicalHilbert -> TemporalBXHilbert -> BimodalTMHilbert

**Timing**: 1 hour

**Depends on**: 4

**Files to modify**:
- None (verification only, potential minor doc fixes)

**Verification**:
- `lake build` passes
- `grep -rn "PropositionalHilbert" --include="*.lean" Cslib/` returns zero results (excluding comments/docs explaining the rename)
- Hierarchy is correct and documented

## Testing & Validation

- [ ] `lake build` passes with zero errors after all phases
- [ ] All existing theorem names are preserved (no API breakage)
- [ ] Combinators.lean compiles with `[MinimalHilbert S]` only
- [ ] Core.lean sections compile at their declared strength levels
- [ ] No `PropositionalHilbert` references remain in source code
- [ ] Tag types `Propositional.HilbertMin` and `Propositional.HilbertInt` exist
- [ ] `HasAxiomDNE` is cleaned up (removed or deprecated)

## Artifacts & Outputs

- `Cslib/Foundations/Logic/ProofSystem.lean` -- three-level hierarchy, new tag types
- `Cslib/Foundations/Logic/Theorems/Combinators.lean` -- weakened to MinimalHilbert
- `Cslib/Foundations/Logic/Theorems/Propositional/Core.lean` -- stratified sections
- `Cslib/Foundations/Logic/Theorems/Propositional/Connectives.lean` -- stratified sections
- All downstream instance files updated
- plans/01_intuitionistic-base-plan.md (this file)
- summaries/01_intuitionistic-base-summary.md (upon completion)

## Rollback/Contingency

If the refactoring causes unforeseen issues:
1. All changes are in the typeclass layer and theorem variable declarations; the underlying proof logic is unchanged
2. Reverting to a single `ClassicalHilbert` (equivalent to old `PropositionalHilbert`) restores the original behavior
3. Git revert to the pre-refactoring commit provides a clean rollback
4. If specific theorems resist re-stratification, leave them at `ClassicalHilbert` and document as future work
