# Implementation Plan: Port Frame Conditions and Soundness to Bimodal Module

- **Task**: 6 - Port Frame Conditions and Soundness to Bimodal module
- **Status**: [NOT STARTED]
- **Effort**: 12 hours
- **Dependencies**: Tasks 3 (Semantics), 4 (ProofSystem) -- both merged
- **Research Inputs**: specs/006_port_frame_conditions_soundness_bimodal/reports/01_frame-soundness-research.md
- **Artifacts**: plans/01_frame-soundness-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

Port 10 source files (4,680 lines) from BimodalLogic to cslib, establishing the soundness of the BX/TM axiom system with respect to linear, dense, and discrete frame classes. The port spans two target directories: `Cslib/Logics/Bimodal/FrameConditions/` (frame condition typeclasses and parameterized validity/soundness) and `Cslib/Logics/Bimodal/Metalogic/Soundness/` (core soundness lemmas and main soundness theorem). All proofs are sorry-free in the source. The primary porting adaptations are: universe-polymorphic Atom parameterization (`Formula` -> `Formula Atom`), frame variable rename (`F` -> `ℱ`), model parameterization (`TaskModel F` -> `TaskModel Atom ℱ`), namespace change to `Cslib.Logic.Bimodal`, and import path updates.

### Research Integration

The research report (01_frame-soundness-research.md) provides a complete source file inventory (10 files, 4,680 lines), internal and external dependency maps, a build order respecting dependencies, and risk assessment per file. Key findings integrated:

- Zero sorries in all source files -- all proofs are complete
- Build order must follow: FrameClass -> Core -> DenseValidity -> FrameClassVariants -> Soundness -> FC/Validity -> FC/Soundness -> FC/Compatibility -> thin wrappers
- Highest risk files are DenseValidity.lean (1,338 lines, 42-case axiom swap proof), FrameClassVariants.lean (971 lines, discrete validity with succ/pred recursion), and Metalogic/Soundness.lean (1,372 lines, main soundness with 42+ axiom cases)
- Universe level concern: source `is_valid` uses `Type*` but cslib `valid` uses `Type` explicitly to avoid issues; ported `is_valid` may need `Type` constraint
- FrameClass.lean has Mathlib-only imports (no BimodalLogic dependencies) so it ports independently

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Port all 10 source files with zero sorries and zero build errors
- Establish `Cslib/Logics/Bimodal/FrameConditions/` directory with frame condition typeclasses and parameterized soundness
- Establish `Cslib/Logics/Bimodal/Metalogic/Soundness/` directory with core soundness lemmas and main soundness theorem
- Maintain the `FrameClass` / `minFrameClass` gating pattern from the source
- Pass `lake build`, linter checks, and sorry verification on each phase

**Non-Goals**:
- Standalone temporal frame conditions (moved to Task 22)
- Completeness proofs (Task 8, depends on this task)
- Refactoring proof strategies -- port proofs as faithfully as possible
- Performance optimization of long proofs

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Universe level mismatch in `is_valid` with `Atom : Type u` | H | M | Follow cslib pattern: use `Type` (not `Type*`) for `D` parameter; test early in Phase 2 |
| 42-case axiom proofs break due to Atom parameterization | H | L | Atom appears only in type signatures, not proof bodies; proofs manipulate formulas structurally |
| Typeclass resolution failures in FrameClass instances | M | M | Verify `haveI` patterns in Validity.lean compile; add explicit instance hints if needed |
| `termination_by d.height` fails with parameterized types | M | L | Height is a Nat computation independent of Atom; should work unchanged |
| Import transitivity changes between BimodalLogic and cslib | L | M | Verify each import compiles; add explicit Mathlib imports where transitivity breaks |
| Axiom constructor name changes between source and cslib Axioms.lean | M | L | Cross-reference research report Section 3 with cslib Axioms.lean constructors |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3 | 2 |
| 3 | 4 | 3 |
| 4 | 5 | 4 |
| 5 | 6 | 1, 5 |
| 6 | 7 | 5, 6 |
| 7 | 8 | 7 |
| 8 | 9 | 5 |
| 9 | 10 | 8, 9 |

Phases within the same wave can execute in parallel.

---

### Phase 1: FrameConditions/FrameClass.lean [COMPLETED]

**Goal**: Port the frame condition typeclasses (LinearTemporalFrame, SerialFrame, DenseTemporalFrame, DiscreteTemporalFrame) and Int instances. This file has Mathlib-only imports and no BimodalLogic dependencies.

**Tasks**:
- [ ] Create `Cslib/Logics/Bimodal/FrameConditions/FrameClass.lean` with Apache 2.0 header
- [ ] Copy source content from `BimodalLogic/Theories/Bimodal/FrameConditions/FrameClass.lean`
- [ ] Update namespace to `Cslib.Logic.Bimodal`
- [ ] Verify Mathlib imports compile (AddCommGroup, LinearOrder, SuccOrder, PredOrder, etc.)
- [ ] Check that `Mathlib.Algebra.Order.Ring.Rat` import is still needed; remove if unused
- [ ] Run `lake build Cslib.Logics.Bimodal.FrameConditions.FrameClass`

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Bimodal/FrameConditions/FrameClass.lean` - create (220 lines)

**Verification**:
- `lake build Cslib.Logics.Bimodal.FrameConditions.FrameClass` passes with zero errors
- `grep -c sorry Cslib/Logics/Bimodal/FrameConditions/FrameClass.lean` returns 0

---

### Phase 2: Metalogic/Soundness/Core.lean [COMPLETED]

**Goal**: Port the core soundness definitions (`is_valid`, `valid_at_triple`, `truth_at_swap_swap` involution lemma). This establishes the local validity definition used by all subsequent soundness files.

**Tasks**:
- [ ] Create `Cslib/Logics/Bimodal/Metalogic/Soundness/Core.lean` with Apache 2.0 header
- [ ] Copy source content from `BimodalLogic/Theories/Bimodal/Metalogic/SoundnessLemmas/Core.lean`
- [ ] Update imports: `Bimodal.Semantics.Truth` -> `Cslib.Logics.Bimodal.Semantics.Truth`, etc.
- [ ] Update namespace to `Cslib.Logic.Bimodal`
- [ ] Add `variable {Atom : Type*}` and parameterize `Formula` -> `Formula Atom`
- [ ] Adapt `is_valid` definition: use `D : Type` (not `Type*`) for universe safety, following cslib `valid` pattern
- [ ] Rename frame variables `F` -> `ℱ` and `TaskModel F` -> `TaskModel Atom ℱ`
- [ ] Run `lake build Cslib.Logics.Bimodal.Metalogic.Soundness.Core`

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Soundness/Core.lean` - create (106 lines)

**Verification**:
- `lake build Cslib.Logics.Bimodal.Metalogic.Soundness.Core` passes with zero errors
- `grep -c sorry Cslib/Logics/Bimodal/Metalogic/Soundness/Core.lean` returns 0
- `is_valid` type-checks with `Formula Atom` parameter

---

### Phase 3: Metalogic/Soundness/DenseValidity.lean [COMPLETED]

**Goal**: Port the dense validity proofs -- all swap_axiom_*_valid theorems (42 cases), `axiom_swap_valid`, `axiom_locally_valid`, preservation lemmas, and the combined `derivable_valid_and_swap_valid` theorem with `termination_by d.height`.

**Tasks**:
- [ ] Create `Cslib/Logics/Bimodal/Metalogic/Soundness/DenseValidity.lean` with Apache 2.0 header
- [ ] Copy source content from `BimodalLogic/Theories/Bimodal/Metalogic/SoundnessLemmas/DenseValidity.lean`
- [ ] Update imports to reference `Cslib.Logics.Bimodal.Metalogic.Soundness.Core` and Mathlib SuccPred modules
- [ ] Update namespace to `Cslib.Logic.Bimodal`
- [ ] Add `variable {Atom : Type*}` and parameterize all `Formula`/`Context` types
- [ ] Rename frame variables `F` -> `ℱ`, `TaskModel F` -> `TaskModel Atom ℱ`
- [ ] Verify `termination_by d.height` still works with parameterized types
- [ ] Cross-reference axiom constructor names against cslib `Axioms.lean` -- update any renamed constructors
- [ ] Run `lake build Cslib.Logics.Bimodal.Metalogic.Soundness.DenseValidity`

**Timing**: 2 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Soundness/DenseValidity.lean` - create (1,338 lines)

**Verification**:
- `lake build Cslib.Logics.Bimodal.Metalogic.Soundness.DenseValidity` passes with zero errors
- `grep -c sorry Cslib/Logics/Bimodal/Metalogic/Soundness/DenseValidity.lean` returns 0
- All 42 swap_axiom cases compile

---

### Phase 4: Metalogic/Soundness/FrameClassVariants.lean [PARTIAL] *(deviation: partial -- axiom_swap_valid_general and axiom_locally_valid_general ported; remaining: derivable_valid_and_swap_valid_general, Prior-UZ/SZ/Z1, discrete combined soundness)*

**Goal**: Port the general and discrete swap validity variants -- `axiom_swap_valid_general`, `derivable_implies_swap_valid_general`, prior_UZ/SZ validity, z1 validity, and the discrete combined soundness.

**Tasks**:
- [ ] Create `Cslib/Logics/Bimodal/Metalogic/Soundness/FrameClassVariants.lean` with Apache 2.0 header
- [ ] Copy source content from `BimodalLogic/Theories/Bimodal/Metalogic/SoundnessLemmas/FrameClassVariants.lean`
- [ ] Update imports to reference `Cslib.Logics.Bimodal.Metalogic.Soundness.DenseValidity`
- [ ] Update namespace to `Cslib.Logic.Bimodal`
- [ ] Add `variable {Atom : Type*}` and parameterize all types
- [ ] Rename frame variables `F` -> `ℱ`, `TaskModel F` -> `TaskModel Atom ℱ`
- [ ] Verify well-founded recursion on succ/pred chains compiles with parameterized types
- [ ] Run `lake build Cslib.Logics.Bimodal.Metalogic.Soundness.FrameClassVariants`

**Timing**: 1.5 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Soundness/FrameClassVariants.lean` - create (971 lines)

**Verification**:
- `lake build Cslib.Logics.Bimodal.Metalogic.Soundness.FrameClassVariants` passes with zero errors
- `grep -c sorry Cslib/Logics/Bimodal/Metalogic/Soundness/FrameClassVariants.lean` returns 0

---

### Phase 5: Metalogic/Soundness/Soundness.lean [NOT STARTED]

**Goal**: Port the main soundness theorem -- all individual axiom validity theorems (prop_k_valid through z1_valid), `axiom_valid`, `axiom_dense_valid`, `axiom_discrete_valid`, and the main `soundness` theorem. This is the central file connecting swap validity to semantic validity.

**Tasks**:
- [ ] Create `Cslib/Logics/Bimodal/Metalogic/Soundness/Soundness.lean` with Apache 2.0 header
- [ ] Copy source content from `BimodalLogic/Theories/Bimodal/Metalogic/Soundness.lean`
- [ ] Update imports to reference `Cslib.Logics.Bimodal.Metalogic.Soundness.FrameClassVariants`, `Cslib.Logics.Bimodal.ProofSystem.Derivation`, `Cslib.Logics.Bimodal.Semantics.Validity`
- [ ] Update namespace to `Cslib.Logic.Bimodal`
- [ ] Add `variable {Atom : Type*}` and parameterize all `Formula`/`Context`/`TaskModel` types
- [ ] Rename frame variables `F` -> `ℱ`
- [ ] Cross-reference all 42+ axiom constructor names against cslib `Axioms.lean`
- [ ] Verify `soundness_dense_valid`, `soundness_dense`, `soundness_discrete_valid`, `soundness_discrete` compile
- [ ] Run `lake build Cslib.Logics.Bimodal.Metalogic.Soundness.Soundness`

**Timing**: 2 hours

**Depends on**: 4

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Soundness/Soundness.lean` - create (1,372 lines)

**Verification**:
- `lake build Cslib.Logics.Bimodal.Metalogic.Soundness.Soundness` passes with zero errors
- `grep -c sorry Cslib/Logics/Bimodal/Metalogic/Soundness/Soundness.lean` returns 0
- `soundness` theorem type-checks with `Formula Atom` parameter

---

### Phase 6: FrameConditions/Validity.lean [NOT STARTED]

**Goal**: Port the parameterized validity definitions -- `valid_over`, `valid_linear`, `valid_dense_fc`, `valid_discrete_fc` -- and equivalence lemmas connecting these to the existing `valid_dense`/`valid_discrete` from `Cslib.Logics.Bimodal.Semantics.Validity`.

**Tasks**:
- [ ] Create `Cslib/Logics/Bimodal/FrameConditions/Validity.lean` with Apache 2.0 header
- [ ] Copy source content from `BimodalLogic/Theories/Bimodal/FrameConditions/Validity.lean`
- [ ] Update imports to reference `Cslib.Logics.Bimodal.FrameConditions.FrameClass` and `Cslib.Logics.Bimodal.Semantics.Validity`
- [ ] Update namespace to `Cslib.Logic.Bimodal`
- [ ] Add `variable {Atom : Type*}` and parameterize all types
- [ ] Rename frame variables `F` -> `ℱ`
- [ ] Verify `haveI` typeclass resolution patterns compile with cslib's typeclass instances
- [ ] Run `lake build Cslib.Logics.Bimodal.FrameConditions.Validity`

**Timing**: 1 hour

**Depends on**: 1, 5

**Files to modify**:
- `Cslib/Logics/Bimodal/FrameConditions/Validity.lean` - create (204 lines)

**Verification**:
- `lake build Cslib.Logics.Bimodal.FrameConditions.Validity` passes with zero errors
- `grep -c sorry Cslib/Logics/Bimodal/FrameConditions/Validity.lean` returns 0
- Equivalence lemmas between `valid_dense_fc` and `valid_dense` type-check

---

### Phase 7: FrameConditions/Soundness.lean [NOT STARTED]

**Goal**: Port the frame-condition-parameterized soundness theorems -- `soundness_over`, `soundness_linear`, `soundness_dense`, `soundness_discrete`, and `soundness_Int`. These bridge the FrameConditions layer to the Metalogic/Soundness layer.

**Tasks**:
- [ ] Create `Cslib/Logics/Bimodal/FrameConditions/Soundness.lean` with Apache 2.0 header
- [ ] Copy source content from `BimodalLogic/Theories/Bimodal/FrameConditions/Soundness.lean`
- [ ] Update imports to reference `Cslib.Logics.Bimodal.FrameConditions.Validity` and `Cslib.Logics.Bimodal.Metalogic.Soundness.Soundness`
- [ ] Update namespace to `Cslib.Logic.Bimodal`
- [ ] Add `variable {Atom : Type*}` and parameterize all types
- [ ] Rename frame variables `F` -> `ℱ`
- [ ] Verify `soundness_Int` instantiation compiles (Int satisfies all frame typeclasses)
- [ ] Run `lake build Cslib.Logics.Bimodal.FrameConditions.Soundness`

**Timing**: 1 hour

**Depends on**: 5, 6

**Files to modify**:
- `Cslib/Logics/Bimodal/FrameConditions/Soundness.lean` - create (190 lines)

**Verification**:
- `lake build Cslib.Logics.Bimodal.FrameConditions.Soundness` passes with zero errors
- `grep -c sorry Cslib/Logics/Bimodal/FrameConditions/Soundness.lean` returns 0

---

### Phase 8: FrameConditions/Compatibility.lean [NOT STARTED]

**Goal**: Port the axiom compatibility typeclasses (`AxiomLinearCompatible`, `AxiomDenseCompatible`, `AxiomDiscreteCompatible`) and all per-axiom instances (13+ monotonicity instances).

**Tasks**:
- [ ] Create `Cslib/Logics/Bimodal/FrameConditions/Compatibility.lean` with Apache 2.0 header
- [ ] Copy source content from `BimodalLogic/Theories/Bimodal/FrameConditions/Compatibility.lean`
- [ ] Update imports to reference `Cslib.Logics.Bimodal.FrameConditions.Soundness` and `Cslib.Logics.Bimodal.ProofSystem.Axioms`
- [ ] Update namespace to `Cslib.Logic.Bimodal`
- [ ] Add `variable {Atom : Type*}` and parameterize all types
- [ ] Cross-reference axiom constructor names against cslib Axioms.lean for instance declarations
- [ ] Verify all instance declarations resolve correctly
- [ ] Run `lake build Cslib.Logics.Bimodal.FrameConditions.Compatibility`

**Timing**: 1 hour

**Depends on**: 7

**Files to modify**:
- `Cslib/Logics/Bimodal/FrameConditions/Compatibility.lean` - create (176 lines)

**Verification**:
- `lake build Cslib.Logics.Bimodal.FrameConditions.Compatibility` passes with zero errors
- `grep -c sorry Cslib/Logics/Bimodal/FrameConditions/Compatibility.lean` returns 0
- All 13+ instance declarations compile

---

### Phase 9: DenseSoundness.lean and DiscreteSoundness.lean [NOT STARTED]

**Goal**: Port the two thin wrapper files that re-export soundness results for dense and discrete frame classes. These are minimal files (51 + 53 lines) that provide convenient entry points.

**Tasks**:
- [ ] Create `Cslib/Logics/Bimodal/Metalogic/Soundness/DenseSoundness.lean` with Apache 2.0 header
- [ ] Copy source content from `BimodalLogic/Theories/Bimodal/Metalogic/DenseSoundness.lean`
- [ ] Update imports to reference `Cslib.Logics.Bimodal.Metalogic.Soundness.Soundness` and `Cslib.Logics.Bimodal.Semantics.Validity`
- [ ] Update namespace, add `variable {Atom : Type*}`, parameterize types
- [ ] Create `Cslib/Logics/Bimodal/Metalogic/Soundness/DiscreteSoundness.lean` with Apache 2.0 header
- [ ] Copy source content from `BimodalLogic/Theories/Bimodal/Metalogic/DiscreteSoundness.lean`
- [ ] Update imports, namespace, and parameterize types (same adaptations as DenseSoundness)
- [ ] Run `lake build` on both modules

**Timing**: 0.5 hours

**Depends on**: 5

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Soundness/DenseSoundness.lean` - create (51 lines)
- `Cslib/Logics/Bimodal/Metalogic/Soundness/DiscreteSoundness.lean` - create (53 lines)

**Verification**:
- `lake build Cslib.Logics.Bimodal.Metalogic.Soundness.DenseSoundness` passes
- `lake build Cslib.Logics.Bimodal.Metalogic.Soundness.DiscreteSoundness` passes
- `grep -rn sorry Cslib/Logics/Bimodal/Metalogic/Soundness/DenseSoundness.lean Cslib/Logics/Bimodal/Metalogic/Soundness/DiscreteSoundness.lean` returns nothing

---

### Phase 10: Integration, Linter, and Final Verification [NOT STARTED]

**Goal**: Full project build, linter check, sorry verification, and import cleanup across all 10 ported files. Ensure the module is ready for PR submission.

**Tasks**:
- [ ] Run `lake build` (full project) to verify no regressions
- [ ] Run `grep -rn sorry Cslib/Logics/Bimodal/FrameConditions/ Cslib/Logics/Bimodal/Metalogic/Soundness/` to confirm zero sorries
- [ ] Run lake shake on each file to identify and remove unused imports
- [ ] Add `set_option linter.all true` to each file and verify linter passes (or suppress specific style lints with justification)
- [ ] Verify all 10 files have correct Apache 2.0 copyright headers
- [ ] Verify namespace consistency (`Cslib.Logic.Bimodal`) across all files
- [ ] Create module import aggregator if needed (e.g., `Cslib/Logics/Bimodal/FrameConditions.lean` barrel file)
- [ ] Update lakefile if needed to register new modules
- [ ] Verify downstream consumers (Task 8: Completeness) will have correct import paths

**Timing**: 2 hours

**Depends on**: 8, 9

**Files to modify**:
- All 10 ported files - linter and import cleanup
- `Cslib/Logics/Bimodal/FrameConditions.lean` - potential barrel file (create)
- `Cslib/Logics/Bimodal/Metalogic/Soundness.lean` - potential barrel file (create, note: distinct from `Soundness/Soundness.lean`)

**Verification**:
- `lake build` (full project) passes with zero errors
- Zero sorries in all ported files
- Linter passes on all files
- All imports are used (no lake shake removals needed)

## Testing & Validation

- [ ] Full `lake build` passes with zero errors across entire project
- [ ] `grep -rn sorry Cslib/Logics/Bimodal/FrameConditions/ Cslib/Logics/Bimodal/Metalogic/Soundness/` returns empty
- [ ] All 10 source files successfully ported (no files skipped)
- [ ] Frame condition typeclasses resolve correctly for `Int` instances
- [ ] `soundness` theorem type-checks with `Formula Atom` parameter
- [ ] `soundness_dense` and `soundness_discrete` correctly specialize
- [ ] No regressions in existing Semantics/ or ProofSystem/ modules
- [ ] Lake shake confirms no unused imports

## Artifacts & Outputs

- `Cslib/Logics/Bimodal/FrameConditions/FrameClass.lean` (220 lines)
- `Cslib/Logics/Bimodal/FrameConditions/Validity.lean` (204 lines)
- `Cslib/Logics/Bimodal/FrameConditions/Soundness.lean` (190 lines)
- `Cslib/Logics/Bimodal/FrameConditions/Compatibility.lean` (176 lines)
- `Cslib/Logics/Bimodal/Metalogic/Soundness/Core.lean` (106 lines)
- `Cslib/Logics/Bimodal/Metalogic/Soundness/DenseValidity.lean` (1,338 lines)
- `Cslib/Logics/Bimodal/Metalogic/Soundness/FrameClassVariants.lean` (971 lines)
- `Cslib/Logics/Bimodal/Metalogic/Soundness/Soundness.lean` (1,372 lines)
- `Cslib/Logics/Bimodal/Metalogic/Soundness/DenseSoundness.lean` (51 lines)
- `Cslib/Logics/Bimodal/Metalogic/Soundness/DiscreteSoundness.lean` (53 lines)
- specs/006_port_frame_conditions_soundness_bimodal/plans/01_frame-soundness-plan.md (this file)
- specs/006_port_frame_conditions_soundness_bimodal/summaries/01_frame-soundness-summary.md (after implementation)

## Rollback/Contingency

All new files are additive (no existing files modified except potentially lakefile). Rollback is straightforward:

1. Delete `Cslib/Logics/Bimodal/FrameConditions/` directory
2. Delete `Cslib/Logics/Bimodal/Metalogic/Soundness/` directory
3. Remove any barrel file imports added
4. Run `lake build` to verify clean state

If individual phases fail:
- For universe level issues in Core.lean: constrain `D` to `Type` (not `Type*`)
- For axiom constructor name mismatches: audit cslib Axioms.lean and create name mapping
- For typeclass resolution failures: add explicit `@` applications or `haveI` hints
- For termination proof failures: try `decreasing_by` with explicit well-founded relation
