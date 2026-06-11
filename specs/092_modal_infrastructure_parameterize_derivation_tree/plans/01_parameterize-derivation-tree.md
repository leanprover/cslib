# Implementation Plan: Parameterize DerivationTree and Add Modal Typeclasses

- **Task**: 92 - Parameterize DerivationTree over an axiom predicate for modal cube expansion
- **Status**: [COMPLETED]
- **Effort**: 5 hours
- **Dependencies**: None
- **Research Inputs**: specs/092_modal_infrastructure_parameterize_derivation_tree/reports/01_parameterize-derivation-tree.md
- **Artifacts**: plans/01_parameterize-derivation-tree.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Parameterize the S5 modal logic `DerivationTree` and all downstream definitions over an
`Axioms : Proposition Atom -> Prop` predicate so the proof infrastructure works for any normal
modal logic (K, T, D, S4, S5). The existing `ModalAxiom` inductive stays as-is and becomes the
S5 axiom set. New bundled typeclasses (`ModalTHilbert`, `ModalDHilbert`, `ModalS4Hilbert`) and
tag types are added to `ProofSystem.lean`. All 6 files in the modal metalogic stack are updated.
Backward compatibility is maintained via type aliases that instantiate the parameterized types
at `ModalAxiom`.

### Research Integration

The research report (01_parameterize-derivation-tree.md) identified:
- `ModalAxiom` has 8 constructors (4 propositional + 4 modal: K, T, 4, B), all hardcoded for S5.
- The single parameterization point is the `ax` constructor: `(h : ModalAxiom phi)`.
- Recommended design: add `(Axioms : Proposition Atom -> Prop)` parameter to `DerivationTree`.
- The deduction theorem never inspects axiom payload -- generalization is mechanical.
- MCS lemmas decompose into generic (all normal modal logics) and axiom-specific (T, 4, B).
- Backward compatibility via type aliases (`S5DerivationTree`, etc.).
- 6 files affected in dependency order: ProofSystem -> DerivationTree -> DeductionTheorem -> MCS -> Soundness -> Completeness.
- The `NormalModalAxioms` structural wrapper approach is cleanest for ensuring propositional axiom inclusion.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Parameterize `DerivationTree`, `Deriv`, `Derivable`, `modalDerivationSystem` over `Axioms`
- Add `ModalTHilbert`, `ModalDHilbert`, `ModalS4Hilbert` bundled classes to ProofSystem.lean
- Add `Modal.HilbertT`, `Modal.HilbertD`, `Modal.HilbertS4` tag types
- Refactor `ModalS5Hilbert` to extend `ModalS4Hilbert` with `HasAxiomB`
- Generalize `DeductionTheorem.lean` over `Axioms`
- Generalize MCS.lean: parameterize generic lemmas, add explicit axiom hypotheses to modal-specific ones
- Adapt Soundness.lean and Completeness.lean to use parameterized types (keeping S5-specific proofs)
- Maintain backward compatibility: existing names resolve to S5 instantiations
- Zero regressions: `lake build` passes after every phase

**Non-Goals**:
- Defining separate `PropAxiom`, `AxiomK`, `ModalTAxiom` inductive types (deferred to task 93 Instances.lean)
- Per-system completeness proofs (tasks 95-97)
- Refactoring the completeness proof to be generic over frame conditions
- Changing the Temporal or Bimodal proof systems

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Universe polymorphism issues when adding `Axioms` parameter | H | L | `Axioms phi : Prop` fits in any universe; test early |
| `HasHilbertTree` instance fails to typecheck with parameterized `Axioms` | H | M | Require `ModalAxiom phi -> Axioms phi` inclusion or use `ModalAxiom` directly in the instance; fallback to constraining `Axioms` |
| Cascading type errors across 6 files | M | M | Work file-by-file in dependency order, `lake build` after each |
| `mcs_mp_axiom` signature change breaks Completeness proof | M | M | Keep S5-specific versions alongside generic ones |
| Refactoring `ModalS5Hilbert` to extend `ModalS4Hilbert` breaks BimodalTMHilbert | M | L | Check BimodalTMHilbert extends ModalS5Hilbert; verify compilation |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |

Phases are strictly sequential due to import chain dependencies.

---

### Phase 1: Add Bundled Classes and Tag Types to ProofSystem.lean [COMPLETED]

**Goal**: Add intermediate modal bundled typeclasses and tag types to the proof system hierarchy, and refactor `ModalS5Hilbert` to use the new intermediate classes.

**Tasks**:
- [ ] Add `ModalTHilbert` class extending `ModalHilbert` with `HasAxiomT` (after line 301, after `ModalHilbert` definition)
- [ ] Add `ModalDHilbert` class extending `ModalHilbert` with `HasAxiomD` (after `ModalTHilbert`)
- [ ] Add `ModalS4Hilbert` class extending `ModalTHilbert` with `HasAxiom4` (after `ModalDHilbert`)
- [ ] Refactor `ModalS5Hilbert` (lines 304-309) to extend `ModalS4Hilbert` with `HasAxiomB` instead of extending `ModalHilbert` with T, 4, B directly
- [ ] Verify `BimodalTMHilbert` (lines 342-346) still compiles (it extends `ModalS5Hilbert`)
- [ ] Add tag types after line 363:
  - `opaque Modal.HilbertT : Type := Empty`
  - `opaque Modal.HilbertD : Type := Empty`
  - `opaque Modal.HilbertS4 : Type := Empty`
- [ ] Run `lake build Cslib.Foundations.Logic.ProofSystem` to verify

**Timing**: 30 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/ProofSystem.lean` - Add 3 bundled classes, refactor ModalS5Hilbert, add 3 tag types

**Verification**:
- `lake build Cslib.Foundations.Logic.ProofSystem` passes
- `ModalS5Hilbert` still extends `ClassicalHilbert`, `Necessitation`, `HasAxiomK`, `HasAxiomT`, `HasAxiom4`, `HasAxiomB` (transitively)
- `BimodalTMHilbert` still compiles

---

### Phase 2: Parameterize DerivationTree.lean [COMPLETED]

**Goal**: Add `Axioms` parameter to `DerivationTree` and all derived definitions, with backward-compatible aliases.

**Tasks**:
- [ ] Parameterize `DerivationTree` inductive (lines 95-112):
  - Change signature from `inductive DerivationTree : List (Proposition Atom) -> Proposition Atom -> Type _` to `inductive DerivationTree (Axioms : Proposition Atom -> Prop) : List (Proposition Atom) -> Proposition Atom -> Type _`
  - Change `ax` constructor: `(h : ModalAxiom phi)` becomes `(h : Axioms phi)`
  - All other constructors: add `Axioms` parameter to recursive `DerivationTree` references
- [ ] Update `DerivationTree.height` (lines 121-126): add `{Axioms}` implicit parameter. Body unchanged (never inspects axiom payload).
- [ ] Update height theorems (lines 130-143): add `{Axioms}` implicit parameter
- [ ] Parameterize `Deriv` (line 151): `def Deriv (Axioms : Proposition Atom -> Prop) (Gamma : List ...) (phi : ...) : Prop := Nonempty (DerivationTree Axioms Gamma phi)`
- [ ] Parameterize `Derivable` (line 155): `def Derivable (Axioms : ...) (phi : ...) : Prop := Deriv Axioms [] phi`
- [ ] Parameterize `mp_deriv` (lines 160-163): add `{Axioms}` parameter
- [ ] Parameterize `weakening_deriv` (lines 165-168): add `{Axioms}` parameter
- [ ] Parameterize `assumption_deriv` (lines 170-172): add `{Axioms}` parameter
- [ ] Parameterize `modalDerivationSystem` (lines 181-185): change to `def modalDerivationSystem (Axioms : Proposition Atom -> Prop) : Metalogic.DerivationSystem (Proposition Atom)` using parameterized `Deriv Axioms`
- [ ] Add backward-compatible aliases after `modalDerivationSystem`:
  - `abbrev S5DerivationTree := DerivationTree (@ModalAxiom Atom)`
  - `abbrev S5Deriv := Deriv (@ModalAxiom Atom)`
  - `abbrev S5Derivable := Derivable (@ModalAxiom Atom)`
  - `def s5DerivationSystem : Metalogic.DerivationSystem (Proposition Atom) := modalDerivationSystem ModalAxiom`
- [ ] Update module docstring to reflect parameterization
- [ ] Run `lake build Cslib.Logics.Modal.Metalogic.DerivationTree` to verify

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/DerivationTree.lean` - Parameterize all definitions, add aliases

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.DerivationTree` passes
- `DerivationTree ModalAxiom Gamma phi` is equivalent to old `DerivationTree Gamma phi`
- `s5DerivationSystem` matches old `modalDerivationSystem`

---

### Phase 3: Generalize DeductionTheorem.lean [COMPLETED]

**Goal**: Parameterize the deduction theorem and `HasHilbertTree` instance over `Axioms`, requiring that `Axioms` includes propositional axioms (implyK, implyS).

**Tasks**:
- [ ] Parameterize `HasHilbertTree` instance (lines 57-63):
  - The instance currently references `.implyK` and `.implyS` from `ModalAxiom`. After parameterization, the instance must work for any `Axioms` that includes these.
  - Approach: Add hypotheses `(h_implyK : forall phi psi, Axioms (phi.imp (psi.imp phi)))` and `(h_implyS : forall phi psi chi, Axioms (...))` as instance arguments, OR keep the instance specific to `ModalAxiom` and provide a generic version separately.
  - **Recommended**: Keep the instance at `ModalAxiom` for backward compatibility and add a generic `hilbertTreeOfAxioms` definition that takes explicit inclusion proofs. Alternatively, define a `HasPropAxioms` class and use it.
  - **Simplest approach**: Make the instance parameterized with `[h_K : forall phi psi, Axioms (phi.imp (psi.imp phi))]` but this is awkward. Instead, add a `variable (Axioms : Proposition Atom -> Prop)` and provide the instance when `Axioms` includes the needed constructors. For the deduction theorem itself, just pass proofs.
  - **Practical decision**: Define `noncomputable def hilbertTree (Axioms : Proposition Atom -> Prop) (h_implyK : forall (phi psi : Proposition Atom), Axioms (phi.imp (psi.imp phi))) (h_implyS : forall (phi psi chi : Proposition Atom), Axioms ((phi.imp (psi.imp chi)).imp ((phi.imp psi).imp (phi.imp chi)))) : HasHilbertTree (Proposition Atom)` and keep the existing instance as `instance : HasHilbertTree (Proposition Atom) := hilbertTree ModalAxiom (fun phi psi => .implyK phi psi) (fun phi psi chi => .implyS phi psi chi)`
- [ ] Parameterize `deductionWithMem` (lines 72-114):
  - Add `{Axioms : Proposition Atom -> Prop}` implicit parameter
  - Change `DerivationTree` to `DerivationTree Axioms` throughout
  - The body uses `.ax [] psi h_ax` -- this now has type `Axioms psi`, which is fine
  - The `.implyK` reference on line 105 must come from the axiom set: add hypothesis `(h_implyK : forall phi psi, Axioms (phi.imp (psi.imp phi)))` as explicit parameter, or thread it through
  - **Decision**: Add explicit parameters for `h_implyK` and `h_implyS` to `deductionWithMem` and `deductionTheorem`
- [ ] Parameterize `deductionTheorem` (lines 128-176):
  - Add `{Axioms}` and `h_implyK`, `h_implyS` parameters
  - Line 105 `.implyK phi A` becomes `h_implyK phi A`
  - Line 165 `.implyK phi A` becomes `h_implyK phi A`
  - All `DerivationTree` references become `DerivationTree Axioms`
- [ ] Parameterize `modal_has_deduction_theorem` (lines 184-190):
  - Change signature to take `Axioms` parameter plus `h_implyK`/`h_implyS`
  - References to `modalDerivationSystem` become `modalDerivationSystem Axioms`
  - References to `Deriv` become `Deriv Axioms`
- [ ] Add backward-compatible wrapper: `theorem s5_has_deduction_theorem : Metalogic.HasDeductionTheorem (modalDerivationSystem (@ModalAxiom Atom)) := modal_has_deduction_theorem ModalAxiom ...`
- [ ] Update module docstring
- [ ] Run `lake build Cslib.Logics.Modal.Metalogic.DeductionTheorem` to verify

**Timing**: 1 hour

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean` - Parameterize all definitions

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.DeductionTheorem` passes
- `deductionTheorem` works for any `Axioms` that include `implyK` and `implyS`

---

### Phase 4: Generalize MCS.lean, Soundness.lean, and Completeness.lean [COMPLETED]

**Goal**: Parameterize all MCS, soundness, and completeness definitions to use the new parameterized types, keeping S5-specific content under explicit axiom assumptions.

**Tasks**:

**MCS.lean changes**:
- [ ] Parameterize `Modal.SetConsistent` and `Modal.SetMaximalConsistent` (lines 49-54): add `Axioms` parameter, reference `modalDerivationSystem Axioms`
- [ ] Parameterize `modal_lindenbaum` (lines 59-62): add `Axioms` parameter
- [ ] Parameterize `modal_closed_under_derivation` (lines 65-70): add `Axioms` plus `h_implyK`/`h_implyS` (needed for `modal_has_deduction_theorem`)
- [ ] Parameterize `modal_implication_property` (lines 73-77): add `Axioms` plus prop axiom proofs
- [ ] Parameterize `modal_negation_complete` (lines 80-84): add `Axioms` plus prop axiom proofs
- [ ] Parameterize `mcs_mp_axiom` (lines 89-97): change `(h_ax : ModalAxiom (phi.imp psi))` to `(h_ax : Axioms (phi.imp psi))`. All `DerivationTree` refs become `DerivationTree Axioms`. All `modalDerivationSystem` refs become `modalDerivationSystem Axioms`.
- [ ] Parameterize `mcs_bot_not_mem` (lines 100-107): add `Axioms` parameter
- [ ] Parameterize `mcs_box_closure` (lines 110-113): add `Axioms` parameter and explicit hypothesis `(h_T : forall phi, Axioms ((Proposition.box phi).imp phi))` instead of relying on `ModalAxiom.modalT`
- [ ] Parameterize `mcs_box_box` (lines 116-120): add hypothesis `(h_4 : forall phi, Axioms ((Proposition.box phi).imp (Proposition.box (Proposition.box phi))))`
- [ ] Parameterize `mcs_box_diamond` (lines 123-127): add hypothesis `(h_B : forall phi, Axioms (phi.imp (Proposition.box (Proposition.diamond phi))))`
- [ ] Parameterize `mcs_box_mp` (lines 130-135): add hypothesis `(h_K : forall phi psi, Axioms ((Proposition.box (phi.imp psi)).imp ((Proposition.box phi).imp (Proposition.box psi))))`
- [ ] Parameterize `mcs_neg_of_not_mem`, `mcs_not_mem_of_neg`, `mcs_mem_iff_neg_not_mem` (lines 140-162): add `Axioms` plus prop axiom proofs
- [ ] Parameterize `iteratedDeduction` (lines 169-190): add `Axioms`, `h_implyK`/`h_implyS` plus `h_K` (uses `mcs_box_mp`)
- [ ] Parameterize `derive_box_from_box_context` (lines 197-211): add `Axioms`, prop axiom proofs, `h_K`
- [ ] Parameterize `derive_box_from_inconsistency` (lines 223-289): add `Axioms`, prop axiom proofs, `h_K`, `h_T` (uses `mcs_box_closure` on line 287)
- [ ] Parameterize `mcs_box_witness` (lines 300-322): add `Axioms`, all required axiom proofs
- [ ] Add S5-specific convenience aliases that instantiate at `ModalAxiom`:
  - `abbrev S5SetConsistent := Modal.SetConsistent (@ModalAxiom Atom)`
  - etc. for the most commonly used lemmas
- [ ] Run `lake build Cslib.Logics.Modal.Metalogic.MCS` to verify

**Soundness.lean changes**:
- [ ] Parameterize `axiom_sound` (lines 50-95): The current version pattern-matches on `ModalAxiom` constructors. Keep this S5-specific (it must be S5-specific since it matches all 8 constructors). But change the signature to take `{Axioms}` and `(h_ax : Axioms phi)` plus a proof that `Axioms phi -> ModalAxiom phi` (for the S5 case), OR keep it as `h_ax : ModalAxiom phi` unchanged. **Decision**: Keep `axiom_sound` taking `ModalAxiom` as-is. The parameterized `soundness` theorem takes a generic `axiom_sound_fn` callback.
- [ ] Parameterize `soundness` (lines 103-125): Change `DerivationTree` to `DerivationTree Axioms` and take an additional parameter `(h_ax_sound : forall phi, Axioms phi -> ...valid...)` instead of hardcoding `axiom_sound`. The `.ax` case calls `h_ax_sound` instead of `axiom_sound`.
- [ ] Parameterize `soundness_derivable` (lines 129-137): Change `Derivable` to `Derivable Axioms`, take `h_ax_sound` callback.
- [ ] Add S5-specific wrappers: `theorem s5_soundness ...` and `theorem s5_soundness_derivable ...` that instantiate at `ModalAxiom` using `axiom_sound`.
- [ ] Run `lake build Cslib.Logics.Modal.Metalogic.Soundness` to verify

**Completeness.lean changes**:
- [ ] Parameterize `CanonicalWorld` (line 52): `def CanonicalWorld (Axioms : Proposition Atom -> Prop) (Atom : Type*) := { S : Set (Proposition Atom) // Modal.SetConsistent Axioms ... }`
  - Actually, `CanonicalWorld` uses `Modal.SetMaximalConsistent` which is now parameterized by `Axioms`.
  - Change to: `def CanonicalWorld (Axioms : Proposition Atom -> Prop) (Atom : Type*) := { S : Set (Proposition Atom) // Modal.SetMaximalConsistent Axioms S }`
- [ ] Parameterize `CanonicalModel` (lines 59-61): add `Axioms` parameter
- [ ] Parameterize `canonical_refl`, `canonical_trans`, `canonical_eucl` (lines 66-129): add `Axioms` parameter, thread axiom proofs for T, 4, B, K through to the MCS lemmas they call
- [ ] Parameterize `truth_lemma` (lines 141-208): add `Axioms` and all required axiom proofs. This is the most complex change -- it uses `modal_closed_under_derivation`, `modalDerivationSystem`, `modal_implication_property`, `modal_negation_complete`, `mcs_box_witness`, `mcs_bot_not_mem`, `mcs_not_mem_of_neg`, all of which are now parameterized.
  - Every reference to `modalDerivationSystem` becomes `modalDerivationSystem Axioms`
  - Every reference to MCS lemmas gets the additional axiom proof arguments
  - The explicit `DerivationTree` constructions (`.ax [] _ (.implyK ...)`, `.ax [] _ (.efq ...)`, `.ax [] _ (.peirce ...)`, `.ax [] _ (.implyS ...)`) need axiom inclusion proofs
- [ ] Parameterize `completeness` (lines 221-261): add `Axioms` parameter and all axiom proofs. The explicit `DerivationTree` construction in the consistency proof (lines 237-256) uses `.efq`, `.implyK`, `.implyS`, `.peirce` -- these must come from `Axioms`.
- [ ] Add S5-specific wrappers:
  - `def S5CanonicalWorld := CanonicalWorld (@ModalAxiom Atom)`
  - `theorem s5_completeness` calling `completeness` at `ModalAxiom`
- [ ] Run `lake build Cslib.Logics.Modal.Metalogic.Completeness` to verify

**Timing**: 2 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/MCS.lean` - Parameterize all definitions, add axiom hypotheses
- `Cslib/Logics/Modal/Metalogic/Soundness.lean` - Parameterize soundness with axiom callback
- `Cslib/Logics/Modal/Metalogic/Completeness.lean` - Parameterize canonical model and completeness

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.Completeness` passes (this transitively builds MCS and Soundness)
- S5-specific wrappers type-check

---

### Phase 5: Full Build Verification and Cleanup [COMPLETED]

**Goal**: Verify the entire project builds with zero regressions, clean up any remaining issues, and update documentation.

**Tasks**:
- [ ] Run full `lake build` to verify zero regressions across all modules
- [ ] Verify Bimodal modules still compile (they import from Modal): `lake build Cslib.Logics.Bimodal`
- [ ] Verify Temporal modules still compile: `lake build Cslib.Logics.Temporal`
- [ ] Verify Foundations modules still compile: `lake build Cslib.Foundations`
- [ ] Check for any `sorry` introduced: `grep -rn "sorry" Cslib/Logics/Modal/Metalogic/`
- [ ] Update docstrings in all 6 files to reflect parameterization
- [ ] Verify backward-compatible aliases work: spot-check that old names (`ModalAxiom`, `DerivationTree` at S5, etc.) still resolve

**Timing**: 30 minutes (mostly build time)

**Depends on**: 4

**Files to modify**:
- All 6 files (docstring updates only)

**Verification**:
- `lake build` passes with zero errors
- `grep -rn "sorry" Cslib/Logics/Modal/Metalogic/` returns empty
- No regressions in downstream modules (Bimodal, Temporal)

---

## Testing & Validation

- [ ] `lake build Cslib.Foundations.Logic.ProofSystem` passes after Phase 1
- [ ] `lake build Cslib.Logics.Modal.Metalogic.DerivationTree` passes after Phase 2
- [ ] `lake build Cslib.Logics.Modal.Metalogic.DeductionTheorem` passes after Phase 3
- [ ] `lake build Cslib.Logics.Modal.Metalogic.Completeness` passes after Phase 4 (transitively builds MCS, Soundness)
- [ ] Full `lake build` passes after Phase 5 with zero errors
- [ ] Zero `sorry` in any modified file
- [ ] `BimodalTMHilbert` still compiles (extends `ModalS5Hilbert`)
- [ ] Bimodal and Temporal modules unaffected

## Artifacts & Outputs

- `specs/092_modal_infrastructure_parameterize_derivation_tree/plans/01_parameterize-derivation-tree.md` (this file)
- Modified: `Cslib/Foundations/Logic/ProofSystem.lean`
- Modified: `Cslib/Logics/Modal/Metalogic/DerivationTree.lean`
- Modified: `Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean`
- Modified: `Cslib/Logics/Modal/Metalogic/MCS.lean`
- Modified: `Cslib/Logics/Modal/Metalogic/Soundness.lean`
- Modified: `Cslib/Logics/Modal/Metalogic/Completeness.lean`

## Rollback/Contingency

All changes are to existing files in a git-tracked repository. If parameterization proves infeasible at any phase:

1. `git stash` or `git checkout -- Cslib/` to revert all changes
2. The fallback strategy (from research report): create separate `DerivationTree` types per modal system rather than parameterizing the single type
3. If Phase 4 (MCS/Soundness/Completeness) is too complex, Phases 1-3 can stand alone with backward-compatible aliases -- downstream files would continue using `ModalAxiom` directly until a later task addresses them
