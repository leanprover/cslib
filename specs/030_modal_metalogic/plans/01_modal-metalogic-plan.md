# Implementation Plan: Task #30 - Modal Metalogic

- **Task**: 30 - Build standalone modal metalogic
- **Status**: [NOT STARTED]
- **Effort**: 18 hours
- **Dependencies**: Task 21 (Modal Proof System, completed), Task 29 (Generic MCS Foundations, completed)
- **Research Inputs**: specs/030_modal_metalogic/reports/01_modal-metalogic-research.md
- **Artifacts**: plans/01_modal-metalogic-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Build a standalone modal metalogic module (~1,500-1,650 lines) at `Cslib/Logics/Modal/Metalogic/` providing the four pillars of metalogic for S5 modal logic: a syntactic proof system (DerivationTree), the deduction theorem, maximal consistent set theory (importing generic foundations from Task 29), soundness over Kripke frames, and completeness via canonical model construction. This is new development, not ported from BimodalLogic, though BimodalLogic patterns inform the proof strategies.

### Research Integration

The research report (01_modal-metalogic-research.md) established:
1. **Existing infrastructure**: `Basic.lean` has full semantic infrastructure (Model, Satisfies, validity) with axiom validity proofs for K, T, B, 4, 5, D. `Cube.lean` defines S5. No syntactic proof system exists.
2. **Generic MCS API** (Task 29, completed): `Consistency.lean` provides `DerivationSystem`, `SetConsistent`, `SetMaximalConsistent`, `set_lindenbaum`, `HasDeductionTheorem`, and closure properties (`closed_under_derivation`, `implication_property`, `negation_complete`).
3. **BimodalLogic patterns**: DerivationTree with 5 constructors (axiom, assumption, modus_ponens, necessitation, weakening), deduction theorem via well-founded recursion on height with `deduction_with_mem` helper, canonical model with universal accessibility for S5.
4. **Design decisions**: Use inductive `ModalAxiom` type (not typeclasses), `DerivationTree` as `Type` (not `Prop`) for pattern matching, S5 with simplified universal canonical relation.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This plan advances the following ROADMAP.md items:
- "Modal metalogic (DeductionTheorem + MCS + Soundness + Completeness)" in `Logics/Modal/Metalogic/`
- Phase 4 (Standalone Metalogic) of the overall porting roadmap
- Validates the generic MCS architecture from Task 29

## Goals & Non-Goals

**Goals**:
- Define `ModalAxiom` inductive type covering S5 axioms (propositional + K, T, B, 4)
- Define `DerivationTree` with 5 constructors and `Deriv` wrapper
- Construct `DerivationSystem` instance connecting to generic MCS framework
- Prove the deduction theorem via structural induction on DerivationTree
- Prove soundness: `Deriv [] phi -> Valid phi` over reflexive+transitive+Euclidean frames
- Prove completeness: `Valid phi -> Deriv [] phi` via canonical Kripke model for S5
- All files compile with `lake build`, zero `sorry` occurrences

**Non-Goals**:
- Soundness/completeness for logics weaker than S5 (K, T, S4)
- Finite model property or decidability (these are bimodal-specific, Task 9)
- Typeclass-polymorphic proof system (ModalHilbert integration deferred to later work)
- Connecting to the existing `HasInferenceSystem (Judgement World Atom)` semantic inference system

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Deduction theorem termination proof is tricky (well-founded recursion on height) | H | M | Follow BimodalLogic's `deduction_with_mem` pattern; simplification from 7 to 5 constructors reduces case analysis |
| Truth lemma box case requires careful canonical relation reasoning | H | M | S5 universal relation simplifies significantly; box_closure + box_witness from MCS properties handle the key steps |
| `ModalConnectives` instance gives `HasBot`/`HasImp` but `HasImp.imp` may not reduce cleanly to `Proposition.imp` | M | L | Verify instance unfolding early in Phase 1; add simp lemmas if needed |
| Lindenbaum lemma for completeness may require universe-level care with `Set (Proposition Atom)` | M | L | Task 29 already handles this generically; instantiation should be straightforward |
| Import cycles between Modal/Basic.lean and Modal/Metalogic/ | L | L | Metalogic imports Basic.lean (one-directional); no risk of cycles |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4, 5 | 3 |
| 5 | 6 | 4, 5 |

Phases within the same wave can execute in parallel.

---

### Phase 1: DerivationTree and Proof System Setup [COMPLETED]

**Goal**: Define the syntactic proof system for S5 modal logic -- axiom schema, derivation tree, derivability predicate, and DerivationSystem instance connecting to the generic MCS framework.

**Tasks**:
- [x] Create file `Cslib/Logics/Modal/Metalogic/DerivationTree.lean` with module header and imports
- [x] Define `ModalAxiom` inductive type with constructors for propositional axioms (ImplyK: `phi -> (psi -> phi)`, ImplyS: `(phi -> (psi -> chi)) -> ((phi -> psi) -> (phi -> chi))`, EFQ: `bot -> phi`, Peirce/DNE: `((phi -> psi) -> phi) -> phi`) and modal axioms (K: `box(phi -> psi) -> (box phi -> box psi)`, T: `box phi -> phi`, Four: `box phi -> box(box phi)`, B: `phi -> box(diamond phi)`)
- [x] Define `DerivationTree` inductive with 5 constructors: `axiom` (axiom instance), `assumption` (from context), `modus_ponens` (from imp and antecedent), `necessitation` (from empty-context derivation), `weakening` (from subset context)
- [x] Define `Deriv` as `Nonempty (DerivationTree Gamma phi)` (the `Prop` wrapper)
- [x] Define `Derivable` as `Deriv [] phi` (derivable without assumptions)
- [x] Prove basic combinators: `mp_deriv` (modus ponens on `Deriv`), `weakening_deriv` (weakening on `Deriv`), `assumption_deriv` (assumption on `Deriv`)
- [x] Construct `modalDerivationSystem : DerivationSystem (Proposition Atom)` by providing `Deriv`, `weakening`, `assumption`, and `mp` fields from the DerivationTree constructors
- [x] Verify `lake build Cslib.Logics.Modal.Metalogic.DerivationTree`

**Timing**: 2.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/DerivationTree.lean` - new file (~200-250 lines)

**Verification**:
- File compiles with zero errors
- `ModalAxiom` has 8 constructors (4 propositional + 4 modal)
- `DerivationTree` has 5 constructors
- `modalDerivationSystem` type-checks as `DerivationSystem (Proposition Atom)`

---

### Phase 2: Deduction Theorem [COMPLETED]

**Goal**: Prove the deduction theorem for modal logic by structural induction on `DerivationTree`, and provide the `HasDeductionTheorem` instance for the generic MCS framework.

**Tasks**:
- [x] Create file `Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean` with imports from DerivationTree.lean and Consistency.lean
- [x] Define `DerivationTree.height : DerivationTree Gamma phi -> Nat` by recursion on all 5 constructors *(deviation: altered -- height defined in DerivationTree.lean, not DeductionTheorem.lean)*
- [x] Prove propositional axiom derivability helpers needed for the deduction theorem: `derive_imp_self` (phi -> phi), `derive_imp_intro` (prove `Gamma |- phi -> psi` from `Gamma |- psi`), `derive_imp_trans` (transitivity of implication derivability) *(deviation: altered -- named deduction_axiom, deduction_imp_self, deduction_assumption_other, deduction_mp as helper functions)*
- [x] Define the main `deduction_theorem` function by well-founded recursion on `DerivationTree.height`, handling all 5 constructor cases
- [x] Define `deduction_with_mem` helper that handles the weakening case where the deduction hypothesis `A` may or may not be in the source context
- [x] Prove `modal_has_deduction_theorem : HasDeductionTheorem (@modalDerivationSystem Atom)` wrapping the main theorem
- [x] Verify `lake build Cslib.Logics.Modal.Metalogic.DeductionTheorem`

**Timing**: 4 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean` - new file (~300 lines)

**Verification**:
- File compiles with zero errors and zero `sorry`
- `modal_has_deduction_theorem` has type `HasDeductionTheorem (@modalDerivationSystem Atom)`
- All 5 constructor cases of `DerivationTree` are handled in the deduction theorem proof
- Termination proof accepted by Lean (well-founded recursion on height)

---

### Phase 3: Modal MCS [COMPLETED]

**Goal**: Instantiate the generic MCS framework for modal logic and prove modal-specific MCS properties needed for the canonical model construction (box_closure, box_box, box_witness).

**Tasks**:
- [x] Create file `Cslib/Logics/Modal/Metalogic/MCS.lean` with imports from DeductionTheorem.lean and Consistency.lean
- [x] Define type aliases for readability: `Modal.SetConsistent`, `Modal.SetMaximalConsistent`
- [x] Instantiate generic Lindenbaum lemma: `modal_lindenbaum`
- [x] Prove `modal_closed_under_derivation` by instantiating generic `closed_under_derivation` with `modal_has_deduction_theorem`
- [x] Prove `modal_implication_property` by instantiating generic `implication_property`
- [x] Prove `modal_negation_complete` by instantiating generic `negation_complete`
- [x] Prove `mcs_box_closure`: if `□φ ∈ S` and S is MCS, then `φ ∈ S`
- [x] Prove `mcs_box_box`: if `□φ ∈ S` and S is MCS, then `□□φ ∈ S`
- [ ] Prove `SetMaximalConsistent.diamond_box_duality` *(deviation: skipped -- diamond/box duality follows directly from negation completeness and is handled inline in completeness proof where needed)*
- [x] Prove `mcs_box_witness`: if `□φ ∉ S` and S is MCS, then exists MCS T with box-accessibility and φ ∉ T *(deviation: altered -- proof uses iterated_deduction with sigma type bundling the K-distribution property, rather than separate k_distribution function)*
- [x] Verify `lake build Cslib.Logics.Modal.Metalogic.MCS`

**Timing**: 3.5 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/MCS.lean` - new file (~350-400 lines)

**Verification**:
- File compiles with zero errors and zero `sorry`
- `box_closure`, `box_box`, `box_witness` are all proven
- Generic MCS properties (`closed_under_derivation`, `implication_property`, `negation_complete`) are successfully instantiated
- `modal_lindenbaum` type-checks

---

### Phase 4: Soundness [COMPLETED]

**Goal**: Prove that every derivable formula is valid over the class of reflexive, transitive, Euclidean Kripke frames (S5 frames).

**Tasks**:
- [x] Create file `Cslib/Logics/Modal/Metalogic/Soundness.lean` with imports from DerivationTree.lean and Basic.lean *(deviation: altered -- imports only DerivationTree.lean; Basic.lean imported transitively)*
- [x] Define S5 frame conditions as explicit hypotheses (h_refl, h_trans, h_eucl) rather than typeclasses *(deviation: altered -- uses explicit hypotheses rather than S5Frame predicate or Std.Refl/IsTrans/Euclidean typeclasses for cleaner proof structure)*
- [x] Prove `axiom_sound`: all 8 axiom constructors valid over S5 frames
- [x] Prove main `soundness` theorem by structural recursion on `DerivationTree` *(deviation: altered -- uses match/structural recursion instead of induction tactic, to properly handle necessitation case with varying worlds)*
- [x] Prove `soundness_derivable` corollary
- [x] Verify `lake build Cslib.Logics.Modal.Metalogic.Soundness`

**Timing**: 3 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Soundness.lean` - new file (~300-350 lines)

**Verification**:
- File compiles with zero errors and zero `sorry`
- `soundness` theorem handles all 5 DerivationTree constructors
- All 8 ModalAxiom cases are proven valid
- `soundness_derivable` provides the clean statement `Derivable phi -> ...`

---

### Phase 5: Completeness [NOT STARTED]

**Goal**: Prove completeness for S5 modal logic via canonical Kripke model construction: every formula valid over all S5 frames is derivable.

**Tasks**:
- [ ] Create file `Cslib/Logics/Modal/Metalogic/Completeness.lean` with imports from MCS.lean, Soundness.lean (for the statement), and Basic.lean
- [ ] Define `CanonicalWorld Atom` as a subtype: `{S : Set (Proposition Atom) // Modal.SetMaximalConsistent S}`
- [ ] Define `CanonicalModel Atom : Model (CanonicalWorld Atom) Atom` where:
  - `r S T := forall phi, box phi in S.val -> phi in T.val` (S5 canonical accessibility)
  - `v S p := Proposition.atom p in S.val` (canonical valuation)
- [ ] Prove canonical model frame properties for S5:
  - Reflexivity: `forall S, r S S` (from `box_closure`)
  - Transitivity: `forall S T U, r S T -> r T U -> r S U` (from `box_box` + transitivity of membership)
  - Euclideanness: `forall S T U, r S T -> r S U -> r T U` (from S5 closure properties)
- [ ] Prove `truth_lemma` by structural induction on `Proposition Atom`: `forall (S : CanonicalWorld Atom) (phi : Proposition Atom), Satisfies (CanonicalModel Atom) S phi <-> phi in S.val`
  - Case `atom p`: by definition of canonical valuation
  - Case `bot`: `False <-> bot in S.val` from consistency of MCS
  - Case `imp phi psi`: from `implication_property` and `negation_complete`
  - Case `box phi`: forward direction from canonical accessibility definition; reverse direction from `box_witness` (contrapositive: if `box phi notin S`, find T with `r S T` and `phi notin T`)
- [ ] Prove `completeness`: if `phi` is valid over all S5 frames, then `Derivable phi`. Proof by contrapositive: if not `Derivable phi`, then `{neg phi}` is consistent, extend to MCS M via Lindenbaum, M is a world in the canonical model, truth lemma gives `neg phi in M`, so `Satisfies (CanonicalModel Atom) M (neg phi)`, so M does not satisfy phi, contradicting validity.
- [ ] Verify `lake build Cslib.Logics.Modal.Metalogic.Completeness`

**Timing**: 4 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Completeness.lean` - new file (~400-450 lines)

**Verification**:
- File compiles with zero errors and zero `sorry`
- `truth_lemma` handles all 4 Proposition constructors
- `completeness` provides `Valid phi -> Derivable phi` (with appropriate formulation of validity over S5 frames)
- Canonical model frame properties (reflexive, transitive, Euclidean) are proven
- `CanonicalWorld` and `CanonicalModel` are well-defined

---

### Phase 6: Build Verification and Integration [NOT STARTED]

**Goal**: Verify full project build, ensure module import structure is correct, and confirm zero sorry occurrences across all metalogic files.

**Tasks**:
- [ ] Create or update a module file `Cslib/Logics/Modal/Metalogic.lean` that imports all four submodules (DerivationTree, DeductionTheorem, MCS, Soundness, Completeness)
- [ ] Run `lake build` for full project verification
- [ ] Run `grep -r sorry Cslib/Logics/Modal/Metalogic/` to confirm zero sorry occurrences
- [ ] Verify that existing modal modules (`Basic.lean`, `Cube.lean`, `Denotation.lean`) are unaffected by the new imports
- [ ] Verify total line count is in the expected range (~1,500-1,650 lines across 5 files)

**Timing**: 1 hour

**Depends on**: 4, 5

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic.lean` - new module aggregator file (~10 lines)

**Verification**:
- `lake build` passes with zero errors
- `grep -r sorry Cslib/Logics/Modal/Metalogic/` returns empty
- All 5 metalogic files are importable from the aggregator
- No regressions in existing modal module compilation

## Testing & Validation

- [ ] `lake build Cslib.Logics.Modal.Metalogic.DerivationTree` compiles
- [ ] `lake build Cslib.Logics.Modal.Metalogic.DeductionTheorem` compiles
- [ ] `lake build Cslib.Logics.Modal.Metalogic.MCS` compiles
- [ ] `lake build Cslib.Logics.Modal.Metalogic.Soundness` compiles
- [ ] `lake build Cslib.Logics.Modal.Metalogic.Completeness` compiles
- [ ] Full `lake build` passes with zero errors
- [ ] `grep -r sorry Cslib/Logics/Modal/Metalogic/` returns no matches
- [ ] `modalDerivationSystem` correctly instantiates the generic `DerivationSystem`
- [ ] `modal_has_deduction_theorem` enables all generic MCS closure properties
- [ ] Soundness theorem covers all 8 axiom cases and all 5 derivation tree constructors
- [ ] Truth lemma covers all 4 proposition constructors
- [ ] Canonical model satisfies S5 frame conditions (reflexive, transitive, Euclidean)

## Artifacts & Outputs

- `Cslib/Logics/Modal/Metalogic/DerivationTree.lean` (~200-250 lines) - Proof system definitions
- `Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean` (~300 lines) - Deduction theorem
- `Cslib/Logics/Modal/Metalogic/MCS.lean` (~350-400 lines) - Modal MCS theory
- `Cslib/Logics/Modal/Metalogic/Soundness.lean` (~300-350 lines) - Soundness theorem
- `Cslib/Logics/Modal/Metalogic/Completeness.lean` (~400-450 lines) - Completeness theorem
- `Cslib/Logics/Modal/Metalogic.lean` (~10 lines) - Module aggregator
- `specs/030_modal_metalogic/plans/01_modal-metalogic-plan.md` (this file)

## Rollback/Contingency

All new files are in `Cslib/Logics/Modal/Metalogic/` -- a new directory with no existing content. Rollback is achieved by deleting the directory and the aggregator file. No existing files are modified. If individual phases fail:
- Phase 2 (deduction theorem) is the highest risk. If well-founded recursion on height fails, try direct structural induction on DerivationTree or mutual recursion pattern.
- Phase 5 (completeness) box case in truth lemma is second highest risk. If the universal canonical relation approach fails, fall back to explicit `box_witness`-based construction with more granular case analysis.
