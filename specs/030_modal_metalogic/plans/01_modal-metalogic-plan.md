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

### Phase 2: Deduction Theorem [NOT STARTED]

**Goal**: Prove the deduction theorem for modal logic by structural induction on `DerivationTree`, and provide the `HasDeductionTheorem` instance for the generic MCS framework.

**Tasks**:
- [ ] Create file `Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean` with imports from DerivationTree.lean and Consistency.lean
- [ ] Define `DerivationTree.height : DerivationTree Gamma phi -> Nat` by recursion on all 5 constructors
- [ ] Prove propositional axiom derivability helpers needed for the deduction theorem: `derive_imp_self` (phi -> phi), `derive_imp_intro` (prove `Gamma |- phi -> psi` from `Gamma |- psi`), `derive_imp_trans` (transitivity of implication derivability)
- [ ] Define the main `deduction_theorem` function by well-founded recursion on `DerivationTree.height`, handling all 5 constructor cases:
  - `axiom`: `A :: Gamma |- ax_phi` becomes `Gamma |- A -> ax_phi` via imp-intro and axiom
  - `assumption` with `phi = A`: produces `Gamma |- A -> A` (imp_self)
  - `assumption` with `phi in Gamma`: produces `Gamma |- A -> phi` via imp-intro and assumption
  - `modus_ponens`: recursive on both subderivations, then combine via ImplyS axiom
  - `necessitation`: impossible (requires empty context, but `A :: Gamma` is non-empty)
  - `weakening`: `deduction_with_mem` helper for the case where `A` is in the weakened context
- [ ] Define `deduction_with_mem` helper that handles the weakening case where the deduction hypothesis `A` may or may not be in the source context
- [ ] Prove `modal_has_deduction_theorem : HasDeductionTheorem (@modalDerivationSystem Atom)` wrapping the main theorem
- [ ] Verify `lake build Cslib.Logics.Modal.Metalogic.DeductionTheorem`

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

### Phase 3: Modal MCS [NOT STARTED]

**Goal**: Instantiate the generic MCS framework for modal logic and prove modal-specific MCS properties needed for the canonical model construction (box_closure, box_box, box_witness).

**Tasks**:
- [ ] Create file `Cslib/Logics/Modal/Metalogic/MCS.lean` with imports from DeductionTheorem.lean and Consistency.lean
- [ ] Define type aliases for readability: `Modal.SetConsistent S := Metalogic.SetConsistent modalDerivationSystem S`, `Modal.SetMaximalConsistent S := Metalogic.SetMaximalConsistent modalDerivationSystem S`
- [ ] Instantiate generic Lindenbaum lemma: `modal_lindenbaum : Modal.SetConsistent S -> exists M, S subset M and Modal.SetMaximalConsistent M` (direct application of `set_lindenbaum`)
- [ ] Prove `modal_closed_under_derivation` by instantiating generic `closed_under_derivation` with `modal_has_deduction_theorem`
- [ ] Prove `modal_implication_property` by instantiating generic `implication_property`
- [ ] Prove `modal_negation_complete` by instantiating generic `negation_complete`
- [ ] Prove `SetMaximalConsistent.box_closure`: if `box phi in S` and S is MCS, then `phi in S` (using axiom T and `closed_under_derivation`: derive `phi` from `box phi` via T axiom `box phi -> phi` and MP)
- [ ] Prove `SetMaximalConsistent.box_box`: if `box phi in S` and S is MCS, then `box(box phi) in S` (using axiom 4 and `closed_under_derivation`: derive `box(box phi)` from `box phi` via 4 axiom `box phi -> box(box phi)` and MP)
- [ ] Prove `SetMaximalConsistent.diamond_box_duality`: `diamond phi in S iff not (box (neg phi) in S)` (diamond is defined as `neg(box(neg phi))`, so this follows from negation completeness)
- [ ] Prove `SetMaximalConsistent.box_witness`: if `box phi notin S` and S is MCS, then there exists an MCS T such that (forall psi, box psi in S -> psi in T) and phi notin T. Proof: show `{psi | box psi in S} union {neg phi}` is consistent (otherwise derive `box phi` using necessitation + weakening, contradicting `box phi notin S`), then extend to MCS via Lindenbaum.
- [ ] Verify `lake build Cslib.Logics.Modal.Metalogic.MCS`

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

### Phase 4: Soundness [NOT STARTED]

**Goal**: Prove that every derivable formula is valid over the class of reflexive, transitive, Euclidean Kripke frames (S5 frames).

**Tasks**:
- [ ] Create file `Cslib/Logics/Modal/Metalogic/Soundness.lean` with imports from DerivationTree.lean and Basic.lean
- [ ] Define `S5Frame` predicate or use existing frame conditions: a model `m : Model World Atom` where `m.r` is reflexive (`Std.Refl m.r`), transitive (`IsTrans World m.r`), and Euclidean (`Relation.RightEuclidean m.r`)
- [ ] Prove `axiom_sound`: for each `ModalAxiom phi`, phi is valid over S5 frames. Handle each of the 8 axiom constructors:
  - Propositional axioms (ImplyK, ImplyS, EFQ, Peirce): valid in all models (pure propositional reasoning)
  - K axiom: reuse or adapt `Satisfies.k` from Basic.lean
  - T axiom: use reflexivity, connect to `Satisfies.t` pattern
  - Four axiom: use transitivity, connect to `Satisfies.four` pattern (formulated as `box phi -> box(box phi)`, dual of `diamond diamond phi -> diamond phi`)
  - B axiom: use symmetry (derivable from reflexivity + Euclideanness for S5), connect to `Satisfies.b` pattern
- [ ] Prove `mp_sound`: if `Gamma models phi -> psi` and `Gamma models phi`, then `Gamma models psi`
- [ ] Prove `necessitation_sound`: if `[] models phi` (valid in all worlds), then `[] models box phi`
- [ ] Prove `weakening_sound`: if `Gamma models phi` and `Gamma subset Delta`, then `Delta models phi`
- [ ] Prove main `soundness` theorem by induction on `DerivationTree`: `Deriv Gamma phi -> forall (m : Model World Atom), Std.Refl m.r -> IsTrans World m.r -> Relation.RightEuclidean m.r -> forall w, (forall psi in Gamma, Satisfies m w psi) -> Satisfies m w phi`
- [ ] Prove corollary `soundness_derivable`: `Derivable phi -> forall S5 model m, forall w, Satisfies m w phi`
- [ ] Verify `lake build Cslib.Logics.Modal.Metalogic.Soundness`

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
