# Implementation Plan: Task #22

- **Task**: 22 - Build temporal proof system infrastructure and port temporal theorems
- **Status**: [NOT STARTED]
- **Effort**: 10 hours
- **Dependencies**: Task 20 (Propositional theorems -- must be completed)
- **Research Inputs**: specs/022_temporal_infrastructure_theorems/reports/02_temporal-infra-research.md
- **Artifacts**: plans/02_temporal-infra-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

This plan builds the temporal proof system infrastructure in cslib by porting content from BimodalLogic. The work spans three layers: (1) foundation-level additions to Axioms.lean and ProofSystem.lean (22 axiom abbreviations, 22 HasAxiom* typeclasses, TemporalBXHilbert restructuring, TemporalNecessitation non-empty upgrade), (2) concrete proof system files under Logics/Temporal/ProofSystem/ (axiom inductive, derivation tree, derivable wrapper, TemporalBXHilbert instance), and (3) derived theorem library under Logics/Temporal/Theorems/ plus frame condition typeclasses. Total estimated output is approximately 1,735 lines across 8 new or modified files.

### Research Integration

The research report (02_temporal-infra-research.md) identified:
- **Critical bug**: cslib's ModalFuture axiom encodes a different formula than BimodalLogic's modal_future. Must be fixed first.
- **22 axiom abbreviations** needed in Axioms.lean with exact formula encodings using raw connectives (HasImp.imp, HasUntil.untl, HasSince.snce, HasBot.bot).
- **22 HasAxiom* typeclasses** needed in ProofSystem.lean, plus TemporalBXHilbert restructuring to extend all of them.
- **TemporalNecessitation** must become non-empty with a tempNec field encoding G-necessitation generically.
- **Diamond-avoidance**: Direct extension (Option A) preferred for BimodalTMHilbert, with fallback to mirroring BimodalConnectives pattern if compilation issues arise.
- **H-variant theorems** should be derived directly from past-direction axioms rather than via temporal duality, since swap_temporal is not available at the generic typeclass level.
- **788 lines of TemporalDerived** in BimodalLogic translate to approximately 600 lines in cslib's generic typeclass style.
- **Frame condition typeclasses** (220 lines) can be adapted nearly verbatim.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This plan advances the following ROADMAP.md items:
- Phase 2: Task 22 (Temporal Infrastructure and Theorems) -- the primary deliverable
- Unlocks Phase 3: Task 23 (Temporal Semantics) which depends on Task 22
- Unlocks Phase 4: Tasks 4, 5 (Bimodal Proof System, Perpetuity) which depend on Task 22

## Goals & Non-Goals

**Goals**:
- Fix the ModalFuture axiom bug in Axioms.lean
- Add 20 new temporal axiom abbreviations to Axioms.lean
- Add 22 new HasAxiom* typeclasses to ProofSystem.lean
- Make TemporalNecessitation non-empty with tempNec field
- Restructure TemporalBXHilbert to extend all temporal HasAxiom* classes
- Update BimodalTMHilbert for compatibility with restructured TemporalBXHilbert
- Create Temporal.DerivationTree, axiom inductive, and Derivable wrapper
- Register InferenceSystem and TemporalBXHilbert instances for Temporal.HilbertBX
- Port TemporalDerived theorems to generic typeclass style
- Adapt frame condition typeclasses from BimodalLogic

**Non-Goals**:
- Temporal semantics (Task 23 scope)
- Bimodal DerivationTree (Task 4 scope)
- Discrete/Dense extension axiom typeclasses (future work)
- DeductionTheorem for temporal logic (Task 7 scope)
- Perpetuity theorems (Task 5 scope)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| ModalFuture fix breaks downstream code | H | L | Fix early (Phase 1); verify lake build before proceeding |
| Lean 4 class extends limit (24 parents on TemporalBXHilbert) | M | M | Start with flat extends; fall back to intermediate bundle classes if compilation slows |
| Raw connective encoding makes axiom abbrevs verbose/error-prone | M | H | Copy exact formulas from research report; verify each with lean_goal |
| H-variant theorem proofs differ substantially from G-variant patterns | M | L | Past-direction axioms mirror future-direction axioms; proofs follow same structure |
| BimodalTMHilbert diamond causes typeclass resolution failures | M | L | Lean 4 handles extends diamonds; fall back to Option B (direct extension + manual instance) |
| Propositional theorem imports missing needed lemmas | L | L | Task 20 is complete; imp_trans, identity, b_combinator, etc. are all available |

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

### Phase 1: Foundation Axioms and Typeclasses [COMPLETED]

**Goal**: Add all temporal axiom abbreviations, HasAxiom* typeclasses, and restructure TemporalBXHilbert and TemporalNecessitation in the foundation files.

**Tasks**:
- [ ] Fix ModalFuture axiom in Axioms.lean to match BimodalLogic's encoding (box phi -> box (G phi))
- [ ] Add HasSince to the Interaction section variable block in Axioms.lean (needed for complete temporal axiom encoding)
- [ ] Add 20 temporal axiom abbreviations to the Temporal section of Axioms.lean, using raw connective encodings from the research report
- [ ] Add HasAxiomSerialFuture and HasAxiomSerialPast typeclasses to ProofSystem.lean
- [ ] Add 20 new HasAxiom* typeclasses for temporal axioms to ProofSystem.lean in a new TemporalAxiomClasses section
- [ ] Make TemporalNecessitation non-empty: add HasBot and HasImp constraints; add tempNec field encoding G-necessitation
- [ ] Restructure TemporalBXHilbert to extend PropositionalHilbert + TemporalNecessitation + all 22 HasAxiom* classes
- [ ] Update BimodalTMHilbert to extend TemporalBXHilbert (Option A: direct diamond) instead of TemporalNecessitation directly
- [ ] Run lake build to verify no compilation errors

**Timing**: 2.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/Axioms.lean` - Fix ModalFuture; add 20 temporal abbrevs (~200 lines added)
- `Cslib/Foundations/Logic/ProofSystem.lean` - Add 22 HasAxiom* typeclasses; restructure TemporalBXHilbert, TemporalNecessitation, BimodalTMHilbert (~250 lines added)

**Verification**:
- `lake build Cslib.Foundations.Logic.Axioms` passes
- `lake build Cslib.Foundations.Logic.ProofSystem` passes
- All 22 temporal axiom abbrevs resolve correctly (spot-check with lean_hover_info)
- TemporalBXHilbert extends all 22 HasAxiom* plus TemporalNecessitation plus PropositionalHilbert

---

### Phase 2: Temporal Axiom Inductive and FrameClass [COMPLETED]

**Goal**: Create the concrete Temporal.Axiom inductive type with all axiom constructors and the FrameClass enumeration for frame-class-gated derivations.

**Tasks**:
- [ ] Create directory `Cslib/Logics/Temporal/ProofSystem/`
- [ ] Create `Cslib/Logics/Temporal/ProofSystem/Axioms.lean` with:
  - Temporal.FrameClass inductive (Base, Dense, Discrete, Continuous) with LE instance
  - Temporal.Axiom inductive with constructors for: 4 propositional axioms (imp_k, imp_s, efq, peirce), 22 temporal axioms (serial_future, serial_past, left_mono_until_G, left_mono_since_H, right_mono_until, right_mono_since, connect_future, connect_past, enrichment_until, enrichment_since, self_accum_until, self_accum_since, absorb_until, absorb_since, linear_until, linear_since, until_F, since_P, temp_linearity, temp_linearity_past, F_until_equiv, P_since_equiv)
  - minFrameClass function mapping each axiom to its minimum frame class
- [ ] Add module to lakefile (if needed) and verify compilation

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Temporal/ProofSystem/Axioms.lean` - New file (~250 lines)

**Verification**:
- `lake build Cslib.Logics.Temporal.ProofSystem.Axioms` passes
- All 26 axiom constructors are well-typed (lean_hover_info on a few)
- FrameClass ordering is correct (Base <= Dense, Base <= Discrete, etc.)

---

### Phase 3: Temporal DerivationTree and Derivable [COMPLETED]

**Goal**: Create the concrete derivation tree inductive with 6 inference rules and the Prop-valued Derivable wrapper, mirroring BimodalLogic's architecture but for temporal-only logic (no box/necessitation).

**Tasks**:
- [ ] Create `Cslib/Logics/Temporal/ProofSystem/Derivation.lean` with:
  - Temporal.DerivationTree inductive parameterized by (fc : FrameClass), Context, and Formula, with 6 rules: axiom, assumption, modus_ponens, temporal_necessitation, temporal_duality, weakening
  - Height function for derivation trees
  - Lift function for frame class monotonicity
  - Notation: Gamma ⊢ phi (defaults to FrameClass.Base), Gamma ⊢[fc] phi
- [ ] Create `Cslib/Logics/Temporal/ProofSystem/Derivable.lean` with:
  - Temporal.Derivable as Nonempty wrapper
  - Constructor-mirroring lemmas (ax, assume, mp, temp_nec, temp_dual, weaken)
  - Derivable.lift for frame class monotonicity
  - Notation: Gamma |-! phi, |-![fc] phi
- [ ] Verify compilation of both files

**Timing**: 2 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Temporal/ProofSystem/Derivation.lean` - New file (~150 lines)
- `Cslib/Logics/Temporal/ProofSystem/Derivable.lean` - New file (~100 lines)

**Verification**:
- `lake build Cslib.Logics.Temporal.ProofSystem.Derivation` passes
- `lake build Cslib.Logics.Temporal.ProofSystem.Derivable` passes
- DerivationTree has exactly 6 constructors
- Derivable is Prop-valued (Nonempty wrapper)

---

### Phase 4: TemporalBXHilbert Instance Registration [COMPLETED]

**Goal**: Register InferenceSystem, PropositionalHilbert, TemporalNecessitation, all 22 HasAxiom*, and TemporalBXHilbert instances for the Temporal.HilbertBX tag type.

**Tasks**:
- [ ] Create `Cslib/Logics/Temporal/ProofSystem/Instances.lean` with:
  - InferenceSystem instance for Temporal.HilbertBX mapping to Temporal.Derivable
  - ModusPonens instance (from modus_ponens constructor)
  - HasAxiomImplyK, HasAxiomImplyS, HasAxiomEFQ, HasAxiomPeirce instances (from propositional axiom constructors)
  - TemporalNecessitation instance (from temporal_necessitation constructor, providing tempNec)
  - All 22 temporal HasAxiom* instances (each wrapping the corresponding axiom constructor in Derivable)
  - PropositionalHilbert instance (combines ModusPonens + propositional axioms)
  - TemporalBXHilbert instance (combines PropositionalHilbert + TemporalNecessitation + all 22 HasAxiom*)
- [ ] Verify that the TemporalBXHilbert instance compiles without issues (test for extends-limit)
- [ ] Run lake build on the module

**Timing**: 1.5 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Temporal/ProofSystem/Instances.lean` - New file (~200 lines)

**Verification**:
- `lake build Cslib.Logics.Temporal.ProofSystem.Instances` passes
- `lean_hover_info` on the TemporalBXHilbert instance confirms correct type
- All 22 HasAxiom* instances are satisfied

---

### Phase 5: TemporalDerived Theorems and Frame Conditions [COMPLETED]

**Goal**: Port the TemporalDerived theorem library to generic typeclass style and adapt the frame condition typeclasses from BimodalLogic.

**Tasks**:
- [ ] Create `Cslib/Logics/Temporal/Theorems/` directory
- [ ] Create `Cslib/Logics/Temporal/Theorems/TemporalDerived.lean` with:
  - Private local abbreviations for someFuture, allFuture, somePast, allPast using raw connectives
  - Level 0 theorems (direct axiom wrappers): F_mono, P_mono, until_mono_guard, since_mono_guard, until_mono_event, since_mono_event, connect_future_thm, connect_past_thm, until_implies_some_future, since_implies_some_past
  - Level 1 theorems: G_distribution (from right_mono_until + propositional reasoning), G_transitivity (from right_mono_until + absorb_until + DNE)
  - Level 2 theorems: H_distribution (directly from past axioms, NOT via temporal duality), H_transitivity, G_contrapose, G_and_intro, G_imp_trans
  - Level 3 theorems: H_contrapose, H_and_intro, H_imp_trans, connect_future_G, connect_past_H
  - Level 4 theorems: connect_future_chain, connect_past_chain
  - Conjunction elimination theorems: always_to_present, present_to_sometimes, weak_future_left/right, weak_past_left/right, always_imp_all_future, always_imp_all_past
  - Helper lemmas: contrapositive, formula_or_comm
- [ ] Create `Cslib/Logics/Temporal/Theorems/FrameConditions.lean` with:
  - Frame condition typeclasses adapted from BimodalLogic (LinearTemporalFrame, SerialFrame, DenseTemporalFrame, DiscreteTemporalFrame)
  - Standard Int instance for DiscreteTemporalFrame
  - LE hierarchy between frame conditions
- [ ] Verify compilation of both files

**Timing**: 2 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Temporal/Theorems/TemporalDerived.lean` - New file (~600 lines)
- `Cslib/Logics/Temporal/Theorems/FrameConditions.lean` - New file (~130 lines)

**Verification**:
- `lake build Cslib.Logics.Temporal.Theorems.TemporalDerived` passes
- `lake build Cslib.Logics.Temporal.Theorems.FrameConditions` passes
- All 30+ theorems have correct type signatures (spot-check G_distribution, H_distribution, connect_future_chain)
- No sorry in any theorem
- Frame condition instances for Int compile

---

### Phase 6: Final Integration and Build Verification [NOT STARTED]

**Goal**: Ensure all modules are properly imported, the full project builds, and all new files are registered in the build system.

**Tasks**:
- [ ] Create barrel import file `Cslib/Logics/Temporal/ProofSystem.lean` importing all ProofSystem submodules
- [ ] Create barrel import file `Cslib/Logics/Temporal/Theorems.lean` importing all Theorem submodules
- [ ] Verify all new files are discovered by lake (check lakefile if needed)
- [ ] Run full `lake build` to verify no regressions across the entire project
- [ ] Verify no sorry in any new file using lean_verify on key declarations
- [ ] Spot-check that TemporalBXHilbert instance works end-to-end: a temporal theorem applied at the concrete Temporal.Formula type via the registered instance

**Timing**: 0.5 hours

**Depends on**: 4, 5

**Files to modify**:
- `Cslib/Logics/Temporal/ProofSystem.lean` - New barrel import file
- `Cslib/Logics/Temporal/Theorems.lean` - New barrel import file
- Potentially lakefile adjustments

**Verification**:
- `lake build` passes with zero errors
- `lean_verify` on 3-5 key theorems shows no sorry/axiom usage
- Import chain works: Temporal.Theorems.TemporalDerived imports ProofSystem which imports Foundations

---

## Testing & Validation

- [ ] `lake build` passes with zero errors after each phase
- [ ] Full `lake build` passes at the end with zero regressions
- [ ] No `sorry` in any new file (verified via lean_verify)
- [ ] ModalFuture axiom fix verified: formula matches BimodalLogic's modal_future (box phi -> box (G phi))
- [ ] TemporalBXHilbert instance for Temporal.HilbertBX compiles and resolves correctly
- [ ] All 22 temporal HasAxiom* instances satisfied for Temporal.HilbertBX
- [ ] At least 3 TemporalDerived theorems spot-checked for correct type (G_distribution, H_distribution, connect_future_chain)
- [ ] Frame condition typeclasses compile and Int instance satisfies DiscreteTemporalFrame

## Artifacts & Outputs

- `Cslib/Foundations/Logic/Axioms.lean` - Modified: ModalFuture fix + 20 temporal axiom abbrevs
- `Cslib/Foundations/Logic/ProofSystem.lean` - Modified: 22 HasAxiom* + TemporalBXHilbert restructure + TemporalNecessitation update + BimodalTMHilbert update
- `Cslib/Logics/Temporal/ProofSystem/Axioms.lean` - New: FrameClass + Temporal.Axiom inductive
- `Cslib/Logics/Temporal/ProofSystem/Derivation.lean` - New: DerivationTree
- `Cslib/Logics/Temporal/ProofSystem/Derivable.lean` - New: Derivable wrapper
- `Cslib/Logics/Temporal/ProofSystem/Instances.lean` - New: TemporalBXHilbert instance
- `Cslib/Logics/Temporal/Theorems/TemporalDerived.lean` - New: 30+ derived theorems
- `Cslib/Logics/Temporal/Theorems/FrameConditions.lean` - New: Frame condition typeclasses

## Rollback/Contingency

All changes are additive (new files) except for modifications to Axioms.lean and ProofSystem.lean. If the ModalFuture fix or ProofSystem changes break downstream files:
1. Revert Axioms.lean and ProofSystem.lean changes using git
2. All new files under Temporal/ProofSystem/ and Temporal/Theorems/ can be deleted independently
3. If the flat-extends approach causes compilation issues on TemporalBXHilbert (24 parents), fall back to intermediate bundle classes grouping related axioms (e.g., HasBXMonotonicity, HasBXConnection, HasBXAccumulation)
4. If BimodalTMHilbert diamond fails (Option A), fall back to Option B: extend individual HasAxiom* classes directly with a manual TemporalBXHilbert instance
