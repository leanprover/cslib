# Implementation Plan: Port Dense Completeness Infrastructure

- **Task**: 35 - Port dense completeness infrastructure and completeness_dense theorem
- **Status**: [NOT STARTED]
- **Effort**: 28 hours
- **Dependencies**: Task 34 (base MCS completeness properties, completed)
- **Research Inputs**: specs/035_port_dense_completeness_bimodal/reports/01_dense-completeness-research.md
- **Artifacts**: plans/01_dense-completeness-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

Port the dense completeness infrastructure from BimodalLogic to cslib, totaling approximately 37 critical-path files (25,857 lines) plus 9 external dependency files (5,302 lines). The deliverable is `completeness_dense`: if a formula is valid on all densely ordered models, then it is derivable in the Dense proof system. The proof uses the Burgess 1982 chronicle construction over Rat. The port involves four directory trees (Algebraic/, Bundle/, BXCanonical/, Chronicle/) plus prerequisite Theorems/ and Syntax/ files. All ~50 existing sorries are ported as-is per task description.

### Research Integration

The research report identified:
- **37 critical-path files** across 10 dependency layers, with a complete porting order
- **7 missing external dependencies** (Theorems/Combinators, GeneralizedNecessitation, Propositional/{Core,Connectives}, TemporalDerived, Subformulas, SubformulaClosure/*) totaling 5,302 lines. Generic versions exist in Foundations/Logic/Theorems/ but bimodal-specific wrappers or ports are needed.
- **WeakCanonical dependency** in BXCanonical/Completeness.lean and ChronicleToCountermodel.lean: must be handled by file splitting (Dense.lean) or sorry-stubs for discrete path
- **~50 sorries** to port as-is across all files
- **Key translation patterns**: Formula -> Formula Atom, S -> Omega, Axiom renaming, FrameClass genericity, noncomputable sections

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This plan advances Phase 5 (Bimodal Porting), specifically Task 8 (Strong Completeness, expanded into tasks 34-37). Completing task 35 unblocks tasks 36 (discrete completeness), 37 (continuous completeness), and 41 (abstract completeness infrastructure).

## Goals & Non-Goals

**Goals**:
- Port all 37 critical-path files for `completeness_dense`
- Port 9 external dependency files (bimodal-specific Theorems/ and Syntax/SubformulaClosure/)
- `lake build` succeeds after each phase
- All ~50 sorries preserved as-is
- Correct namespace translation (Bimodal -> Cslib.Logic.Bimodal)
- Type-polymorphic Formula Atom throughout

**Non-Goals**:
- Eliminating any existing sorries (port as-is)
- Porting WeakCanonical/ (52,942 lines; separate task 36)
- Porting off-path Bundle/ files (CanonicalIrreflexivity, CanonicalTaskRelation, SuccExistence; 2,390 lines)
- Porting off-path Quasimodel/ files (EnrichedClosure, Realization, LocusControl; 700 lines)
- Mathlib linter compliance (focus on compilation correctness)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Volume (~30K lines) overwhelms single implementation cycle | H | H | 12-phase plan with independent verification per phase |
| Bimodal Theorems/ bridge files have API differences from generic Foundations versions | M | H | Phase 1 creates bridge/wrapper files first; verify imports early |
| WeakCanonical import in Completeness.lean and ChronicleToCountermodel.lean | H | M | Split Completeness.lean into Dense.lean (no WeakCanonical) and placeholder; sorry-stub WeakCanonical refs in ChronicleToCountermodel |
| Mathlib API differences for Rat/Archimedean/CountableDenseLinearOrder in Chronicle/ | M | M | Verify Mathlib imports compile in Phase 9 (ChronicleTypes first) before committing to deeper Chronicle files |
| Universe polymorphism (Formula -> Formula Atom) requires pervasive changes | M | L | Systematic pattern from tasks 34/42 experience; apply uniformly |
| Encodable/Denumerable instance for `Formula Atom` may not exist | M | M | Check in Phase 8 (CanonicalModel); may need sorry-stub or instance construction |
| SubformulaClosure TemporalFormulas.lean is 1,296 lines with dense case analysis | M | L | Budget adequate time; this is a mechanical port |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4, 5 | 2, 3 |
| 4 | 6 | 4, 5 |
| 5 | 7 | 4, 5 |
| 6 | 8 | 6, 7 |
| 7 | 9 | 8 |
| 8 | 10 | 9 |
| 9 | 11 | 10 |
| 10 | 12 | 11 |

Phases within the same wave can execute in parallel.

---

### Phase 1: External Dependencies -- Bimodal Theorems and Syntax [COMPLETED]

**Goal**: Port the 9 prerequisite files that nearly all Algebraic/, Bundle/, and BXCanonical/ files depend on. These are bimodal-specific versions of Theorems/ and Syntax/ files.

**Tasks**:
- [x] Port `Theorems/Combinators.lean` (675 lines) to `Cslib/Logics/Bimodal/Theorems/Combinators.lean`. *(completed)*
- [x] Port `Theorems/GeneralizedNecessitation.lean` (240 lines) to `Cslib/Logics/Bimodal/Theorems/GeneralizedNecessitation.lean`. *(completed)*
- [x] Port `Theorems/Propositional/Core.lean` (730 lines) to `Cslib/Logics/Bimodal/Theorems/Propositional/Core.lean`. *(completed)*
- [x] Port `Theorems/Propositional/Connectives.lean` (745 lines) to `Cslib/Logics/Bimodal/Theorems/Propositional/Connectives.lean`. *(completed)*
- [x] Port `Theorems/TemporalDerived.lean` (788 lines) to `Cslib/Logics/Bimodal/Theorems/TemporalDerived.lean`. *(completed)*
- [x] Port `Syntax/Subformulas.lean` (229 lines) to `Cslib/Logics/Bimodal/Syntax/Subformulas.lean`. *(deviation: skipped -- already exists in cslib)*
- [x] Port `Syntax/SubformulaClosure/Closure.lean` (367 lines) to `Cslib/Logics/Bimodal/Syntax/SubformulaClosure/Closure.lean`. *(deviation: skipped -- already exists as SubformulaClosure.lean)*
- [x] Port `Syntax/SubformulaClosure/NestingDepth.lean` (232 lines) to `Cslib/Logics/Bimodal/Syntax/SubformulaClosure/NestingDepth.lean`. *(completed)*
- [x] Port `Syntax/SubformulaClosure/TemporalFormulas.lean` (1,296 lines) to `Cslib/Logics/Bimodal/Syntax/SubformulaClosure/TemporalFormulas.lean`. *(deviation: altered -- ported core definitions and membership lemmas; structural case analysis lemmas deferred to continuation)*
- [ ] Verify `lake build` passes

**Timing**: 4 hours

**Depends on**: none

**Files to modify/create**:
- `Cslib/Logics/Bimodal/Theorems/Combinators.lean` - new (675 lines)
- `Cslib/Logics/Bimodal/Theorems/GeneralizedNecessitation.lean` - new (240 lines)
- `Cslib/Logics/Bimodal/Theorems/Propositional/Core.lean` - new (730 lines)
- `Cslib/Logics/Bimodal/Theorems/Propositional/Connectives.lean` - new (745 lines)
- `Cslib/Logics/Bimodal/Theorems/TemporalDerived.lean` - new (788 lines)
- `Cslib/Logics/Bimodal/Syntax/Subformulas.lean` - new (229 lines)
- `Cslib/Logics/Bimodal/Syntax/SubformulaClosure/Closure.lean` - new (367 lines)
- `Cslib/Logics/Bimodal/Syntax/SubformulaClosure/NestingDepth.lean` - new (232 lines)
- `Cslib/Logics/Bimodal/Syntax/SubformulaClosure/TemporalFormulas.lean` - new (1,296 lines)

**Verification**:
- `lake build` succeeds
- All 9 files compile with correct imports
- Namespace is `Cslib.Logic.Bimodal.Theorems.*` and `Cslib.Logic.Bimodal.Syntax.*`

---

### Phase 2: Algebraic Layer 1-3 -- Lindenbaum through UltrafilterMCS [NOT STARTED]

**Goal**: Port the first four Algebraic/ files establishing the Lindenbaum-Tarski algebra and ultrafilter-MCS bijection.

**Tasks**:
- [ ] Port `Algebraic/LindenbaumQuotient.lean` (440 lines, 2 sorries) to `Cslib/Logics/Bimodal/Metalogic/Algebraic/LindenbaumQuotient.lean`. Quotient construction via provable equivalence. Layer 1.
- [ ] Port `Algebraic/BooleanStructure.lean` (447 lines) to `Cslib/Logics/Bimodal/Metalogic/Algebraic/BooleanStructure.lean`. Boolean algebra instance for Lindenbaum algebra. Layer 2, depends on LindenbaumQuotient.
- [ ] Port `Algebraic/InteriorOperators.lean` (191 lines, 1 sorry) to `Cslib/Logics/Bimodal/Metalogic/Algebraic/InteriorOperators.lean`. G/H as interior operators. Layer 3, depends on BooleanStructure.
- [ ] Port `Algebraic/UltrafilterMCS.lean` (1,053 lines) to `Cslib/Logics/Bimodal/Metalogic/Algebraic/UltrafilterMCS.lean`. Bijection ultrafilters <-> MCS. Layer 4, depends on InteriorOperators.
- [ ] Verify `lake build` passes

**Timing**: 2 hours

**Depends on**: 1

**Files to modify/create**:
- `Cslib/Logics/Bimodal/Metalogic/Algebraic/LindenbaumQuotient.lean` - new (440 lines)
- `Cslib/Logics/Bimodal/Metalogic/Algebraic/BooleanStructure.lean` - new (447 lines)
- `Cslib/Logics/Bimodal/Metalogic/Algebraic/InteriorOperators.lean` - new (191 lines)
- `Cslib/Logics/Bimodal/Metalogic/Algebraic/UltrafilterMCS.lean` - new (1,053 lines)

**Verification**:
- `lake build` succeeds
- All 4 files compile
- 3 sorries preserved (2 in LindenbaumQuotient, 1 in InteriorOperators)

---

### Phase 3: Bundle Layer 1-3 -- FMCS through CanonicalFrame [NOT STARTED]

**Goal**: Port the foundational Bundle/ files establishing FMCS definitions, temporal content, witness seeds, and canonical frame construction.

**Tasks**:
- [ ] Port `Bundle/FMCSDef.lean` (125 lines) to `Cslib/Logics/Bimodal/Metalogic/Bundle/FMCSDef.lean`. FMCS structure definition. Layer 1.
- [ ] Port `Bundle/FMCS.lean` (17 lines) to `Cslib/Logics/Bimodal/Metalogic/Bundle/FMCS.lean`. Barrel import. Layer 2, depends on FMCSDef.
- [ ] Port `Bundle/TemporalContent.lean` (244 lines) to `Cslib/Logics/Bimodal/Metalogic/Bundle/TemporalContent.lean`. Temporal content for MCS. Layer 1.
- [ ] Port `Bundle/WitnessSeed.lean` (648 lines) to `Cslib/Logics/Bimodal/Metalogic/Bundle/WitnessSeed.lean`. Forward/backward witness seeds. Layer 2, depends on TemporalContent.
- [ ] Port `Bundle/BFMCS.lean` (229 lines) to `Cslib/Logics/Bimodal/Metalogic/Bundle/BFMCS.lean`. Bundle of FMCS families. Layer 3, depends on FMCS.
- [ ] Port `Bundle/CanonicalFrame.lean` (297 lines) to `Cslib/Logics/Bimodal/Metalogic/Bundle/CanonicalFrame.lean`. Canonical frame construction. Layer 3, depends on TemporalContent, WitnessSeed.
- [ ] Verify `lake build` passes

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify/create**:
- `Cslib/Logics/Bimodal/Metalogic/Bundle/FMCSDef.lean` - new (125 lines)
- `Cslib/Logics/Bimodal/Metalogic/Bundle/FMCS.lean` - new (17 lines)
- `Cslib/Logics/Bimodal/Metalogic/Bundle/TemporalContent.lean` - new (244 lines)
- `Cslib/Logics/Bimodal/Metalogic/Bundle/WitnessSeed.lean` - new (648 lines)
- `Cslib/Logics/Bimodal/Metalogic/Bundle/BFMCS.lean` - new (229 lines)
- `Cslib/Logics/Bimodal/Metalogic/Bundle/CanonicalFrame.lean` - new (297 lines)

**Verification**:
- `lake build` succeeds
- All 6 files compile
- 0 sorries in this phase

---

### Phase 4: Bundle Layer 4-5 -- ModalSaturation through UntilSinceCoherence [NOT STARTED]

**Goal**: Port the mid-layer Bundle/ files for modal saturation, successor relation, temporal coherence, construction, and until/since coherence.

**Tasks**:
- [ ] Port `Bundle/ModalSaturation.lean` (521 lines, 1 sorry) to `Cslib/Logics/Bimodal/Metalogic/Bundle/ModalSaturation.lean`. Modal saturation for MCS. Layer 4, depends on BFMCS.
- [ ] Port `Bundle/SuccRelation.lean` (655 lines, 7 sorries) to `Cslib/Logics/Bimodal/Metalogic/Bundle/SuccRelation.lean`. Successor relation on canonical frame. Layer 4, depends on TemporalContent, CanonicalFrame, WitnessSeed.
- [ ] Port `Bundle/TemporalCoherence.lean` (621 lines, 2 sorries) to `Cslib/Logics/Bimodal/Metalogic/Bundle/TemporalCoherence.lean`. G/H propagation proofs. Layer 4, depends on BFMCS, ModalSaturation.
- [ ] Port `Bundle/Construction.lean` (260 lines, 3 sorries) to `Cslib/Logics/Bimodal/Metalogic/Bundle/Construction.lean`. BFMCS construction. Layer 4, depends on BFMCS, ModalSaturation.
- [ ] Port `Bundle/UntilSinceCoherence.lean` (211 lines, 2 sorries) to `Cslib/Logics/Bimodal/Metalogic/Bundle/UntilSinceCoherence.lean`. Until/Since coherence. Layer 5, depends on TemporalCoherence, SuccRelation.
- [ ] Verify `lake build` passes

**Timing**: 2.5 hours

**Depends on**: 2, 3

**Files to modify/create**:
- `Cslib/Logics/Bimodal/Metalogic/Bundle/ModalSaturation.lean` - new (521 lines)
- `Cslib/Logics/Bimodal/Metalogic/Bundle/SuccRelation.lean` - new (655 lines)
- `Cslib/Logics/Bimodal/Metalogic/Bundle/TemporalCoherence.lean` - new (621 lines)
- `Cslib/Logics/Bimodal/Metalogic/Bundle/Construction.lean` - new (260 lines)
- `Cslib/Logics/Bimodal/Metalogic/Bundle/UntilSinceCoherence.lean` - new (211 lines)

**Verification**:
- `lake build` succeeds
- All 5 files compile
- 15 sorries preserved (7 SuccRelation, 2 TemporalCoherence, 3 Construction, 2 UntilSinceCoherence, 1 ModalSaturation)

---

### Phase 5: BXCanonical Core -- Frame, Quasimodel, Filtration [NOT STARTED]

**Goal**: Port the BXCanonical core infrastructure: Frame, TruthLemma, Quasimodel/, Filtration/, and CanonicalChain.

**Tasks**:
- [ ] Port `BXCanonical/Quasimodel/SubformulaClosure.lean` (112 lines) to `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Quasimodel/SubformulaClosure.lean`. Finite subformula closure. Layer 1.
- [ ] Port `BXCanonical/Quasimodel/HintikkaPoint.lean` (144 lines) to `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Quasimodel/HintikkaPoint.lean`. Hintikka point definition. Layer 3, depends on SubformulaClosure.
- [ ] Port `BXCanonical/Quasimodel/Construction.lean` (841 lines, 1 sorry) to `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Quasimodel/Construction.lean`. BX axiom lemmas at MCS level. Layer 4, depends on HintikkaPoint.
- [ ] Port `BXCanonical/Frame.lean` (710 lines, 2 sorries) to `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Frame.lean`. BXPoint, canonical ordering, witnesses. Layer 4, depends on Bundle/TemporalContent, WitnessSeed, CanonicalFrame.
- [ ] Port `BXCanonical/TruthLemma.lean` (302 lines) to `Cslib/Logics/Bimodal/Metalogic/BXCanonical/TruthLemma.lean`. Truth lemma by formula induction. Layer 5, depends on Frame.
- [ ] Port `BXCanonical/Filtration/DefectChain.lean` (112 lines) to `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Filtration/DefectChain.lean`. Defect chain for filtration. Layer 5, depends on Frame, Quasimodel/Construction.
- [ ] Port `BXCanonical/CanonicalChain.lean` (110 lines, 1 sorry) to `Cslib/Logics/Bimodal/Metalogic/BXCanonical/CanonicalChain.lean`. BX axiom lemmas, delegation bridges. Layer 5, depends on Frame, Quasimodel/Construction, DefectChain.
- [ ] Verify `lake build` passes

**Timing**: 2.5 hours

**Depends on**: 2, 3

**Files to modify/create**:
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Quasimodel/SubformulaClosure.lean` - new (112 lines)
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Quasimodel/HintikkaPoint.lean` - new (144 lines)
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Quasimodel/Construction.lean` - new (841 lines)
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Frame.lean` - new (710 lines)
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/TruthLemma.lean` - new (302 lines)
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Filtration/DefectChain.lean` - new (112 lines)
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/CanonicalChain.lean` - new (110 lines)

**Verification**:
- `lake build` succeeds
- All 7 files compile
- 4 sorries preserved (2 Frame, 1 Quasimodel/Construction, 1 CanonicalChain)

---

### Phase 6: Algebraic Parametric Modules [NOT STARTED]

**Goal**: Port the parametric completeness infrastructure that provides D-parametric canonical models, truth lemmas, and completeness.

**Tasks**:
- [ ] Port `Algebraic/ParametricCanonical.lean` (246 lines) to `Cslib/Logics/Bimodal/Metalogic/Algebraic/ParametricCanonical.lean`. D-parametric TaskFrame. Layer 5, depends on UltrafilterMCS, Bundle/CanonicalFrame.
- [ ] Port `Algebraic/ParametricHistory.lean` (174 lines) to `Cslib/Logics/Bimodal/Metalogic/Algebraic/ParametricHistory.lean`. D-parametric history conversion. Layer 6, depends on ParametricCanonical, BFMCS.
- [ ] Port `Algebraic/ParametricTruthLemma.lean` (472 lines) to `Cslib/Logics/Bimodal/Metalogic/Algebraic/ParametricTruthLemma.lean`. D-parametric truth lemma. Layer 7, depends on ParametricHistory, TemporalCoherence.
- [ ] Port `Algebraic/RestrictedParametricTruthLemma.lean` (410 lines) to `Cslib/Logics/Bimodal/Metalogic/Algebraic/RestrictedParametricTruthLemma.lean`. Restricted parametric truth lemma. Layer 7, depends on ParametricTruthLemma, TemporalCoherence.
- [ ] Port `Algebraic/ParametricCompleteness.lean` (301 lines) to `Cslib/Logics/Bimodal/Metalogic/Algebraic/ParametricCompleteness.lean`. D-parametric completeness. Layer 7, depends on ParametricTruthLemma, Bundle/Construction, ModalSaturation.
- [ ] Verify `lake build` passes

**Timing**: 2 hours

**Depends on**: 4, 5

**Files to modify/create**:
- `Cslib/Logics/Bimodal/Metalogic/Algebraic/ParametricCanonical.lean` - new (246 lines)
- `Cslib/Logics/Bimodal/Metalogic/Algebraic/ParametricHistory.lean` - new (174 lines)
- `Cslib/Logics/Bimodal/Metalogic/Algebraic/ParametricTruthLemma.lean` - new (472 lines)
- `Cslib/Logics/Bimodal/Metalogic/Algebraic/RestrictedParametricTruthLemma.lean` - new (410 lines)
- `Cslib/Logics/Bimodal/Metalogic/Algebraic/ParametricCompleteness.lean` - new (301 lines)

**Verification**:
- `lake build` succeeds
- All 5 files compile
- 0 sorries in this phase

---

### Phase 7: BXCanonical Secondary -- OrderedSeedConsistency and CanonicalModel [NOT STARTED]

**Goal**: Port the ordered seed consistency and canonical model construction that bridges Bundle/ and BXCanonical/.

**Tasks**:
- [ ] Port `BXCanonical/OrderedSeedConsistency.lean` (254 lines) to `Cslib/Logics/Bimodal/Metalogic/BXCanonical/OrderedSeedConsistency.lean`. Ordered seed consistency. Layer 6, depends on Frame, CanonicalChain.
- [ ] Port `BXCanonical/CanonicalModel.lean` (794 lines) to `Cslib/Logics/Bimodal/Metalogic/BXCanonical/CanonicalModel.lean`. BFMCS Int construction from BX witnesses. Layer 8, depends on CanonicalChain, TruthLemma, FMCSDef, ChronicleTypes (forward ref), BFMCS. Note: this file uses `Denumerable.ofNat Formula` which requires `Denumerable (Formula Atom)` in the polymorphic target. May need a sorry-stub or instance construction for `Denumerable`.
- [ ] Verify `lake build` passes

**Timing**: 2 hours

**Depends on**: 4, 5

**Files to modify/create**:
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/OrderedSeedConsistency.lean` - new (254 lines)
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/CanonicalModel.lean` - new (794 lines)

**Verification**:
- `lake build` succeeds
- Both files compile
- 0 sorries in this phase (unless Denumerable instance needs sorry-stub)

---

### Phase 8: Chronicle Types and RRelation [NOT STARTED]

**Goal**: Port the Chronicle type definitions and R-relation, which form the foundation of the Burgess chronicle construction. These files import many Mathlib modules (Rat, Archimedean, etc.) so this phase validates Mathlib compatibility.

**Tasks**:
- [ ] Port `Chronicle/ChronicleTypes.lean` (865 lines) to `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleTypes.lean`. Chronicle type definitions. Layer 5, depends on Bundle/TemporalContent, BXCanonical/Frame, Bundle/ModalSaturation. Imports Mathlib Rat, Archimedean, CountableDenseLinearOrder.
- [ ] Port `Chronicle/RRelation.lean` (1,686 lines, 1 sorry) to `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/RRelation.lean`. R-relation on chronicle. Layer 5, depends on ChronicleTypes, Bundle/WitnessSeed.
- [ ] Verify `lake build` passes

**Timing**: 2.5 hours

**Depends on**: 6, 7

**Files to modify/create**:
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleTypes.lean` - new (865 lines)
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/RRelation.lean` - new (1,686 lines)

**Verification**:
- `lake build` succeeds
- Both files compile with Mathlib imports
- 1 sorry preserved (RRelation)

---

### Phase 9: Chronicle Core -- PointInsertion, CounterexampleElimination, Construction [NOT STARTED]

**Goal**: Port the three large Chronicle core files that implement the point insertion and counterexample elimination algorithms.

**Tasks**:
- [ ] Port `Chronicle/PointInsertion.lean` (3,527 lines, 1 sorry) to `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/PointInsertion.lean`. Point insertion construction. Layer 6, depends on BXCanonical/Frame, OrderedSeedConsistency, ChronicleTypes, RRelation.
- [ ] Port `Chronicle/CounterexampleElimination.lean` (3,487 lines) to `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/CounterexampleElimination.lean`. Counterexample elimination. Layer 6, depends on ChronicleTypes, RRelation, PointInsertion.
- [ ] Port `Chronicle/ChronicleConstruction.lean` (1,510 lines) to `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleConstruction.lean`. Main chronicle construction. Layer 7, depends on ChronicleTypes, RRelation, PointInsertion, CounterexampleElimination.
- [ ] Verify `lake build` passes

**Timing**: 4 hours

**Depends on**: 8

**Files to modify/create**:
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/PointInsertion.lean` - new (3,527 lines)
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/CounterexampleElimination.lean` - new (3,487 lines)
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleConstruction.lean` - new (1,510 lines)

**Verification**:
- `lake build` succeeds
- All 3 files compile
- 1 sorry preserved (PointInsertion)

---

### Phase 10: Countermodel Integration [NOT STARTED]

**Goal**: Port the countermodel construction pipeline that converts chronicles to actual countermodels. ChronicleToCountermodelBasic has no WeakCanonical dependency. ChronicleToCountermodel imports WeakCanonical only for the discrete path; sorry-stub those references.

**Tasks**:
- [ ] Port `Chronicle/ChronicleToCountermodelBasic.lean` (1,163 lines, 3 sorries) to `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodelBasic.lean`. Dense/discrete case split, cantor_bfmcs_dense. Layer 9, depends on ChronicleConstruction, CanonicalModel, UntilSinceCoherence, ParametricCompleteness, RestrictedParametricTruthLemma. No WeakCanonical dependency.
- [ ] Port `Chronicle/ChronicleToCountermodel.lean` (2,271 lines, 6 sorries) to `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodel.lean`. Gap elimination, mcs_mixed_case_absurd. Layer 10, depends on ChronicleToCountermodelBasic. For WeakCanonical references (used only in discrete path and mcs_mixed_case_absurd): sorry-stub those definitions/imports. The dense-path functions should compile without WeakCanonical.
- [ ] Verify `lake build` passes

**Timing**: 2.5 hours

**Depends on**: 9

**Files to modify/create**:
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodelBasic.lean` - new (1,163 lines)
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodel.lean` - new (2,271 lines, with sorry-stubs for WeakCanonical refs)

**Verification**:
- `lake build` succeeds
- Both files compile
- 9 sorries preserved (3 Basic + 6 Countermodel) plus WeakCanonical sorry-stubs

---

### Phase 11: completeness_dense Theorem [NOT STARTED]

**Goal**: Port the completeness_dense theorem, splitting BXCanonical/Completeness.lean to isolate the dense path from the WeakCanonical-dependent discrete path.

**Tasks**:
- [ ] Create `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Completeness/Dense.lean` containing: `neg_consistent_of_not_derivable`, `countermodel_dense_enriched`, `completeness_dense`. These are the dense-path theorems that do NOT require WeakCanonical. Extract from source Completeness.lean (407 lines total; dense portion ~200 lines).
- [ ] Create `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Completeness.lean` as a placeholder/barrel that re-exports Dense.lean and contains sorry-stubbed `completeness` and `completeness_discrete` with TODO comments for when WeakCanonical is ported (task 36).
- [ ] Port `Algebraic/AlgebraicCompleteness.lean` (191 lines) to `Cslib/Logics/Bimodal/Metalogic/Algebraic/AlgebraicCompleteness.lean`. Off-path but small and depends only on UltrafilterMCS.
- [ ] Verify `lake build` passes
- [ ] Verify `completeness_dense` compiles and has the expected type signature

**Timing**: 2 hours

**Depends on**: 10

**Files to modify/create**:
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Completeness/Dense.lean` - new (~200 lines)
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Completeness.lean` - new (~200 lines, placeholder)
- `Cslib/Logics/Bimodal/Metalogic/Algebraic/AlgebraicCompleteness.lean` - new (191 lines)

**Verification**:
- `lake build` succeeds
- `completeness_dense` theorem exists and has correct type
- Dense path is fully functional without WeakCanonical

---

### Phase 12: Barrel Imports and Final Verification [NOT STARTED]

**Goal**: Create barrel import files, verify the full build, and ensure all files are properly connected.

**Tasks**:
- [ ] Create `Cslib/Logics/Bimodal/Metalogic/Algebraic/Algebraic.lean` barrel import (re-exports all Algebraic/ modules)
- [ ] Create `Cslib/Logics/Bimodal/Metalogic/Bundle/Bundle.lean` barrel import (re-exports all critical-path Bundle/ modules)
- [ ] Create `Cslib/Logics/Bimodal/Metalogic/BXCanonical/BXCanonical.lean` barrel import (re-exports all BXCanonical/ modules including Chronicle/)
- [ ] Run full `lake build` to verify everything compiles together
- [ ] Run `grep -r "sorry" Cslib/Logics/Bimodal/Metalogic/Algebraic/ Cslib/Logics/Bimodal/Metalogic/Bundle/ Cslib/Logics/Bimodal/Metalogic/BXCanonical/` to inventory all sorries
- [ ] Verify sorry count is approximately 50 (matching source)
- [ ] Verify all namespace translations are correct (spot-check 5 files)

**Timing**: 1.5 hours

**Depends on**: 11

**Files to modify/create**:
- `Cslib/Logics/Bimodal/Metalogic/Algebraic/Algebraic.lean` - new (barrel)
- `Cslib/Logics/Bimodal/Metalogic/Bundle/Bundle.lean` - new (barrel)
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/BXCanonical.lean` - new (barrel)

**Verification**:
- Full `lake build` succeeds with no errors
- All barrel imports resolve
- Sorry count matches expected (~50)
- `completeness_dense` is accessible via barrel imports

## Testing & Validation

- [ ] `lake build` succeeds after each phase (12 checkpoints)
- [ ] `completeness_dense` theorem compiles with correct type signature
- [ ] All ~50 sorries are preserved from source (no new sorries introduced except for WeakCanonical stubs)
- [ ] WeakCanonical sorry-stubs are clearly marked with TODO comments referencing task 36
- [ ] Namespace translation is consistent: `Cslib.Logic.Bimodal.Metalogic.*`
- [ ] Type polymorphism: all files use `Formula Atom` with `{Atom : Type*}`
- [ ] Variable naming: `S` renamed to `Omega` where scoped temporal notation conflicts

## Artifacts & Outputs

- `specs/035_port_dense_completeness_bimodal/plans/01_dense-completeness-plan.md` (this file)
- `Cslib/Logics/Bimodal/Theorems/Combinators.lean` (new)
- `Cslib/Logics/Bimodal/Theorems/GeneralizedNecessitation.lean` (new)
- `Cslib/Logics/Bimodal/Theorems/Propositional/Core.lean` (new)
- `Cslib/Logics/Bimodal/Theorems/Propositional/Connectives.lean` (new)
- `Cslib/Logics/Bimodal/Theorems/TemporalDerived.lean` (new)
- `Cslib/Logics/Bimodal/Syntax/Subformulas.lean` (new)
- `Cslib/Logics/Bimodal/Syntax/SubformulaClosure/` (3 new files)
- `Cslib/Logics/Bimodal/Metalogic/Algebraic/` (10 new files + barrel)
- `Cslib/Logics/Bimodal/Metalogic/Bundle/` (11 new files + barrel)
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/` (12 new files including Chronicle/ + barrel)

## Rollback/Contingency

- Each phase produces independently verifiable files; if a later phase fails, earlier phases remain valid
- If WeakCanonical sorry-stubs cause unexpected issues in ChronicleToCountermodel.lean, fall back to porting only the dense-path functions and deferring the rest
- If Mathlib API differences in Chronicle/ are extensive, use `sorry` as temporary placeholders and track in a follow-up error report
- Git history preserves pre-port state; `git revert` on the phase commit to undo
