# Research Report: Port Dense Completeness Infrastructure (Task 35)

## Executive Summary

Task 35 ports the dense completeness infrastructure from the BimodalLogic repository to cslib. The scope includes three directory trees (Algebraic/, Bundle/, BXCanonical/) plus the Chronicle/ pipeline, totaling 37 files on the critical path (25,857 lines) plus 9 off-path files (3,418 lines). Seven external dependencies (4,523 lines) are missing and must be ported first. The task description's "~15,000 lines" is an undercount; the actual transitive closure for `completeness_dense` is approximately 30,000 lines including external deps.

The key deliverable is `completeness_dense`: if a formula is valid on all densely ordered models, then it is derivable in the Dense proof system. This uses the Burgess 1982 chronicle construction over Rat.

## Source Analysis

### Files in Scope (37 on critical path + 9 off-path = 46 total)

#### Algebraic/ (10 files, 3,925 lines)

| File | Lines | Sorries | On Critical Path | Description |
|------|-------|---------|-----------------|-------------|
| LindenbaumQuotient.lean | 440 | 2 | Yes | Quotient construction via provable equivalence |
| BooleanStructure.lean | 447 | 0 | Yes | Boolean algebra instance for Lindenbaum algebra |
| InteriorOperators.lean | 191 | 1 | Yes | G/H as interior operators (T-axioms) |
| UltrafilterMCS.lean | 1,053 | 0 | Yes | Bijection: ultrafilters <-> MCS |
| AlgebraicCompleteness.lean | 191 | 0 | No | Main algebraic theorem (not needed for dense) |
| ParametricCanonical.lean | 246 | 0 | Yes | D-parametric TaskFrame |
| ParametricHistory.lean | 174 | 0 | Yes | D-parametric history conversion |
| ParametricTruthLemma.lean | 472 | 0 | Yes | D-parametric truth lemma |
| ParametricCompleteness.lean | 301 | 0 | Yes | D-parametric completeness |
| RestrictedParametricTruthLemma.lean | 410 | 0 | Yes | Restricted parametric truth lemma |

**Algebraic barrel** (Algebraic.lean, 109 lines): Off-path, re-exports only.

#### Bundle/ (14 files, 6,218 lines)

| File | Lines | Sorries | On Critical Path | Description |
|------|-------|---------|-----------------|-------------|
| FMCSDef.lean | 125 | 0 | Yes | FMCS structure definition |
| FMCS.lean | 17 | 0 | Yes | FMCS barrel import |
| BFMCS.lean | 229 | 0 | Yes | Bundle of FMCS families |
| TemporalContent.lean | 244 | 0 | Yes | Temporal content for MCS |
| WitnessSeed.lean | 648 | 0 | Yes | Forward/backward witness seeds |
| CanonicalFrame.lean | 297 | 0 | Yes | Canonical frame construction |
| SuccRelation.lean | 655 | 7 | Yes | Successor relation on canonical frame |
| ModalSaturation.lean | 521 | 1 | Yes | Modal saturation for MCS |
| TemporalCoherence.lean | 621 | 2 | Yes | G/H propagation proofs |
| UntilSinceCoherence.lean | 211 | 2 | Yes | Until/Since coherence |
| Construction.lean | 260 | 3 | Yes | BFMCS construction |
| CanonicalTaskRelation.lean | 1,041 | 0 | No | Task relation on canonical frame |
| CanonicalIrreflexivity.lean | 177 | 0 | No | Irreflexivity proofs |
| SuccExistence.lean | 1,172 | 4 | No | Successor existence proofs |

#### BXCanonical/ non-Chronicle (13 files, 4,486 lines)

| File | Lines | Sorries | On Critical Path | Description |
|------|-------|---------|-----------------|-------------|
| Frame.lean | 710 | 2 | Yes | BXPoint, canonical ordering, witnesses |
| TruthLemma.lean | 302 | 0 | Yes | Truth lemma by formula induction |
| CanonicalChain.lean | 110 | 1 | Yes | BX axiom lemmas, delegation bridges |
| CanonicalModel.lean | 794 | 0 | Yes | BFMCS Int construction from BX witnesses |
| OrderedSeedConsistency.lean | 254 | 0 | Yes | Ordered seed consistency |
| Completeness.lean | 407 | 7 | Yes | Dense/discrete/mixed completeness theorems |
| Quasimodel/SubformulaClosure.lean | 112 | 0 | Yes | Finite subformula closure |
| Quasimodel/HintikkaPoint.lean | 144 | 0 | Yes | Hintikka point definition |
| Quasimodel/Construction.lean | 841 | 1 | Yes | BX axiom lemmas at MCS level |
| Filtration/DefectChain.lean | 112 | 0 | Yes | Defect chain for filtration |
| Quasimodel/EnrichedClosure.lean | 158 | 0 | No | Enriched closure (off-path) |
| Quasimodel/Realization.lean | 493 | 1 | No | Realization lifting (off-path) |
| Quasimodel/LocusControl.lean | 49 | 0 | No | Locus-control delegation (off-path) |
| BXCanonical.lean | 28 | 0 | No | Barrel import |

#### Chronicle/ (7 files, 14,509 lines)

| File | Lines | Sorries | On Critical Path | Description |
|------|-------|---------|-----------------|-------------|
| ChronicleTypes.lean | 865 | 0 | Yes | Chronicle type definitions |
| RRelation.lean | 1,686 | 1 | Yes | R-relation on chronicle |
| PointInsertion.lean | 3,527 | 1 | Yes | Point insertion construction |
| CounterexampleElimination.lean | 3,487 | 0 | Yes | Counterexample elimination |
| ChronicleConstruction.lean | 1,510 | 0 | Yes | Main chronicle construction |
| ChronicleToCountermodelBasic.lean | 1,163 | 3 | Yes | Dense/discrete case split, cantor_bfmcs_dense |
| ChronicleToCountermodel.lean | 2,271 | 6 | Yes | Gap elimination, mcs_mixed_case_absurd |

### Sorry Inventory

**Total sorries in scope**: ~50 across all files

**Algebraic/ sorries** (3):
- `LindenbaumQuotient.lean` (2): Quotient construction details
- `InteriorOperators.lean` (1): Interior operator property

**Bundle/ sorries** (18):
- `SuccRelation.lean` (7): Successor relation proofs
- `SuccExistence.lean` (4): Successor existence (off-path)
- `Construction.lean` (3): BFMCS construction
- `TemporalCoherence.lean` (2): Temporal coherence
- `UntilSinceCoherence.lean` (2): Until/Since coherence
- `ModalSaturation.lean` (1): Modal saturation

**BXCanonical/ non-Chronicle sorries** (12):
- `Completeness.lean` (7): Inherited via imports; discrete/mixed branches
- `Frame.lean` (2): Frame property proofs
- `CanonicalChain.lean` (1): Chain construction
- `Quasimodel/Construction.lean` (1): MCS-level axiom
- `Quasimodel/Realization.lean` (1): Realization (off-path)

**Chronicle/ sorries** (11):
- `ChronicleToCountermodel.lean` (6): Gap elimination, succ_reaches_dom_N (dead code)
- `ChronicleToCountermodelBasic.lean` (3): Dense/discrete pipeline
- `PointInsertion.lean` (1): Point insertion
- `RRelation.lean` (1): R-relation

All sorries should be ported as-is per the task description.

## Target Analysis

### Already Ported (from tasks 7, 34, 10, 42, and earlier)

| Module | Status | Task |
|--------|--------|------|
| Core/DerivationTree.lean | Ported | Task 6 |
| Core/DeductionTheorem.lean | Ported | Task 7 |
| Core/MaximalConsistent.lean | Ported | Task 7 |
| Core/MCSProperties.lean | Ported | Task 7 |
| Core.lean (barrel) | Ported | Task 7 |
| Completeness.lean (base MCS props) | Ported | Task 34 |
| ProofSystem/* | Ported | Earlier tasks |
| Semantics/* | Ported | Earlier tasks |
| Syntax/Formula.lean | Ported | Earlier tasks |
| Syntax/Context.lean | Ported | Earlier tasks |
| Theorems/Perpetuity/* | Ported | Task 5 |
| Soundness/* | Ported | Earlier tasks |
| Separation/* | Ported | Task 10 |
| Decidability/* | Ported | Tasks 9, 42 |

### NOT Yet Ported (Required External Dependencies)

These are **prerequisites** that must be ported as part of this task or identified as blockers:

| Module | Lines | Sorries | Used By |
|--------|-------|---------|---------|
| Theorems/Combinators.lean | 675 | 0 | 19 files (nearly all) |
| Theorems/GeneralizedNecessitation.lean | 240 | 0 | 7 files |
| Theorems/Propositional/Core.lean | 730 | 0 | 5 files |
| Theorems/Propositional/Connectives.lean | 745 | 0 | 2 files |
| Theorems/TemporalDerived.lean | 788 | 2 | 10 files |
| Syntax/BigConj.lean | 49 | 0 | 2 files (off-path) |
| Syntax/SubformulaClosure/TemporalFormulas.lean | 1,296 | 0 | 4 files |

Additional transitive deps for SubformulaClosure:
- Syntax/Subformulas.lean (229 lines)
- Syntax/SubformulaClosure/Closure.lean (367 lines)
- Syntax/SubformulaClosure/NestingDepth.lean (232 lines)

**Total external deps**: ~5,351 lines (including SubformulaClosure chain)

### NOT Ported and NOT Required for Dense Path

| Module | Why Not Needed |
|--------|----------------|
| WeakCanonical/* (56 files, 52,942 lines) | Only used by completeness/completeness_discrete; completeness_dense uses only Chronicle path |
| Core/RestrictedMCS/* | Not imported by any in-scope file (only mentioned in comments) |
| Syntax/BigConj.lean | Only used by off-path Quasimodel/EnrichedClosure and Realization |

### WeakCanonical Dependency Strategy

The source BXCanonical/Completeness.lean imports `Bimodal.Metalogic.WeakCanonical` and `Bimodal.Metalogic.BXCanonical.Chronicle.ChronicleToCountermodel` (which imports `GoodStructuresModelSurgery`). However:

- `completeness_dense` does NOT reference any WeakCanonical symbol
- The WeakCanonical import is needed only for `completeness` (base) and `completeness_discrete`
- `ChronicleToCountermodel.lean` imports GoodStructuresModelSurgery for gap elimination in the discrete path

**Recommended approach**: Split BXCanonical/Completeness.lean during porting:
1. **Completeness/Dense.lean**: Contains `completeness_dense`, `countermodel_dense_enriched`, `neg_consistent_of_not_derivable` -- NO WeakCanonical dependency
2. **Completeness.lean** (placeholder): Contains `sorry`-stubbed `completeness` and `completeness_discrete` with a TODO for when WeakCanonical is ported

Similarly, ChronicleToCountermodel.lean's WeakCanonical dependency is only for the `mcs_mixed_case_absurd` path and discrete pipeline code. The dense-path functions are in ChronicleToCountermodelBasic.lean. We can:
- Port ChronicleToCountermodelBasic.lean fully (it does NOT import WeakCanonical)
- Port ChronicleToCountermodel.lean with forward-declarations or sorry-stubs for WeakCanonical references

## Dependency Analysis

### Internal Dependency Layers (Porting Order)

**Layer 0 - External prerequisites** (must be ported first):
1. Theorems/Combinators.lean (675 lines, 0 sorries)
2. Theorems/GeneralizedNecessitation.lean (240 lines, 0 sorries)
3. Theorems/Propositional/Core.lean (730 lines, 0 sorries)
4. Theorems/Propositional/Connectives.lean (745 lines, 0 sorries)
5. Theorems/TemporalDerived.lean (788 lines, 2 sorries)
6. Syntax/Subformulas.lean (229 lines, 0 sorries)
7. Syntax/SubformulaClosure/Closure.lean (367 lines, 0 sorries)
8. Syntax/SubformulaClosure/NestingDepth.lean (232 lines, 0 sorries)
9. Syntax/SubformulaClosure/TemporalFormulas.lean (1,296 lines, 0 sorries)

**Layer 1 - Leaf modules** (no internal deps):
- Algebraic/LindenbaumQuotient.lean (440 lines)
- Bundle/FMCSDef.lean (125 lines)
- Bundle/TemporalContent.lean (244 lines)
- BXCanonical/Quasimodel/SubformulaClosure.lean (112 lines)

**Layer 2 - Basic infrastructure**:
- Algebraic/BooleanStructure.lean (depends on LindenbaumQuotient)
- Bundle/FMCS.lean (depends on FMCSDef)
- Bundle/WitnessSeed.lean (depends on TemporalContent)

**Layer 3 - Core infrastructure**:
- Algebraic/InteriorOperators.lean (depends on BooleanStructure)
- Bundle/BFMCS.lean (depends on FMCS)
- Bundle/CanonicalFrame.lean (depends on TemporalContent, WitnessSeed)
- BXCanonical/Quasimodel/HintikkaPoint.lean (depends on SubformulaClosure)

**Layer 4 - Secondary infrastructure**:
- Algebraic/UltrafilterMCS.lean (depends on InteriorOperators)
- Bundle/ModalSaturation.lean (depends on BFMCS)
- Bundle/SuccRelation.lean (depends on TemporalContent, CanonicalFrame, WitnessSeed)
- Bundle/TemporalCoherence.lean (depends on BFMCS, ModalSaturation)
- Bundle/Construction.lean (depends on BFMCS, ModalSaturation)
- BXCanonical/Quasimodel/Construction.lean (depends on HintikkaPoint)
- BXCanonical/Frame.lean (depends on Bundle/TemporalContent, WitnessSeed, CanonicalFrame)

**Layer 5 - Advanced infrastructure**:
- Algebraic/ParametricCanonical.lean (depends on UltrafilterMCS, Bundle/CanonicalFrame)
- Bundle/UntilSinceCoherence.lean (depends on TemporalCoherence, SuccRelation)
- BXCanonical/TruthLemma.lean (depends on Frame)
- BXCanonical/Filtration/DefectChain.lean (depends on Frame, Quasimodel/Construction)
- BXCanonical/CanonicalChain.lean (depends on Frame, Quasimodel/Construction, DefectChain)
- BXCanonical/Chronicle/ChronicleTypes.lean (depends on Bundle/TemporalContent, Frame, ModalSaturation)
- BXCanonical/Chronicle/RRelation.lean (depends on ChronicleTypes, Bundle/WitnessSeed)

**Layer 6 - Deep infrastructure**:
- Algebraic/ParametricHistory.lean (depends on ParametricCanonical, BFMCS)
- BXCanonical/OrderedSeedConsistency.lean (depends on Frame, CanonicalChain)
- BXCanonical/Chronicle/PointInsertion.lean (depends on Frame, OrderedSeedConsistency, ChronicleTypes, RRelation)
- BXCanonical/Chronicle/CounterexampleElimination.lean (depends on ChronicleTypes, RRelation, PointInsertion)

**Layer 7 - Parametric completeness**:
- Algebraic/ParametricTruthLemma.lean (depends on ParametricHistory, TemporalCoherence)
- Algebraic/RestrictedParametricTruthLemma.lean (depends on ParametricTruthLemma, TemporalCoherence)
- Algebraic/ParametricCompleteness.lean (depends on ParametricTruthLemma, Bundle/Construction, ModalSaturation)
- BXCanonical/Chronicle/ChronicleConstruction.lean (depends on ChronicleTypes, RRelation, PointInsertion, CounterexampleElimination)

**Layer 8 - Model construction**:
- BXCanonical/CanonicalModel.lean (depends on CanonicalChain, TruthLemma, FMCSDef, ChronicleTypes, BFMCS)

**Layer 9 - Countermodel**:
- BXCanonical/Chronicle/ChronicleToCountermodelBasic.lean (depends on ChronicleConstruction, CanonicalModel, UntilSinceCoherence, ParametricCompleteness, RestrictedParametricTruthLemma)

**Layer 10 - Gap elimination + completeness_dense**:
- BXCanonical/Chronicle/ChronicleToCountermodel.lean (depends on ChronicleToCountermodelBasic; WeakCanonical only for discrete path)
- BXCanonical/Completeness.lean (depends on ChronicleToCountermodel; WeakCanonical only for discrete path)

## Namespace Mapping

| Source | Target |
|--------|--------|
| `Bimodal.Metalogic.Algebraic.*` | `Cslib.Logic.Bimodal.Metalogic.Algebraic.*` |
| `Bimodal.Metalogic.Bundle.*` | `Cslib.Logic.Bimodal.Metalogic.Bundle.*` |
| `Bimodal.Metalogic.BXCanonical.*` | `Cslib.Logic.Bimodal.Metalogic.BXCanonical.*` |
| `Bimodal.Metalogic.Core.*` | `Cslib.Logic.Bimodal.Metalogic.Core.*` (already exists) |
| `Bimodal.Theorems.*` | `Cslib.Logic.Bimodal.Theorems.*` |
| `Bimodal.Syntax.*` | `Cslib.Logic.Bimodal.Syntax.*` |
| `Formula` (plain) | `Formula Atom` (universe-polymorphic `{Atom : Type*}`) |
| `Set Formula` | `Set (Formula Atom)` |
| `S` (MCS variable) | `Omega` (avoid scoped temporal Since conflict) |

## Key Translation Patterns (from Task 34 experience)

1. **Type polymorphism**: `Formula` -> `Formula Atom` with `{Atom : Type*}`
2. **Frame class genericity**: Task 34 made theorems generic over `{fc : FrameClass}` instead of specializing to `FrameClass.Base`. The same pattern should apply here.
3. **Axiom name mapping**: `Axiom.ex_falso` -> `Axiom.efq`, `Axiom.prop_s` -> `Axiom.imp_s`
4. **Variable naming**: `S` -> `Omega` (avoid scoped temporal Since notation conflict)
5. **`trivial` for FrameClass constraints**: `trivial` -> `FrameClass.base_le fc` when lifting Base derivations
6. **`noncomputable` sections**: Many definitions in Algebraic/ and Chronicle/ are noncomputable

## Risk Assessment

**High Risk Areas**:
1. **Volume**: ~30,000 lines is very large for a single porting task. Recommend splitting into multiple implementation phases.
2. **Missing external dependencies** (4,523+ lines): Theorems/Combinators, GeneralizedNecessitation, Propositional/{Core,Connectives}, TemporalDerived, and SubformulaClosure chain must be ported first.
3. **WeakCanonical dependency**: BXCanonical/Completeness.lean and ChronicleToCountermodel.lean import WeakCanonical (52,942 lines). Must be handled by file splitting or sorry-stubs.
4. **Mathlib compatibility**: Chronicle files import many Mathlib modules (Rat, Archimedean, CountableDenseLinearOrder, SuccPred, Topology). These may have API differences between Mathlib versions.
5. **Universe polymorphism**: Source uses non-polymorphic `Formula`. Target uses `Formula Atom`. This is a pervasive change affecting every file.

**Medium Risk Areas**:
1. **Sorry propagation**: ~50 sorries across in-scope files. All should be ported as-is, but compilation must still succeed around them.
2. **Notation conflicts**: The `S` variable and temporal operators may conflict with scoped notations.
3. **Encodable/Denumerable instances**: CanonicalModel.lean uses `Denumerable.ofNat Formula` which requires `Denumerable (Formula Atom)` in the polymorphic target.

**Low Risk Areas**:
1. **Algebraic layer** (3,925 lines): Clean modular structure, standard algebraic constructions.
2. **Bundle layer** (6,218 lines): Well-isolated temporal coherence infrastructure.
3. **Core BXCanonical** (excluding Chronicle): Standard canonical model construction.

## Recommended Implementation Strategy

### Phase Organization

Given the volume (~30,000 lines), I recommend organizing into 10-12 phases:

**Phase 1** (~5,000 lines): Port external dependencies
- Theorems/Combinators.lean, GeneralizedNecessitation.lean
- Theorems/Propositional/Core.lean, Connectives.lean
- Theorems/TemporalDerived.lean
- Syntax/Subformulas.lean, SubformulaClosure/*, BigConj.lean

**Phase 2** (~2,000 lines): Port Algebraic Layer 1-3
- LindenbaumQuotient, BooleanStructure, InteriorOperators, UltrafilterMCS

**Phase 3** (~2,000 lines): Port Bundle Layer 1-3
- FMCSDef, FMCS, TemporalContent, WitnessSeed, BFMCS, CanonicalFrame

**Phase 4** (~2,500 lines): Port Bundle Layer 4-5
- ModalSaturation, SuccRelation, TemporalCoherence, Construction, UntilSinceCoherence

**Phase 5** (~2,000 lines): Port BXCanonical core
- Frame, TruthLemma, Quasimodel/SubformulaClosure, HintikkaPoint, Construction, Filtration/DefectChain, CanonicalChain

**Phase 6** (~1,500 lines): Port Algebraic parametric modules
- ParametricCanonical, ParametricHistory, ParametricTruthLemma, ParametricCompleteness, RestrictedParametricTruthLemma

**Phase 7** (~1,300 lines): Port BXCanonical secondary
- OrderedSeedConsistency, CanonicalModel

**Phase 8** (~2,500 lines): Port Chronicle types and R-relation
- ChronicleTypes, RRelation

**Phase 9** (~7,000 lines): Port Chronicle core
- PointInsertion, CounterexampleElimination, ChronicleConstruction

**Phase 10** (~3,500 lines): Port countermodel integration
- ChronicleToCountermodelBasic, ChronicleToCountermodel (with sorry stubs for WeakCanonical refs)

**Phase 11** (~400 lines): Port completeness_dense theorem
- BXCanonical/Completeness.lean (split to avoid WeakCanonical dep, or sorry-stub discrete parts)

**Phase 12**: Barrel imports, verification
- BXCanonical/BXCanonical.lean, Algebraic/Algebraic.lean barrel imports
- Full `lake build` verification

### Off-Path Files Decision

The 9 off-path files (3,418 lines) should be included for completeness of the directory structure:
- Algebraic/AlgebraicCompleteness.lean (191 lines) - simple, depends only on UltrafilterMCS
- BXCanonical barrel files (28+49 lines) - trivial
- Quasimodel/EnrichedClosure, Realization, LocusControl (700 lines) - needed for barrel
- Bundle/CanonicalIrreflexivity, CanonicalTaskRelation, SuccExistence (2,390 lines) - larger, consider deferring

**Recommendation**: Port the small off-path files (Algebraic/AlgebraicCompleteness, Quasimodel/*) as they're trivial. Defer Bundle/CanonicalIrreflexivity, CanonicalTaskRelation, and SuccExistence to a follow-up task since they're not on the critical path and add 2,390 lines.

## Scope Clarification

### In Scope (Task 35)

All 37 critical-path files plus small off-path files, totaling ~40 files.

### Out of Scope

- WeakCanonical/ (56 files, 52,942 lines) -- separate task
- Bundle/CanonicalIrreflexivity, CanonicalTaskRelation, SuccExistence -- defer to follow-up
- Core/RestrictedMCS/* -- not used
- Decidability/FMP/* -- separate task (42)

### Overlap with Completed Tasks

- **Task 34** (completed): Ported `Completeness.lean` (base MCS properties). No overlap -- task 35 creates new files.
- **Task 42** (completed): Ported decidability/tableau. No overlap.
- **Task 10** (completed): Ported separation theorem. No overlap.
- **Task 7** (completed): Ported Core/ infrastructure. No overlap -- task 35 uses these as dependencies.
