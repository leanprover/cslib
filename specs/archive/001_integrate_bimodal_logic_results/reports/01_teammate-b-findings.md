# Teammate B Findings: Dependency Analysis, Modularity & PR Strategy

**Task**: Integrate BimodalLogic results into cslib for upstream PRs
**Date**: 2026-06-08
**Angle**: Alternative approaches — dependency graph, version compatibility, PR ordering

## Key Findings

1. **BimodalLogic is a large, deeply layered project** (~160 non-boneyard Lean files) with a clear dependency spine: Syntax → Semantics → ProofSystem → Theorems → Metalogic. The Automation/ subtree (~20 files) is entirely ML-pipeline tooling (dataset generators, tableau bridges, exporters) and should NOT be integrated into cslib.

2. **cslib already has a `Cslib.Logics.Modal` module** (3 files, ~310 lines total) covering basic single-modality modal logic (K, T, B, 4, 5, S4, S5, D), the Modal Cube, and denotational semantics. BimodalLogic's TM logic is a fundamentally different system — bimodal (S5 □ + temporal Until/Since over linear orders), with its own `Formula`, `Axiom`, `Derivation`, and `Semantics` types. These systems are NOT compatible at the type level but could coexist under `Cslib.Logics.Temporal` or `Cslib.Logics.BimodalTemporal`.

3. **Version gap is significant**: BimodalLogic uses Lean `v4.27.0-rc1` + Mathlib `v4.27.0-rc1`; cslib uses Lean `v4.31.0-rc1` + Mathlib at commit `eb15deb`. This is a ~4-version gap. The code will need porting (module keyword changes, API drift in Mathlib, `public import`/`module` syntax). cslib also uses `module` declarations, `@[expose] public section`, `@[scoped grind]` extensively — BimodalLogic uses none of these.

4. **Sorry landscape**: The core theory stack (Syntax, Semantics, ProofSystem, FrameConditions, Metalogic/Core, Metalogic/Decidability, Metalogic/Decidability/FMP, ConservativeExtension, SoundnessLemmas, Separation) is fully sorry-free — 87 of 87 files. The advanced completeness proofs (Bundle: 8/14, BXCanonical: 4/7, WeakCanonical: 8/14, Algebraic: 9/11) have sorries in ongoing work. A few Theorems have sorries (ModalS5, Perpetuity/Bridge, TemporalDerived).

5. **cslib uses strict coding conventions**: PR titles must follow `feat:`, `fix:`, `chore:` etc. format; all files must `import Cslib.Init`; `lake shake` import minimization is enforced; linting with mathlib-style linters is active; `@[expose] public section` and `module` syntax is standard.

## Dependency Graph (Import Chain Analysis)

```
Layer 0 (Foundation):
  Syntax.Atom         ← Mathlib.Data.Finset.Basic, Mathlib.Data.Countable.Basic, ...
  Syntax.Formula      ← Syntax.Atom

Layer 1 (Syntax):
  Syntax.Context      ← Syntax.Formula
  Syntax.BigConj      ← Syntax.Formula
  Syntax.Subformulas  ← Syntax.Formula, Mathlib.Data.List.Basic
  Syntax.SubformulaClosure/* ← Syntax.Formula (3 files)

Layer 2 (Semantics):
  Semantics.TaskFrame    ← Mathlib.Algebra.Order.Group.Defs, Mathlib.Data.Fintype.Basic
  Semantics.WorldHistory ← Semantics.TaskFrame
  Semantics.TaskModel    ← Semantics.TaskFrame, Semantics.WorldHistory, Syntax.Formula
  Semantics.Truth        ← Semantics.TaskModel, Semantics.WorldHistory, Syntax.Formula
  Semantics.Validity     ← Semantics.Truth, Syntax.Context, Mathlib.Order.SuccPred.*

Layer 3 (ProofSystem):
  ProofSystem.Axioms       ← Syntax.Formula
  ProofSystem.Derivation   ← Syntax.{Formula,Context}, ProofSystem.Axioms
  ProofSystem.Derivable    ← ProofSystem.Derivation, Syntax.Context
  ProofSystem.Substitution ← ProofSystem.Derivation, Syntax.Formula
  ProofSystem.LinearityDerivedFacts ← ProofSystem.{Derivation,Axioms}

Layer 4 (Theorems):
  Theorems.Combinators      ← ProofSystem.Derivation
  Theorems.Propositional/*  ← ProofSystem.Derivation (3 files)
  Theorems.ModalS5          ← ProofSystem.Derivation
  Theorems.TemporalDerived  ← ProofSystem.Derivation
  Theorems.Perpetuity/*     ← ProofSystem.Derivation (3 files)

Layer 5a (FrameConditions):
  FrameConditions.FrameClass     ← Mathlib.Algebra.Order.Group.*, Mathlib.Data.Int.*
  FrameConditions.Validity       ← Semantics.Validity, FrameConditions.FrameClass
  FrameConditions.Soundness      ← (frame-specific soundness)
  FrameConditions.Compatibility  ← (cross-frame-class reasoning)

Layer 5b (Metalogic/Core):
  Core.DeductionTheorem    ← ProofSystem.Derivation, Theorems.Combinators
  Core.MaximalConsistent   ← ProofSystem, Semantics, Core.DeductionTheorem, Theorems
  Core.MCSProperties       ← Core.MaximalConsistent
  Core.RestrictedMCS/*     ← Core.MaximalConsistent (2 files)

Layer 6 (Soundness):
  SoundnessLemmas/*        ← Semantics.Truth, ProofSystem.Derivation
  Soundness                ← ProofSystem.Derivation, Semantics.Validity, SoundnessLemmas
  DenseSoundness           ← Soundness, Semantics.Validity
  DiscreteSoundness        ← Soundness, Semantics.Validity

Layer 7 (Completeness):
  Completeness             ← ProofSystem, Semantics, Soundness, Core.{MaximalConsistent,MCSProperties}

Layer 8 (Decidability — independent of Completeness):
  Decidability.SignedFormula        ← Syntax
  Decidability.Tableau             ← Decidability.SignedFormula
  Decidability.Closure             ← (subformula closure)
  Decidability.Saturation          ← Decidability.{Closure,Tableau}
  Decidability.ProofExtraction     ← Decidability.{Saturation,Tableau}
  Decidability.Correctness         ← Decidability.*
  Decidability.DecisionProcedure   ← Decidability.{Correctness,ProofExtraction}
  Decidability.CountermodelExtraction ← Decidability.*
  Decidability.FMP/*               ← (7 files: Filtration, ClosureMCS, FiniteModel, etc.)

Layer 9+ (Advanced, incomplete):
  Algebraic/*              ← Core.*, Theorems.* (11 files, 2 with sorry)
  Bundle/*                 ← Core.*, Theorems.* (14 files, 6 with sorry)
  BXCanonical/*            ← Core.*, (7 files, 3 with sorry)
  WeakCanonical/*          ← (14 files, 6 with sorry)
  WeakCanonical/Separation/* ← (11 files, 0 sorry — clean!)
  ConservativeExtension/*  ← (4 files, 0 sorry)
```

## Version Compatibility Analysis

| Aspect | BimodalLogic | cslib | Gap |
|--------|-------------|-------|-----|
| Lean toolchain | v4.27.0-rc1 | v4.31.0-rc1 | 4 minor versions |
| Mathlib | v4.27.0-rc1 (tag) | eb15deb (commit) | Significant drift |
| `module` keyword | Not used | Required in all files | Must add |
| `public import` | Not used | Required style | Must convert |
| `@[expose] public section` | Not used | Standard pattern | Must add |
| `import Cslib.Init` | N/A | Required for all files | Must add |
| Namespace | `Bimodal.*` | `Cslib.Logic.*` | Full rename |
| Linting | None | mathlib-style linting | Must pass linters |
| `lake shake` | Not used | Import minimization enforced | Must run |

**Porting effort per file**: Estimated ~30-60 minutes per file for mechanical changes (namespace rename, module/public import conversion, Init import, linting fixes), plus variable time for Mathlib API breakages.

## Proposed PR Strategy (Ordered List of Independent PRs)

The key principle: each PR should be **self-contained**, **sorry-free**, and **independently reviewable**. PRs are ordered by dependency — earlier PRs are prerequisites for later ones.

### PR 1: Temporal Syntax (Layer 0-1)
**Files**: Syntax.{Atom, Formula, Context, BigConj, Subformulas}
**Lines**: ~2,500
**Dependencies**: Mathlib only (no cslib dependencies beyond Init)
**Target path**: `Cslib/Logics/Temporal/Syntax/`
**Sorry count**: 0
**Notes**: Foundation for everything else. Self-contained. Includes `Formula` type with Box/Until/Since constructors, `Atom` type with freshness, `Context` as List Formula. Does NOT include SubformulaClosure (save for decidability PR).

### PR 2: Temporal Semantics — Task Frames and Truth (Layer 2)
**Files**: Semantics.{TaskFrame, WorldHistory, TaskModel, Truth, Validity}
**Lines**: ~2,200
**Dependencies**: PR 1 + Mathlib (Algebra.Order.Group, Order.SuccPred)
**Target path**: `Cslib/Logics/Temporal/Semantics/`
**Sorry count**: 0
**Notes**: Defines task frames (linear temporal orders), world histories, truth evaluation, and validity notions. Completely independent of cslib's existing Modal module.

### PR 3: Proof System (Layer 3)
**Files**: ProofSystem.{Axioms, Derivation, Derivable, Substitution, LinearityDerivedFacts}
**Lines**: ~2,000
**Dependencies**: PR 1 only
**Target path**: `Cslib/Logics/Temporal/ProofSystem/`
**Sorry count**: 0
**Notes**: Hilbert-style axiom system with 42 axiom constructors, derivation rules (MP, necessitation, temporal generalization), substitution. Completely sorry-free.

### PR 4: Derived Theorems — Propositional and Modal (Layer 4, partial)
**Files**: Theorems.{Combinators, Propositional/Core, Propositional/Connectives, Propositional/Reasoning, ContextualProofs, GeneralizedNecessitation}
**Lines**: ~3,000
**Dependencies**: PR 3
**Target path**: `Cslib/Logics/Temporal/Theorems/`
**Sorry count**: 0
**Notes**: Core derived theorems. Excludes ModalS5.lean (has sorry), TemporalDerived.lean (mostly sorry-free but references archived sorry-tainted items), and Perpetuity/* (Bridge.lean has sorry). These can come in follow-up PRs.

### PR 5: Frame Conditions and Soundness (Layers 5a, 6)
**Files**: FrameConditions.{FrameClass, Validity, Soundness, Compatibility} + SoundnessLemmas.{Core, DenseValidity, FrameClassVariants} + Soundness.lean + DenseSoundness.lean + DiscreteSoundness.lean
**Lines**: ~3,500
**Dependencies**: PR 2 + PR 3
**Target path**: `Cslib/Logics/Temporal/FrameConditions/` + `Cslib/Logics/Temporal/Metalogic/Soundness/`
**Sorry count**: 4 in Soundness.lean (check if these are in comments/docstrings only — the grep showed them in documentation lines, not actual code)
**Notes**: Frame condition typeclasses (Dense, Discrete, AllOrders), soundness theorems for each frame class. Largely sorry-free.

### PR 6: Deduction Infrastructure and MCS Theory (Layer 5b)
**Files**: Core.{DeductionTheorem, MaximalConsistent, MCSProperties, RestrictedMCS/Basic, RestrictedMCS/Deferral}
**Lines**: ~2,500
**Dependencies**: PR 3 + PR 4
**Target path**: `Cslib/Logics/Temporal/Metalogic/Core/`
**Sorry count**: 0
**Notes**: Deduction theorem, maximal consistent set construction (Lindenbaum's lemma), MCS properties. Foundation for completeness.

### PR 7: Completeness (Layer 7)
**Files**: Completeness.lean
**Lines**: ~520
**Dependencies**: PR 5 + PR 6
**Target path**: `Cslib/Logics/Temporal/Metalogic/`
**Sorry count**: 0
**Notes**: Strong completeness theorem. Depends on soundness and MCS infrastructure.

### PR 8: Decidability and Tableau (Layer 8)
**Files**: Decidability.{SignedFormula, Tableau, Closure, Saturation, ProofExtraction, Correctness, DecisionProcedure, CountermodelExtraction, TraceCertificate, TraceExport} + SubformulaClosure.{Closure, NestingDepth, TemporalFormulas} + Decidability.FMP.{Filtration, ClosureMCS, FiniteModel, TruthPreservation, FMP, DiscreteFMP, DenseFMP}
**Lines**: ~10,000
**Dependencies**: PR 3 + PR 6 (some parts) — importantly, this is INDEPENDENT of PR 5/7 (Soundness/Completeness)
**Target path**: `Cslib/Logics/Temporal/Metalogic/Decidability/`
**Sorry count**: 0
**Notes**: Complete decision procedure via analytic tableaux, finite model property proof via filtration, countermodel extraction. This is a major result and entirely sorry-free. Could potentially split into FMP (PR 8a) and Decision Procedure (PR 8b).

### PR 9: Separation and Normal Forms (Layer 9, partial)
**Files**: WeakCanonical/Separation/* (11 files)
**Lines**: ~3,500
**Dependencies**: PR 3 + PR 4 + PR 6
**Target path**: `Cslib/Logics/Temporal/Metalogic/Separation/`
**Sorry count**: 0
**Notes**: Separation theorem (temporal formulas can be decomposed). Entirely sorry-free despite being in the advanced WeakCanonical directory.

### PR 10: Conservative Extension (Layer 9, partial)
**Files**: ConservativeExtension.{ExtFormula, ExtDerivation, Substitution, Lifting}
**Lines**: ~1,500
**Dependencies**: PR 3
**Target path**: `Cslib/Logics/Temporal/Metalogic/ConservativeExtension/`
**Sorry count**: 0
**Notes**: Conservative extension results. Self-contained and sorry-free.

### Future PRs (when sorries are resolved):
- **Algebraic Completeness** (Algebraic/*): 9/11 files sorry-free
- **Bundle Construction** (Bundle/*): 8/14 files sorry-free
- **BX Canonical Model** (BXCanonical/*): 4/7 files sorry-free
- **Weak Canonical / EF Games / Expressiveness** (WeakCanonical/*): 8/14 files sorry-free
- **ModalS5 Theorems**: 1 sorry remaining
- **Perpetuity Theorems**: Bridge.lean has sorry

### NOT for integration:
- **Automation/** (20+ files): ML training data generators, tableau bridges, proof step extractors. These are project-specific tooling, not library material.
- **Examples/** (2 files): Demonstration files, not library material.
- **Boneyard/** (archived dead code): Excluded by lakefile.

## Evidence/Examples

**cslib PR title convention** (from recent commits):
```
feat: proof of Myhill-Nerode theorem for DFAs (#491)
feat(FLP): distributed algorithms for solving the consensus problem (#556)
feat(MachineLearning/PACLearning): add VersionSpace abstraction (#592)
chore: Bump `mathlib` dependency to eb15deb (#598)
```

Suggested PR titles for the integration:
```
feat(Logics/Temporal): bimodal temporal logic syntax (PR 1)
feat(Logics/Temporal): task frame semantics and truth evaluation (PR 2)
feat(Logics/Temporal): Burgess-Xu proof system for TM logic (PR 3)
feat(Logics/Temporal): derived theorems for propositional and modal reasoning (PR 4)
feat(Logics/Temporal): frame conditions and soundness theorems (PR 5)
feat(Logics/Temporal): deduction theorem and maximal consistent sets (PR 6)
feat(Logics/Temporal): strong completeness theorem (PR 7)
feat(Logics/Temporal): decidability via analytic tableaux and finite model property (PR 8)
feat(Logics/Temporal): separation theorem for temporal formulas (PR 9)
feat(Logics/Temporal): conservative extension results (PR 10)
```

**Namespace mapping**:
```
Bimodal.Syntax.*       →  Cslib.Logic.Temporal.Syntax.*
Bimodal.Semantics.*    →  Cslib.Logic.Temporal.Semantics.*
Bimodal.ProofSystem.*  →  Cslib.Logic.Temporal.ProofSystem.*
Bimodal.Theorems.*     →  Cslib.Logic.Temporal.Theorems.*
Bimodal.Metalogic.*    →  Cslib.Logic.Temporal.Metalogic.*
```

Note: cslib uses `Cslib.Logic.Modal` (under `Cslib.Logic` in namespace, `Cslib/Logics/Modal` in path). The file path is `Cslib/Logics/` but the namespace is `Cslib.Logic.` — this is a cslib convention to watch.

## Confidence Level

**High** for the dependency graph and PR ordering — the import chains are deterministic and the sorry analysis is objective.

**Medium** for the version porting effort estimate — the actual breakage from Lean v4.27→v4.31 and Mathlib drift is hard to predict without trying. Some Mathlib APIs may have changed significantly (especially `Order.SuccPred`, `Algebra.Order.Group`).

**Medium** for the namespace/path choice (`Cslib.Logic.Temporal` vs alternatives) — this should be discussed with cslib maintainers on Zulip before starting, as recommended in CONTRIBUTING.md for "new foundational frameworks."
