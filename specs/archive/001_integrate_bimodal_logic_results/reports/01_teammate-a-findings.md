# Teammate A Findings: Primary Structure & Mapping

## Key Findings

BimodalLogic is a large Lean 4 library (~211 non-Boneyard source files) formalizing bimodal logic TM (Tense and Modality), combining S5 modal logic with linear temporal logic (Until/Since). It includes:

1. **Syntax**: A `Formula` type with 6 primitive constructors (atom, bot, imp, box, untl, snce) plus ~20 derived operators (G, H, F, P, diamond, always, sometimes, release, weak_until, etc.)
2. **Proof System**: A Hilbert-style axiom system with 42 axiom constructors organized across 8 layers (propositional, S5 modal, BX temporal, interaction, uniformity, Prior, Z1, density) with frame class classification (Base/Dense/Discrete)
3. **Semantics**: Task frame semantics with world histories, truth evaluation, and validity — parameterized over an ordered additive commutative group D (supporting Int, Rat, Real)
4. **Metalogic**: Soundness (sorry-free for base/dense/discrete), completeness (has sorries — chronicle construction), and decidability (sorry-free tableau procedure)
5. **Derived Theorems**: Perpetuity principles P1-P6, modal S4/S5 theorems, propositional reasoning, temporal derived facts
6. **Automation**: Proof search tactics (modal_search, temporal_search), formula enumeration, dataset export tools
7. **Decidability/FMP**: Finite model property via filtration, tableau decision procedure, signed formula calculus, countermodel extraction
8. **Weak Canonical / EF Games / Separation**: Reynolds/Doets pipeline, Ehrenfeucht-Fraïssé games, separation theorem, expressive completeness
9. **Conservative Extension**: Extension formulas and lifting results

The cslib repo has a nascent modal logic module (3 files under `Cslib/Logics/Modal/`) with a simpler single-modality `Proposition` type (atom/neg/and/diamond) and semantic approach (Model with relation + valuation, `Satisfies` relation), including the Modal Cube (K through S5) with frame condition proofs (T/B/4/5/D axiom soundness and completeness). It also has a propositional logic module under `Cslib/Logics/Propositional/`.

**Key version mismatch**: BimodalLogic uses Lean 4.27.0-rc1 + Mathlib v4.27.0-rc1; cslib uses Lean 4.31.0-rc1. This is a significant gap requiring Mathlib API migration.

**Key style mismatch**: cslib uses `module` declarations, `public import`, `@[expose] public section`, and the `Cslib.*` namespace convention. BimodalLogic uses traditional `import` and the `Bimodal.*` namespace. All files would need refactoring for cslib conventions.

## BimodalLogic Module Map

### Core (sorry-free, suitable for PR)

| Module | What it defines/proves | Lines (est.) |
|--------|----------------------|--------------|
| `Syntax/Atom.lean` | Structured atom type with freshness | ~100 |
| `Syntax/Formula.lean` | 6-constructor Formula type, derived operators, complexity, swap_temporal | ~695 |
| `Syntax/Subformulas.lean` | Subformula relation | ~100 |
| `Syntax/SubformulaClosure/` | Fischer-Ladner closure, nesting depth | ~300 |
| `Syntax/Context.lean` | Formula sets/contexts | ~100 |
| `Syntax/BigConj.lean` | Big conjunction operations | ~100 |
| `ProofSystem/Axioms.lean` | 42 axiom constructors, FrameClass | ~485 |
| `ProofSystem/Derivable.lean` | Derivability notation | ~50 |
| `ProofSystem/Derivation.lean` | Derivation trees (axiom/mp/nec/td) | ~200 |
| `ProofSystem/Substitution.lean` | Uniform substitution | ~200 |
| `ProofSystem/LinearityDerivedFacts.lean` | Derived linearity facts | ~150 |
| `Semantics/TaskFrame.lean` | TaskFrame structure, nullity, compositionality, converse | ~300 |
| `Semantics/TaskModel.lean` | Task model (frame + valuation) | ~100 |
| `Semantics/WorldHistory.lean` | World histories (functions from time to world state) | ~150 |
| `Semantics/Truth.lean` | Truth evaluation (`respects_task`, `satisfies`) | ~300 |
| `Semantics/Validity.lean` | Validity definitions | ~100 |
| `Theorems/Propositional/` | Core, Connectives, Reasoning (~3 files) | ~500 |
| `Theorems/Combinators.lean` | Derived proof combinators | ~200 |
| `Theorems/ContextualProofs.lean` | Contextual/hypothetical derivation | ~200 |
| `Theorems/GeneralizedNecessitation.lean` | Generalized necessitation rule | ~100 |
| `Theorems/ModalS4.lean` | S4 derived theorems | ~200 |
| `Theorems/ModalS5.lean` | S5 derived theorems (has some sorry) | ~200 |
| `Theorems/TemporalDerived.lean` | temp_k_dist, temp_4 derived (has sorry) | ~200 |
| `Theorems/Perpetuity/` | P1-P6 perpetuity principles (~3 files, has sorry) | ~500 |
| `Metalogic/Core/` | MCS, deduction theorem, restricted MCS (~5 files) | ~800 |
| `Metalogic/Soundness.lean` | Soundness theorem (sorry-free) | ~400 |
| `Metalogic/SoundnessLemmas/` | Soundness helpers (~3 files) | ~400 |
| `Metalogic/DenseSoundness.lean` | Dense soundness (sorry-free) | ~300 |
| `Metalogic/DiscreteSoundness.lean` | Discrete soundness (sorry-free) | ~300 |
| `Metalogic/Decidability/` | Tableau procedure, FMP, signed formulas, closure (~12 files) | ~2000 |
| `FrameConditions/` | Frame class typeclasses, soundness/validity (~4 files) | ~600 |

### In Progress (has sorries)

| Module | Status |
|--------|--------|
| `Metalogic/Bundle/` | BFMCS infrastructure, partial | 
| `Metalogic/Algebraic/` | Parametric completeness, partial |
| `Metalogic/BXCanonical/` | Chronicle construction, partial |
| `Metalogic/WeakCanonical/` | Reynolds pipeline, partial |
| `Metalogic/ConservativeExtension/` | Extension results |
| `Examples/` | Demo files (has sorry) |

### Not for Integration

| Module | Reason |
|--------|--------|
| `Boneyard/` | Archived dead code |
| `Automation/` | Project-specific tooling (dataset export, benchmark, bridge REPL) |

## cslib Directory Structure (Relevant Areas)

```
Cslib/
├── Logics/
│   ├── Modal/           # 3 files: Basic (Model, Proposition, Satisfies, axiom proofs),
│   │                    #   Cube (K-S5 logics), Denotation (denotational semantics)
│   ├── Propositional/   # 2 files: Defs (Proposition type, Theory, IPL/CPL), NaturalDeduction
│   ├── HML/             # 2 files: Hennessy-Milner Logic
│   └── LinearLogic/     # 5 files: Classical Linear Logic
├── Foundations/
│   ├── Logic/           # InferenceSystem, LogicalEquivalence
│   ├── Semantics/       # LTS, FLTS (Labelled/Finite transition systems)
│   └── Syntax/          # Context, Substitution, Congruence
└── (other dirs not relevant)
```

## Recommended Mapping (BimodalLogic → cslib)

### Tier 1: Standalone, Sorry-Free, High-Value PRs

These can be submitted independently with no cross-dependencies:

| BimodalLogic Source | cslib Target | PR Scope | Notes |
|---|---|---|---|
| `Syntax/Formula.lean` + `Syntax/Atom.lean` | `Cslib/Logics/Bimodal/Syntax/Formula.lean` | New bimodal formula type | Core dependency for everything; must go first. Rename namespace to `Cslib.Logic.Bimodal` |
| `Syntax/Subformulas.lean` + `SubformulaClosure/` | `Cslib/Logics/Bimodal/Syntax/Subformulas.lean` etc. | Subformula operations | Depends on Formula |
| `ProofSystem/Axioms.lean` + `Derivation.lean` + `Derivable.lean` | `Cslib/Logics/Bimodal/ProofSystem/` | Hilbert proof system | Depends on Syntax |
| `Semantics/TaskFrame.lean` + `TaskModel.lean` + `WorldHistory.lean` + `Truth.lean` + `Validity.lean` | `Cslib/Logics/Bimodal/Semantics/` | Task frame semantics | Depends on Syntax |
| `Metalogic/Soundness.lean` + `SoundnessLemmas/` + `DenseSoundness` + `DiscreteSoundness` | `Cslib/Logics/Bimodal/Metalogic/Soundness.lean` | Soundness theorem | Depends on ProofSystem + Semantics; sorry-free |
| `Metalogic/Core/` (MCS, deduction theorem) | `Cslib/Logics/Bimodal/Metalogic/Core/` | MCS infrastructure | General MCS theory; could be useful standalone |

### Tier 2: Sorry-Free but Larger PRs

| BimodalLogic Source | cslib Target | Notes |
|---|---|---|
| `Theorems/Propositional/` + `Combinators` + `ContextualProofs` | `Cslib/Logics/Bimodal/Theorems/` | Derived theorems |
| `Theorems/ModalS4.lean` | `Cslib/Logics/Bimodal/Theorems/ModalS4.lean` | S4 theorems |
| `Metalogic/Decidability/` | `Cslib/Logics/Bimodal/Metalogic/Decidability/` | Tableau + FMP; large (~12 files) |
| `FrameConditions/` | `Cslib/Logics/Bimodal/FrameConditions/` | Frame class architecture |
| `ProofSystem/Substitution.lean` | `Cslib/Logics/Bimodal/ProofSystem/Substitution.lean` | Uniform substitution |

### Tier 3: Has Sorries (future PRs after completion)

| Module | Notes |
|---|---|
| `Metalogic/Bundle/`, `Algebraic/`, `BXCanonical/` | Completeness infrastructure |
| `Metalogic/WeakCanonical/` | Reynolds/Doets pipeline |
| `Theorems/Perpetuity/` | P1-P6 principles (some sorry) |
| `Theorems/ModalS5.lean` | S5 (has sorry) |
| `Theorems/TemporalDerived.lean` | Temporal derived (has sorry) |

### Not Mapped (cslib-incompatible)

| Module | Reason |
|---|---|
| `Automation/` (all files) | Project-specific ML/benchmark tooling, not a library contribution |
| `Boneyard/` | Archived dead code |
| `Examples/` | Could be included as tests/examples but has sorry |

## Overlap Analysis

The existing `Cslib.Logics.Modal` uses a **fundamentally different architecture**:
- cslib's `Proposition` is simpler (atom/neg/and/diamond), no temporal operators
- cslib uses a semantic `Satisfies` relation directly (no proof system)
- cslib defines logics as sets of valid propositions in model classes

BimodalLogic's `Formula` is richer (atom/bot/imp/box/untl/snce) with a Hilbert proof system. The two do NOT conflict — they're different logics. The bimodal content should live in a new `Cslib/Logics/Bimodal/` directory, not merged into the existing `Modal/`.

**Potential for shared infrastructure**: Both repos define notions like "maximal consistent set," "frame conditions," and "satisfaction." There may be opportunities to factor common patterns into `Cslib/Foundations/Logic/` (e.g., a general MCS construction), but this is a stretch goal, not a blocker.

## Confidence Level

**High** for the structural mapping and modular PR strategy.
**Medium** for the Mathlib version migration effort (4.27→4.31 is a significant gap).
**Low** for estimating total effort — the sorry-free core alone is ~8,000+ lines across ~30 files.
