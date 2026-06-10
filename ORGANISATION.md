# Code Organisation

This document gives an overview of how the codebase is structured, in terms of directories.

**Note** that this organisation is still under active discussion and is subject to change.

## Top-Level Structure

- `Cslib/` -- Root namespace of the Computer Science library.
  - `Foundations/` -- General-purpose definitions and results shared across specific logics.
  - `Logics/` -- Specific logic formalizations (propositional, modal, temporal, bimodal, etc.).
  - `Languages/` -- Modelling and programming languages (Boole, CCS, Lambda Calculus, Pi Calculus, etc.).
  - `Computability/` -- Automata theory, Turing machines, partial recursive functions, register machines.
  - `Algorithms/` -- Algorithm formalizations.
  - `Crypto/` -- Cryptography formalizations.
  - `MachineLearning/` -- Machine learning formalizations.
  - `Probability/` -- Probability theory formalizations.
  - `Init.lean` -- Root initialization file.

## Foundations

The `Foundations/` directory provides infrastructure shared across all specific logics. It defines abstract proof systems, connective typeclasses, and generic theorems that are instantiated by each logic.

```
Foundations/
├── Logic/                     -- Abstract proof system infrastructure
│   ├── Axioms.lean            -- Connective typeclasses (HasBot, HasImp, HasBox, etc.)
│   ├── Connectives.lean       -- Derived connective abbreviations
│   ├── InferenceSystem.lean   -- Abstract inference system and derivability
│   ├── ProofSystem.lean       -- Hilbert-style proof system typeclasses
│   ├── LogicalEquivalence.lean-- Abstract logical equivalence
│   ├── Theorems.lean          -- Barrel import for all theorem modules
│   ├── Theorems/
│   │   ├── Combinators.lean   -- S, K, B combinators and imp_trans
│   │   ├── BigConj.lean       -- Big conjunction theorems
│   │   ├── Propositional/     -- Propositional logic theorems
│   │   │   ├── Core.lean      -- LEM, DNE, EFQ, conjunction elimination
│   │   │   └── Connectives.lean-- Contraposition, De Morgan, etc.
│   │   ├── Modal/             -- Modal logic theorems
│   │   │   ├── Basic.lean     -- Box monotonicity, box distribution
│   │   │   └── S5.lean        -- S5-specific derived theorems
│   │   └── Temporal/          -- Temporal logic theorems
│   │       └── TemporalDerived.lean -- G/H distribution, transitivity
│   └── Metalogic/
│       ├── Consistency.lean       -- Consistency and maximal consistency
│       └── DeductionHelpers.lean  -- Deduction theorem helpers
├── Data/                      -- General-purpose data structures
│   ├── HasFresh.lean          -- Fresh name generation
│   ├── Relation.lean          -- Relation utilities
│   ├── ListHelpers.lean       -- List helper lemmas
│   ├── RelatesInSteps.lean    -- Step-indexed relations
│   ├── DecidableEqZero.lean   -- Decidable equality to zero
│   ├── StackTape.lean         -- Stack/tape data structures
│   └── BiTape.lean            -- Bidirectional tape
├── Combinatorics/             -- Combinatorial results
│   └── InfiniteGraphRamsey.lean
├── Control/                   -- Control flow abstractions
│   └── Monad/
│       └── Free/              -- Free monads
├── Semantics/                 -- Operational semantics
│   ├── LTS/                   -- Labelled transition systems
│   │   └── LTSCat/           -- LTS category theory
│   └── FLTS/                  -- Functional LTS
├── Syntax/                    -- Abstract syntax infrastructure
│   ├── HasAlphaEquiv.lean     -- Alpha equivalence
│   ├── HasWellFormed.lean     -- Well-formedness
│   ├── HasSubstitution.lean   -- Substitution
│   ├── Context.lean           -- Contexts
│   └── Congruence.lean        -- Congruence relations
└── Lint/                      -- Custom linting rules
    └── Basic.lean
```

## Logics

The `Logics/` directory contains specific logic formalizations. Each logic instantiates the abstract infrastructure from `Foundations/Logic/`.

### Module Dependency Hierarchy

```
Foundations/Logic  (abstract infrastructure)
       │
       ▼
  Propositional    (propositional logic: formulas, proof system, metalogic)
       │
       ├──────────────────┐
       ▼                  ▼
     Modal            Temporal     (extend propositional with □ or U/S)
       │                  │
       └──────┬───────────┘
              ▼
           Bimodal               (combines modal + temporal, BX axiom system)
```

### Propositional Logic (`Logics/Propositional/`)

```
Propositional/
├── Defs.lean                  -- Formula type, proof system instances
├── NaturalDeduction/          -- Natural deduction proof system
│   └── Basic.lean
├── ProofSystem/               -- Hilbert-style proof system
└── Metalogic/                 -- Completeness, soundness
```

### Modal Logic (`Logics/Modal/`)

```
Modal/
├── Basic.lean                 -- Formula type, Kripke semantics
├── Denotation.lean            -- Denotational semantics
├── Cube.lean                  -- Modal logic cube (K, T, S4, S5)
├── FromPropositional.lean     -- Embedding from propositional
└── Metalogic/                 -- Soundness, completeness, MCS
    ├── Soundness.lean
    ├── Completeness.lean
    ├── MCS.lean
    ├── DeductionTheorem.lean
    └── DerivationTree.lean
```

### Temporal Logic (`Logics/Temporal/`)

```
Temporal/
├── FromPropositional.lean     -- Embedding from propositional
├── Syntax/
│   └── Formula.lean           -- Temporal formula type
├── Semantics/
│   ├── Model.lean             -- Temporal models
│   ├── Satisfies.lean         -- Satisfaction relation
│   └── Validity.lean          -- Validity
├── ProofSystem/
│   ├── Axioms.lean            -- Temporal axiom schemas
│   ├── Derivation.lean        -- Derivation trees
│   ├── Derivable.lean         -- Derivability
│   └── Instances.lean         -- Typeclass instances
├── Theorems/                  -- Derived temporal theorems
└── Metalogic/
    ├── Soundness.lean
    ├── Completeness.lean
    ├── MCS.lean
    ├── DeductionTheorem.lean
    ├── DerivationTree.lean
    ├── TemporalContent.lean
    ├── WitnessSeed.lean
    ├── GeneralizedNecessitation.lean
    ├── PropositionalHelpers.lean
    ├── CompletenessHelpers.lean
    └── Chronicle/             -- Chronicle construction
```

### Bimodal Logic (`Logics/Bimodal/`)

The bimodal logic combines modal and temporal operators under the Burgess-Xu (BX) axiom system. This is the largest and most complex logic in the library.

```
Bimodal/
├── Syntax/
│   ├── Formula.lean           -- Bimodal formula type
│   └── SubformulaClosure/     -- Subformula closure utilities
├── Semantics/                 -- Task-frame semantics
├── ProofSystem/
│   ├── Axioms.lean            -- BX axiom schemas
│   ├── Derivation.lean        -- Derivation trees
│   ├── Derivable.lean         -- Derivability
│   ├── Instances.lean         -- Typeclass instances
│   ├── Substitution.lean      -- Substitution lemmas
│   └── LinearityDerivedFacts.lean
├── Theorems/
│   ├── TemporalDerived.lean   -- Temporal theorems from BX axioms
│   ├── Combinators.lean       -- Proof combinators
│   └── Perpetuity/            -- Always/sometimes operator theorems
│       └── Bridge.lean
├── Embedding/                 -- Conservative extensions
│   ├── PropositionalEmbedding.lean
│   ├── ModalEmbedding.lean
│   └── TemporalEmbedding.lean
├── FrameConditions/           -- Frame validity
│   ├── Soundness.lean
│   ├── Validity.lean
│   ├── FrameClass.lean
│   └── Compatibility.lean    -- Axiom-frame compatibility typeclasses
└── Metalogic/                 -- Core metalogical results
    ├── Core/                  -- MCS, deduction theorem, derivation trees
    ├── Algebraic/             -- Lindenbaum-Tarski algebra approach
    │   ├── LindenbaumQuotient.lean
    │   ├── BooleanStructure.lean
    │   ├── InteriorOperators.lean
    │   ├── UltrafilterMCS.lean
    │   ├── ParametricCanonical.lean
    │   ├── ParametricHistory.lean
    │   ├── ParametricTruthLemma.lean
    │   ├── RestrictedParametricTruthLemma.lean
    │   └── ParametricCompleteness.lean
    ├── Bundle/                -- FMCS bundle construction
    ├── BXCanonical/           -- BX canonical model construction
    │   ├── Chronicle/         -- Chronicle construction
    │   ├── Completeness/      -- Dense/discrete completeness
    │   ├── Filtration/        -- Defect chain filtration
    │   └── Quasimodel/        -- Quasimodel/Hintikka construction
    ├── ConservativeExtension/ -- Conservative extension proofs
    ├── Decidability/          -- Decidability and finite model property
    │   └── FMP/
    ├── Separation/            -- Separation results
    │   ├── DedekindZ/
    │   └── Hierarchy/
    └── Soundness/             -- Soundness proofs
```

### Other Logics

- `Logics/HML/` -- Hennessy-Milner Logic (for process equivalence).
- `Logics/LinearLogic/CLL/` -- Classical Linear Logic (sequent calculus, cut elimination, phase semantics).

## Namespace Convention

The `Cslib.Logic` namespace spans both `Foundations/Logic/` and `Logics/`:
- `Cslib.Logic.Axioms` -- from `Foundations/Logic/Axioms.lean`
- `Cslib.Logic.Propositional` -- from `Logics/Propositional/`
- `Cslib.Logic.Modal` -- from `Logics/Modal/`
- `Cslib.Logic.Temporal` -- from `Logics/Temporal/`
- `Cslib.Logic.Bimodal` -- from `Logics/Bimodal/`

Infrastructure lives in `Foundations/`, specific logics live in `Logics/`, and both share the `Cslib.Logic` namespace prefix.

## Testing

- `CslibTests/` -- Contains tests for the library.
