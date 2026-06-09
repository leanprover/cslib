# Project Roadmap: Porting BimodalLogic to CSLib

This document describes the ongoing effort to extract and organize content from
the [BimodalLogic](https://github.com/benbrastmckie/BimodalLogic) repository
into four standalone CSLib modules: **Propositional**, **Modal**, **Temporal**,
and **Bimodal**. Phases 1–3 (Propositional, Modal, Temporal) are complete,
self-contained deliverables before any bimodal content is introduced.

## Approach

Every component lives at the most general level it can compile at. Content is
distributed across four module levels — Foundations/Logic/Theorems/,
Logics/Modal/, Logics/Temporal/, and Logics/Bimodal/ — with imports flowing
strictly downward: Foundations → Modal/Temporal (including their Metalogic) →
Bimodal. Modal and Temporal metalogic are fully standalone and do not import
from each other.

## Import Hierarchy

```
Foundations/Logic/Theorems/      (Task 20 — propositional lemmas)
Foundations/Logic/Metalogic/     (Task 29 — generic MCS foundations)
       ↓                ↓
Modal/ProofSystem/   Temporal/ProofSystem/   (Tasks 21, 22 — parallel)
Modal/Theorems/      Temporal/Theorems/
Modal/Metalogic/     Temporal/Semantics/     (Tasks 30, 23)
                     Temporal/Metalogic/     (Task 31 — depends on 22, 23, 29)
                            ↓
                    Bimodal/                 (Tasks 2–11)
```

This hierarchy enforces: Foundations → Modal/Temporal (incl. Metalogic) → Bimodal.
Modal and Temporal metalogic are fully standalone — they do not import from each
other, only from Foundations. Bimodal metalogic (Task 7) imports generic MCS
definitions from Foundations/Logic/Metalogic/ (Task 29).

## Completed

| Task | Component | Module |
|------|-----------|--------|
| 20 | Propositional Hilbert theorems (combinators, core, weakening, cut, big-conjunction) | `Foundations/Logic/Theorems/` |
| 21 | Modal proof system, S4/S5 theorems, GeneralizedNecessitation | `Foundations/Logic/Theorems/Modal/` |
| 29 | Generic MCS foundations (SetConsistent, SetMaximalConsistent, Lindenbaum) | `Foundations/Logic/Metalogic/` |
| 22 | Temporal proof system (26-axiom BX), derived theorems, frame conditions | `Logics/Temporal/ProofSystem/` + `Logics/Temporal/Theorems/` |
| 23 | Temporal semantics on LinearOrder | `Logics/Temporal/Semantics/` |
| 30 | Modal metalogic: DeductionTheorem, MCS, Soundness, Completeness | `Logics/Modal/Metalogic/` |
| 2 | Bimodal syntax: Context, BigConj, Subformulas | `Logics/Bimodal/Syntax/` |
| 3 | Task frame semantics: TaskFrame, WorldHistory, Truth, Validity | `Logics/Bimodal/Semantics/` |
| 4 | Bimodal proof system: 42-axiom Hilbert, DerivationTree, Substitution | `Logics/Bimodal/ProofSystem/` |
| 5 | Perpetuity theorems (bimodal fixed-point principles) | `Logics/Bimodal/Theorems/Perpetuity/` |
| 6 | Frame conditions + Soundness | `Logics/Bimodal/FrameConditions/` + `Logics/Bimodal/Metalogic/Soundness/` |
| 7 | Bimodal DeductionTheorem + MCS theory | `Logics/Bimodal/Metalogic/Core/` |
| 34 | Base MCS completeness properties | `Logics/Bimodal/Metalogic/` |
| 10 | Separation theorem (GHR94 10.2.9) | `Logics/Bimodal/Metalogic/Separation/` |
| 11 | BX conservative extension | `Logics/Bimodal/Metalogic/ConservativeExtension/` |
| 42 | Tableau decision procedure | `Logics/Bimodal/Metalogic/Decidability/` |
| 43 | Finite model property | `Logics/Bimodal/Metalogic/Decidability/FMP/` |

## Remaining

| Task | Component | Module |
|------|-----------|--------|
| 31 | Temporal metalogic: DeductionTheorem, MCS, Soundness, Completeness | `Logics/Temporal/Metalogic/` |
| 35 | Dense completeness (Algebraic, Bundle, BXCanonical) | `Logics/Bimodal/Metalogic/` |
| 36 | Discrete completeness | `Logics/Bimodal/Metalogic/` |
| 37 | Continuous extension completeness | `Logics/Bimodal/Metalogic/` |
| 38 | Dense temporal completeness | `Logics/Temporal/Metalogic/` |
| 39 | Discrete temporal completeness | `Logics/Temporal/Metalogic/` |
| 40 | Continuous temporal completeness | `Logics/Temporal/Metalogic/` |
| 41 | Abstract shared completeness infrastructure | `Logics/Bimodal/Metalogic/` + `Logics/Temporal/Metalogic/` |

## Phases

**Phase 1 — Propositional (Task 20, completed)**: Ported generic Hilbert-style
theorems (combinators, propositional core, weakening, cut, big-conjunction) into
`Foundations/Logic/Theorems/`. Any logic that instantiates `PropositionalHilbert`
inherits these results.

**Phase 2 — Modal and Temporal Modules (Tasks 21, 22, completed)**: Added a
standalone modal proof system with S4/S5 theorems (Task 21) and a standalone
temporal proof system with 26 BX axioms, derived theorems, and frame conditions
(Task 22). Both modules import only Foundations and are fully self-contained.

**Phase 3 — Temporal Semantics (Task 23, completed)**: Defined `Temporal.Model`
on `LinearOrder` with satisfaction for all five connectives and frame conditions
for dense, discrete, and linear orders — new infrastructure with no BimodalLogic
counterpart that enables standalone temporal soundness and completeness.

**Phase 4 — Standalone Metalogic (Tasks 29, 30 completed; Task 31 in progress)**:
Task 29 placed generic MCS foundations (parameterized over an abstract derivation
relation) in `Foundations/Logic/Metalogic/`. Task 30 completed the full modal
metalogic layer (deduction theorem, MCS theory, soundness over Kripke frames,
S5 completeness via canonical model). Task 31 (temporal metalogic) remains the
outstanding item in this phase.

**Phase 5 — Bimodal Porting (Tasks 2–11 mostly completed; Task 35 in progress)**:
The largest phase by volume, porting the full TM bimodal logic to `Logics/Bimodal/`.
Syntax, semantics, proof system, perpetuity theorems, soundness, deduction theorem,
MCS theory, base completeness, separation, conservative extension, decidability
(tableau + FMP) are all done. Dense completeness (Task 35) is currently
implementing; discrete and continuous completeness (Tasks 36, 37) follow.
