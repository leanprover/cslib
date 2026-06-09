# Project Roadmap: Porting BimodalLogic to CSLib

This document describes the ongoing effort to extract and organize content from
the [BimodalLogic](https://github.com/benbrastmckie/BimodalLogic) repository
into four standalone CSLib modules: **Propositional**, **Modal**, **Temporal**,
and **Bimodal**. The porting is guided by a modular factoring principle: every
component lives at the most general level it can compile at. Task descriptions
and current statuses are tracked in [specs/TODO.md](TODO.md).

---

## Overview

[BimodalLogic](https://github.com/benbrastmckie/BimodalLogic) is a standalone
Lean 4 repository (~84,547 lines, 246 files) implementing a verified bimodal
logic with soundness, completeness, decidability, and separation results. Porting
it to CSLib is a four-level effort: propositional theorems go into
`Foundations/Logic/Theorems/`, modal content into `Logics/Modal/`, temporal
content into `Logics/Temporal/`, and the inherently bimodal content into
`Logics/Bimodal/`.

The modular factoring analysis identifies ~6,800 lines of content that
are reusable above the bimodal level. These lines benefit any logic built on the
CSLib foundations — not just the bimodal port. Phases 1–3 (Propositional, Modal,
Temporal) are complete, self-contained deliverables before any bimodal content is
introduced.

---

## Modular Factoring Design

**Design Principle:** Every component lives at the most general level it can compile at.

### Component Placement

| Component | CSLib Location | Rationale |
|-----------|---------------|-----------|
| Combinators (I,B,C,S), Propositional/{Core,Connectives,Reasoning}, ContextualProofs, BigConj | `Foundations/Logic/Theorems/` | Pure `[PropositionalHilbert S]`; reusable by all four logics |
| Temporal axiom abbreviations, HasAxiom* typeclasses, TemporalBXHilbert restructuring | `Foundations/Logic/ProofSystem.lean` additions | Infrastructure layer shared by Temporal and Bimodal |
| **Generic MCS foundations** (SetConsistent, SetMaximalConsistent, Lindenbaum skeleton) | `Foundations/Logic/Metalogic/Consistency.lean` | **~60% of MCS theory is generic**; parameterized over abstract derivation relation |
| Modal.DerivationTree + ModalHilbert/ModalS5Hilbert instances | `Logics/Modal/ProofSystem/` | Modal standalone; concrete proof system |
| GeneralizedNecessitation + S4/S5 theorems | `Logics/Modal/Theorems/` | Pure `[ModalHilbert S]` / `[ModalS5Hilbert S]` |
| **Modal metalogic** (DeductionTheorem + MCS + Soundness + Completeness) | `Logics/Modal/Metalogic/` | Standalone; per-logic DT + modal-specific MCS + Kripke soundness/completeness |
| Temporal.DerivationTree + TemporalBXHilbert instance | `Logics/Temporal/ProofSystem/` | Temporal standalone; concrete proof system |
| TemporalDerived theorems + frame condition typeclasses | `Logics/Temporal/Theorems/` | Pure `[TemporalBXHilbert S]` |
| Temporal semantics on LinearOrder | `Logics/Temporal/Semantics/` | New infrastructure; enables standalone soundness |
| **Temporal metalogic** (DeductionTheorem + MCS + Soundness + Completeness) | `Logics/Temporal/Metalogic/` | Standalone; per-logic DT + temporal-specific MCS + linear order soundness/completeness |
| **Bimodal DeductionTheorem** | `Logics/Bimodal/Metalogic/Core/` (per-logic) | Requires structural induction on concrete bimodal DerivationTree; imports generic MCS from Foundations |
| Perpetuity theorems + all bimodal content | `Logics/Bimodal/` | Uses both box and until/since; inherently bimodal |

### Key Design Decisions

1. **DeductionTheorem stays per-logic** (Tasks 7, 30, 31; not Task 20): The deduction
   theorem requires structural induction on the concrete `DerivationTree`
   inductive. It cannot be ported generically to Foundations because
   `DerivationTree` is concrete, not typeclass-polymorphic. Each logic (modal ~5
   constructors, temporal ~6, bimodal 7) needs its own deduction theorem.

2. **MCS theory ~60% generic** (Task 29): Definitions — `SetConsistent`,
   `SetMaximalConsistent`, Lindenbaum skeleton, `consistent_chain_union` — live
   in `Foundations/Logic/Metalogic/`. The `negation_complete` predicate and
   witness conditions depend on the per-logic deduction theorem and stay in
   Modal/Metalogic/ (Task 30), Temporal/Metalogic/ (Task 31), and
   Bimodal/Metalogic/Core/ (Task 7).

3. **BimodalTMHilbert diamond-avoidance** (Task 22): The `BimodalTMHilbert`
   typeclass extends individual temporal `HasAxiom*` classes directly (mirroring
   the `BimodalConnectives` pattern), providing a manual `TemporalBXHilbert`
   instance. This avoids the typeclass diamond that would arise from extending
   both `ModalHilbert` and `TemporalBXHilbert`.

4. **Temporal semantics is new infrastructure** (Task 23): The standalone
   temporal semantics on `LinearOrder` does not exist in BimodalLogic (which
   only has task frame semantics). It is new development enabling temporal
   soundness/completeness proofs without bimodal machinery.

5. **No generic metalogic typeclass** (`HasDeductionTheorem` would be premature):
   Team research explicitly discourages abstracting metalogic with typeclasses
   at this stage. Each logic's metalogic is standalone and imports only
   Foundations definitions, not a shared proof strategy.

---

## What CSLib Gains

Each of the four levels is a standalone, importable library — not scaffolding
for the next level.

- **Propositional (Task 20)**: ~2,400 lines of generic Hilbert-style theorems
  (combinators, propositional core, weakening, cut, big-conjunction) usable by
  any propositional or higher logic in CSLib. Any logic that instantiates
  `PropositionalHilbert` gets these for free.

- **Modal (Task 21)**: ~1,600 lines adding a standalone modal proof system with
  S4 and S5 theorem libraries and generalized necessitation. Modal/ imports only
  Foundations — it is fully self-contained and usable independently of temporal
  or bimodal machinery.

- **Temporal (Tasks 22–23)**: ~1,900–2,100 lines adding a standalone temporal
  proof system, a derived theorem library, and new semantics on `LinearOrder`
  enabling soundness and completeness proofs for linear temporal logic without
  any bimodal dependency. Task 23 (semantics) is new development with no
  BimodalLogic counterpart.

- **Generic Metalogic (Task 29)**: ~200–300 lines of generic MCS foundations
  parameterized over an abstract derivation relation. Any logic in CSLib can
  import these generic definitions and add per-logic witness conditions.

- **Modal Metalogic (Task 30)**: ~1,500 lines of standalone modal metalogic —
  deduction theorem, MCS theory (using Task 29 generic definitions + modal
  witness conditions), soundness over Kripke frames, and completeness via
  canonical Kripke model construction for S5. All new development; no
  BimodalLogic counterpart.

- **Temporal Metalogic (Task 31)**: ~1,500 lines of standalone temporal metalogic —
  deduction theorem, MCS theory (using Task 29 generic definitions + temporal
  witness conditions), soundness over linear orders, and completeness via
  canonical linear model construction. All new development; no BimodalLogic
  counterpart.

- **Bimodal (Tasks 2–11)**: ~30,000+ lines comprising the full bimodal Hilbert
  system, task frame semantics, metalogic (MCS theory importing Task 29 generic
  foundations, completeness, decidability, separation, conservative extension),
  and perpetuity theorems. Phase 4 is the largest by volume but depends on the
  three preceding phases being complete.

---

## Background: TM Bimodal Logic

The **Bimodal Logic of Tense and Modality (TM)** is a formal system combining
S5 modal operators (necessity `□`) with Since/Until linear tense operators. It is
designed for verified reasoning about past and future contingency in
non-deterministic dynamical systems. Truth is evaluated at world-history pairs
inside a task model built from a task frame encoding possible transitions over
durations.

BimodalLogic implements soundness and completeness for four axiom systems (Base,
Dense, Continuous, Discrete) plus decidability and separation results. For the
full formal specification — connectives, semantics, axiom tables, and
metalogical results — see
[github.com/benbrastmckie/BimodalLogic](https://github.com/benbrastmckie/BimodalLogic).

---

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

---

## Current State of CSLib

### What Exists Today

```
Cslib/
├── Foundations/Logic/
│   ├── Connectives.lean      # HasBot/HasImp/HasBox/HasUntil/HasSince typeclasses
│   ├── ProofSystem.lean      # ModusPonens, Necessitation, HasAxiom* typeclasses;
│   │                         # PropositionalHilbert, ModalHilbert, ModalS5Hilbert,
│   │                         # TemporalBXHilbert; tag types
│   ├── Axioms.lean           # Axiom abbreviations (K, T, B, S4, S5, BX temporal)
│   ├── InferenceSystem.lean  # InferenceSystem typeclass, DerivableIn
│   ├── LogicalEquivalence.lean
│   └── Theorems/             # ★ Task 20, 21 (COMPLETED)
│       ├── Combinators.lean  # I, B, C, S combinators (~332 lines)
│       ├── BigConj.lean      # Big conjunction (~138 lines)
│       ├── Propositional/    # Core, Connectives, Reasoning (~877 lines)
│       └── Modal/            # Basic + S5 theorems (~786 lines)
├── Logics/
│   ├── Propositional/
│   │   ├── Defs.lean         # PL.Proposition, derived connectives, Theory
│   │   ├── Embedding.lean    # PL -> Modal embedding (Proposition.toModal)
│   │   └── NaturalDeduction/Basic.lean
│   ├── Modal/
│   │   ├── Basic.lean        # Modal.Proposition, Kripke semantics
│   │   ├── Cube.lean         # Modal logic cube
│   │   └── Denotation.lean
│   ├── Temporal/
│   │   ├── Syntax/           # Formula, BigConj, Subformulas, Context
│   │   ├── ProofSystem/      # ★ Task 22 (COMPLETED)
│   │   │   ├── Axioms.lean   # 26-axiom BX system (~216 lines)
│   │   │   ├── Derivation.lean # DerivationTree (~94 lines)
│   │   │   ├── Derivable.lean  # Derivable + HilbertBX tag (~95 lines)
│   │   │   └── Instances.lean  # InferenceSystem instances (~209 lines)
│   │   └── Theorems/         # ★ Task 22 (COMPLETED)
│   │       ├── TemporalDerived.lean  # 20 derived theorems (~271 lines)
│   │       └── FrameConditions.lean  # Frame typeclasses (~84 lines)
│   └── Bimodal/
│       ├── Syntax/           # ★ Task 2 (COMPLETED)
│       │   ├── Formula.lean  # Bimodal.Formula, BimodalConnectives
│       │   └── Context.lean  # Context type (~140 lines)
│       ├── Semantics/        # ★ Task 3 (COMPLETED)
│       │   ├── TaskFrame.lean    # TaskFrame structure (~191 lines)
│       │   ├── WorldHistory.lean # WorldHistory type (~309 lines)
│       │   ├── TaskModel.lean    # TaskModel structure (~83 lines)
│       │   ├── Truth.lean        # Truth evaluation (~651 lines)
│       │   └── Validity.lean     # Validity definitions (~275 lines)
│       └── Embedding/
│           ├── ModalEmbedding.lean    # Modal.Proposition.toBimodal
│           ├── TemporalEmbedding.lean # Temporal.Formula.toBimodal
│           └── PropositionalEmbedding.lean # PL.Proposition.toBimodal
```

Total CSLib Lean lines (all modules): ~31,723

### What Has Been Completed

| Component | Task | Lines | Status |
|-----------|------|-------|--------|
| `Foundations/Logic/Theorems/` — propositional Hilbert theorems | 20 | ~2,400 | COMPLETED |
| `Foundations/Logic/Theorems/Modal/` — S4/S5 theorems, GenNec | 21 | ~786 | COMPLETED |
| `Foundations/Logic/Metalogic/` — generic MCS foundations | 29 | ~273 | COMPLETED |
| `Temporal/ProofSystem/` + `Temporal/Theorems/` — temporal proof system and theorems | 22 | ~1,433 | COMPLETED |
| `Temporal/Semantics/` — standalone temporal semantics on LinearOrder | 23 | ~440 | COMPLETED |
| `Modal/Metalogic/` — DerivationTree, DeductionTheorem, MCS, Soundness, Completeness | 30 | ~1,449 | COMPLETED |
| `Bimodal/Syntax/` — Context, BigConj, Subformulas | 2 | ~827 | COMPLETED |
| `Bimodal/Semantics/` — TaskFrame, WorldHistory, Truth, Validity | 3 | ~1,649 | COMPLETED |
| `Bimodal/ProofSystem/` — 42-axiom Hilbert, DerivationTree, Substitution | 4 | ~2,000 | COMPLETED |
| `Bimodal/Theorems/Perpetuity/` — bimodal fixed-point principles | 5 | ~549 | COMPLETED |
| `Bimodal/FrameConditions/` + `Bimodal/Metalogic/Soundness/` | 6 | ~2,370 | COMPLETED |
| `Bimodal/Metalogic/Core/` — Deduction theorem, MCS theory | 7 | ~1,112 | COMPLETED |
| `Bimodal/Metalogic/Completeness.lean` — base MCS completeness properties | 34 | ~478 | COMPLETED |
| `Bimodal/Metalogic/Separation/` — Separation theorem (GHR94 10.2.9) | 10 | ~6,420 | COMPLETED |
| `Bimodal/Metalogic/ConservativeExtension/` — BX conservative extension | 11 | ~1,671 | COMPLETED |
| `Bimodal/Metalogic/Decidability/` — Tableau decision procedure | 42 | ~5,957 | COMPLETED |
| `Bimodal/Metalogic/Decidability/FMP/` — Finite model property | 43 | ~2,500 | COMPLETED |

### What Remains

| Missing Component | Task | Lines |
|-------------------|------|-------|
| `Temporal/Metalogic/` — temporal deduction theorem, MCS, soundness, completeness | 31 | ~1,500 (new) |
| `Bimodal/Metalogic/{Algebraic,Bundle,BXCanonical}/` — dense completeness | 35 | ~15,000 |
| `Bimodal/Metalogic/` — discrete completeness | 36 | ~TBD |
| `Bimodal/Metalogic/` — continuous extension completeness | 37 | ~TBD |

**~50,000+ lines of proof code completed.** Critical path: Task 35 (dense completeness) → 36/37 → 31 (temporal metalogic) → 38/39 (temporal completeness).

---

## Porting Phases

Phases 1–3 complete first and unlock Phase 4. Each phase produces a self-contained,
independently useful CSLib module.

### Phase 1: Propositional — Hilbert Theorems (Task 20)

**Target**: `Cslib/Foundations/Logic/Theorems/`
**Scope**: ~2,400 lines ported from BimodalLogic

| Component | Lines | Source |
|-----------|-------|--------|
| Combinators (I, B, C, S) | ~300 | BimodalLogic/Theorems/Combinators.lean |
| Propositional/{Core,Connectives,Reasoning} | ~1,100 | BimodalLogic/Theorems/Propositional/ |
| ContextualProofs (weakening, cut) | ~500 | BimodalLogic/Theorems/ContextualProofs.lean |
| BigConj (generic) | ~500 | BimodalLogic/Syntax/BigConj.lean |

**Milestone**: All four logics can import propositional theorems without bimodal dependency.

---

### Phase 2: Modal and Temporal Modules (Tasks 21, 22 — parallel after Task 20)

#### Task 21: Modal Proof System and Theorems
**Target**: `Cslib/Logics/Modal/ProofSystem/` + `Cslib/Logics/Modal/Theorems/`
**Scope**: ~1,600 lines ported from BimodalLogic

| Component | Lines |
|-----------|-------|
| Modal.DerivationTree + ModalHilbert/ModalS5Hilbert instances | ~400 |
| S4/S5 derived theorems | ~800 |
| GeneralizedNecessitation | ~400 |

**Milestone**: A standalone modal proof system and S4/S5 theorem library, importable independently of temporal or bimodal content.

#### Task 22: Temporal Infrastructure and Theorems
**Target**: Axioms.lean/ProofSystem.lean additions + `Cslib/Logics/Temporal/ProofSystem/` + `Temporal/Theorems/`
**Scope**: ~1,500 lines (new infrastructure + ports)

| Component | Lines |
|-----------|-------|
| ~20 temporal axiom abbreviations | ~100 |
| ~20 HasAxiom* typeclasses | ~200 |
| TemporalBXHilbert restructuring + BimodalTMHilbert instance | ~150 |
| Temporal.DerivationTree + TemporalBXHilbert instance | ~200 |
| TemporalDerived theorems | ~790 |
| Frame condition typeclasses | ~130 |

**Milestone**: Modal/ and Temporal/ are self-contained modules with proof systems and theorems.

---

### Phase 3: Temporal Semantics (Task 23 — after Task 22)

**Target**: `Cslib/Logics/Temporal/Semantics/`
**Scope**: ~400–600 lines (new infrastructure, not ported from BimodalLogic)

Defines `Temporal.Model` on `LinearOrder`, `Temporal.Satisfies` for all five
connectives, and frame conditions for dense/discrete/linear orders. This
enables standalone temporal soundness and completeness proofs entirely
independent of bimodal machinery.

**Milestone**: Temporal/ is a fully standalone module with syntax, proof system, theorems, and semantics.

---

### Phase 4: Standalone Metalogic (Tasks 29, 30, 31)

**Targets**:
- `Cslib/Foundations/Logic/Metalogic/` (Task 29)
- `Cslib/Logics/Modal/Metalogic/` (Task 30)
- `Cslib/Logics/Temporal/Metalogic/` (Task 31)

**Scope**: ~3,200–3,300 lines total (new development, no BimodalLogic counterpart)

This phase adds the full metalogic layer to each standalone module. Task 29
provides generic MCS foundations that Tasks 30 and 31 import. Each logic gets
its own complete proof-theoretic development (deduction theorem + MCS theory +
soundness + completeness).

#### Task 29: Generic MCS Foundations
**Scope**: ~200–300 lines (new; Wave 1, no dependencies)

| Component | Lines |
|-----------|-------|
| `SetConsistent` definition | ~50 |
| `SetMaximalConsistent` definition | ~50 |
| Lindenbaum lemma skeleton (Zorn-based) | ~100 |
| `consistent_chain_union`, `closed_under_derivation`, `implication_property` | ~100 |

**Design**: Parameterized over an abstract derivation relation (`⊢`). Does not
depend on any per-logic `DerivationTree`. Bimodal task 7 also imports from here.

#### Task 30: Modal Metalogic
**Scope**: ~1,500 lines (new; after Tasks 21 + 29)

| Component | Lines |
|-----------|-------|
| `Modal.DeductionTheorem` (structural induction on ~5-constructor DerivationTree) | ~300 |
| `Modal.MCS` (generic definitions + box_closure witness condition) | ~400 |
| `Modal.Soundness` (over Kripke frames/models from Modal/Basic.lean) | ~350 |
| `Modal.Completeness` (canonical Kripke model construction for S5) | ~450 |

#### Task 31: Temporal Metalogic
**Scope**: ~1,500 lines (new; after Tasks 22 + 23 + 29)

| Component | Lines |
|-----------|-------|
| `Temporal.DeductionTheorem` (structural induction on ~6-constructor DerivationTree) | ~300 |
| `Temporal.MCS` (generic definitions + Until/Since witness conditions) | ~400 |
| `Temporal.Soundness` (over linear orders from Task 23 semantics) | ~350 |
| `Temporal.Completeness` (canonical linear model construction) | ~450 |

**Milestone**: Modal/ and Temporal/ are complete standalone modules with full verified
proof theories — syntax, proof system, theorems, semantics, and metalogic. All
four phases produce independently useful, standalone libraries.

---

### Phase 5: Bimodal Porting (Tasks 2–11)

**Target**: `Cslib/Logics/Bimodal/`
**Scope**: ~30,000+ lines (inherently bimodal content)

Phase 5 is the largest by volume and depends on Phases 1–4 being complete. It
ports the full TM bimodal logic into CSLib, including the task frame semantics,
the 42-axiom Hilbert system, and all metalogical results. Bimodal MCS theory
(Task 7) imports the generic MCS foundations from Task 29 (Phase 4).

| Task | Component | Lines | Depends On |
|------|-----------|-------|------------|
| 2 | Bimodal Syntax (Context, BigConj, Subformulas) | ~2,500 | BimodalLogic:291 toolchain |
| 3 | Task Frame Semantics (TaskFrame, WorldHistory, Truth) | ~2,200 | 2 |
| 4 | Bimodal Proof System (42-axiom Hilbert, DerivationTree) | ~2,000 | 2, 20, 22 |
| 5 | Perpetuity Theorems (bimodal fixed-point principles) | ~800 | 4, 21, 22 |
| 6 | Frame Conditions + Soundness | ~2,370 | 3, 4 |
| 7 | Deduction Theorem + MCS Theory | ~2,500 | 4, 5, **29** |
| 8 | Strong Completeness | ~15,000 | 6, 7 |
| 9 | Decidability + Tableau | ~10,000 | 4, 7 |
| 10 | Separation Theorem | ~3,500 | 4, 5, 7 |
| 11 | Conservative Extension | ~1,500 | 4 |

**External dependency**: Task 2 requires BimodalLogic:291 (toolchain upgrade in the source repository) before porting can begin.

**Milestone**: All ~30,000+ lines of bimodal content ported. PR pipeline complete after Task 12 coordination.

---

## Task Dependency Structure

The dependency graph enforces the import hierarchy. Tasks within the same wave can execute in parallel.

| Wave | Tasks | Blocked by | Description |
|------|-------|------------|-------------|
| 1 | 3, 12, 21, 22, 28, 29 | — | Foundations (incl. generic MCS) + frame semantics + standalone modules |
| 2 | 4, 23, 30 | 21, 22, 29 | Bimodal proof system; temporal semantics; modal metalogic |
| 3 | 5, 6, 11, 31 | 3, 4, 21, 22, 23, 29 | Perpetuity; frame conds + soundness; cons. ext.; temporal metalogic |
| 4 | 7 | 4, 5, 29 | Bimodal deduction theorem + MCS theory (imports generic from 29) |
| 5 | 8, 9, 10 | 4, 5, 6, 7 | Completeness; decidability; separation |

**Foundations-first invariant**: Task 29 (generic MCS) is Wave 1. Tasks 30 and 31 depend on Task 29. Bimodal Task 7 also depends on Task 29. This enforces: Foundations/Logic/Metalogic → Modal/Metalogic, Temporal/Metalogic, Bimodal/Metalogic.

**Metalogic invariant**: Modal/Metalogic (Task 30) and Temporal/Metalogic (Task 31) do not import from each other — only from Foundations. The import direction is strictly top-down.

**External dependency**: Task 2 (Wave 1) additionally requires a toolchain upgrade in the BimodalLogic source repository (issue #291) before porting can begin.

**PR coordination**: Task 12 runs in parallel throughout all waves and handles maintainer communication, namespace decisions, and CI compliance for PRs submitted to the CSLib main repository.

See [specs/TODO.md](TODO.md) for full task descriptions and current status.

---

## Component Accounting

Every extractable component maps to exactly one task (no double-counting):

| Component | Task | Lines |
|-----------|------|-------|
| Combinators + Propositional/ + ContextualProofs + BigConj | 20 | ~2,400 |
| Modal DerivationTree + S4/S5 theorems + GenNec | 21 | ~1,600 |
| Temporal infra + HasAxiom* + TemporalDerived + FrameConditions | 22 | ~1,500 |
| Temporal semantics on LinearOrder (new) | 23 | ~400–600 |
| Generic MCS foundations (SetConsistent, SetMaximalConsistent, Lindenbaum) | 29 | ~200–300 (new) |
| Modal metalogic (DT + MCS + Soundness + Completeness) | 30 | ~1,500 (new) |
| Temporal metalogic (DT + MCS + Soundness + Completeness) | 31 | ~1,500 (new) |
| Perpetuity theorems | 5 | ~800 |
| Bimodal DeductionTheorem (per-logic; imports generic MCS from Task 29) | 7 | ~500 |
| All remaining bimodal content | 2–11 | ~30,000+ |

**Total extractable to reusable modules**: ~6,800 lines (Tasks 20–22) plus ~400–600 new lines (Task 23) plus ~3,200–3,300 new metalogic lines (Tasks 29–31).
**Inherently bimodal**: ~30,000+ lines (Tasks 2–11).
**BimodalLogic total**: ~84,547 lines (including ~51,332 in WeakCanonical/ discrete pipeline).

---

## Success Metrics

**Phase 1 (Propositional)**
- [x] Propositional theorems ported: all ~2,400 lines in `Foundations/Logic/Theorems/` (Task 20) *(Completed: Task 20, 2026-06-08)*

**Phase 2 (Modal + Temporal Modules)**
- [x] Modal module complete: proof system + S4/S5 theorems in `Foundations/Logic/Theorems/Modal/` (Task 21) *(Completed: Task 21, 2026-06-08)*
- [x] Temporal module complete: proof system + theorems in `Logics/Temporal/` (Task 22) *(Completed: Task 22, 2026-06-08)*

**Phase 3 (Temporal Semantics)**
- [x] Temporal semantics defined standalone on LinearOrder (Task 23: ~400–600 new lines) *(Completed: Task 23, 2026-06-08)*

**Phase 4 (Standalone Metalogic)**
- [x] Generic MCS foundations in `Foundations/Logic/Metalogic/Consistency.lean` (Task 29: ~200–300 new lines) *(Completed: Task 29, 2026-06-08)*
- [x] Modal deduction theorem proved for ~5-constructor `Modal.DerivationTree` (Task 30) *(Completed: Task 30, 2026-06-08)*
- [x] Modal MCS theory with box_closure witness condition in `Logics/Modal/Metalogic/` (Task 30) *(Completed: Task 30, 2026-06-08)*
- [x] Modal soundness theorem: `ModalS5Hilbert S → S ⊢ φ → Modal.Valid φ` (Task 30) *(Completed: Task 30, 2026-06-08)*
- [x] Modal completeness theorem via canonical Kripke model for S5 (Task 30) *(Completed: Task 30, 2026-06-08)*
- [ ] Temporal deduction theorem proved for ~6-constructor `Temporal.DerivationTree` (Task 31)
- [ ] Temporal MCS theory with Until/Since witness conditions in `Logics/Temporal/Metalogic/` (Task 31)
- [ ] Temporal soundness theorem: `TemporalBXHilbert S → S ⊢ φ → Temporal.Valid φ` (Task 31)
- [ ] Temporal completeness theorem via canonical linear model construction (Task 31)
- [x] All standalone modules self-contained: Modal/ and Temporal/ import only Foundations *(Completed: Tasks 21-23, 30, 2026-06-09)*
- [ ] Zero sorry in Phases 1–4 (Tasks 20–23, 29–31)

**Phase 5 (Bimodal Porting)**
- [ ] All bimodal tasks (2–11) ported to `Cslib/Logics/Bimodal/`
- [x] Bimodal MCS theory imports generic foundations from Task 29 *(Completed: Task 7, 2026-06-09)*

**Cross-cutting**
- [ ] `lake build` passes with zero errors after each task
- [ ] PR pipeline complete: all PRs merged to CSLib main (Task 12)
- [ ] No component double-counted: each theorem belongs to exactly one task
