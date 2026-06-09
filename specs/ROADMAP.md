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
| Modal.DerivationTree + ModalHilbert/ModalS5Hilbert instances | `Logics/Modal/ProofSystem/` | Modal standalone; concrete proof system |
| GeneralizedNecessitation + S4/S5 theorems | `Logics/Modal/Theorems/` | Pure `[ModalHilbert S]` / `[ModalS5Hilbert S]` |
| Temporal.DerivationTree + TemporalBXHilbert instance | `Logics/Temporal/ProofSystem/` | Temporal standalone; concrete proof system |
| TemporalDerived theorems + frame condition typeclasses | `Logics/Temporal/Theorems/` | Pure `[TemporalBXHilbert S]` |
| Temporal semantics on LinearOrder | `Logics/Temporal/Semantics/` | New infrastructure; enables standalone soundness |
| DeductionTheorem | `Logics/Bimodal/Metalogic/Core/` (per-logic) | Requires structural induction on concrete DerivationTree |
| Perpetuity theorems + all bimodal content | `Logics/Bimodal/` | Uses both box and until/since; inherently bimodal |

### Key Design Decisions

1. **DeductionTheorem stays per-logic** (Task 7, not Task 20): The deduction
   theorem requires structural induction on the concrete `DerivationTree`
   inductive. It cannot be ported generically to Foundations because
   `DerivationTree` is concrete, not typeclass-polymorphic.

2. **BimodalTMHilbert diamond-avoidance** (Task 22): The `BimodalTMHilbert`
   typeclass extends individual temporal `HasAxiom*` classes directly (mirroring
   the `BimodalConnectives` pattern), providing a manual `TemporalBXHilbert`
   instance. This avoids the typeclass diamond that would arise from extending
   both `ModalHilbert` and `TemporalBXHilbert`.

3. **Temporal semantics is new infrastructure** (Task 23): The standalone
   temporal semantics on `LinearOrder` does not exist in BimodalLogic (which
   only has task frame semantics). It is new development enabling temporal
   soundness/completeness proofs without bimodal machinery.

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

- **Bimodal (Tasks 2–11)**: ~30,000+ lines comprising the full bimodal Hilbert
  system, task frame semantics, metalogic (MCS theory, completeness, decidability,
  separation, conservative extension), and perpetuity theorems. Phase 4 is the
  largest by volume but depends on the three preceding phases being complete.

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
Foundations/Logic/Theorems/   (Task 20 — propositional lemmas)
       ↓                ↓
Modal/ProofSystem/   Temporal/ProofSystem/   (Tasks 21, 22 — parallel)
Modal/Theorems/      Temporal/Theorems/
                     Temporal/Semantics/     (Task 23 — depends on 22)
                            ↓
                    Bimodal/                 (Tasks 2–11)
```

This hierarchy enforces: Foundations → Modal/Temporal → Bimodal.

---

## Current State of CSLib

### What Exists Today

```
Cslib/
├── Foundations/Logic/
│   ├── Connectives.lean      # HasBot/HasImp/HasBox/HasUntil/HasSince typeclasses;
│   │                         # PropositionalConnectives, ModalConnectives,
│   │                         # TemporalConnectives, BimodalConnectives; LukasiewiczDerived
│   ├── ProofSystem.lean      # ModusPonens, Necessitation, HasAxiom* typeclasses;
│   │                         # PropositionalHilbert, ModalHilbert, ModalS5Hilbert,
│   │                         # TemporalBXHilbert; tag types
│   ├── Axioms.lean           # Axiom abbreviations (K, T, B, S4, S5, ...)
│   ├── InferenceSystem.lean  # InferenceSystem typeclass, DerivableIn
│   └── LogicalEquivalence.lean
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
│   │   └── Syntax/Formula.lean   # Temporal.Formula, TemporalConnectives instance
│   └── Bimodal/
│       ├── Syntax/Formula.lean   # Bimodal.Formula, BimodalConnectives instance
│       └── Embedding/
│           ├── ModalEmbedding.lean    # Modal.Proposition.toBimodal
│           └── TemporalEmbedding.lean # Temporal.Formula.toBimodal
```

Total CSLib Lean lines (all modules): ~25,588

### What Does Not Yet Exist

| Missing Component | Task | Lines |
|-------------------|------|-------|
| `Foundations/Logic/Theorems/` — propositional Hilbert theorems | 20 | ~2,400 |
| `Modal/ProofSystem/` + `Modal/Theorems/` — proof system and S4/S5 theorems | 21 | ~1,600 |
| `Temporal/ProofSystem/` + `Temporal/Theorems/` — temporal proof system and theorems | 22 | ~1,500 |
| `Temporal/Semantics/` — standalone temporal semantics on LinearOrder | 23 | ~400–600 (new) |
| `Bimodal/` (beyond Formula + Embedding) — full bimodal library | 2–11 | ~30,000+ |

**0 lines of proof code ported so far.** All porting tasks are [NOT STARTED].

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

**Milestone**: Temporal/ is a fully standalone module with syntax, proof system, theorems, and semantics — the first CSLib logic with a complete verified proof theory.

---

### Phase 4: Bimodal Porting (Tasks 2–11)

**Target**: `Cslib/Logics/Bimodal/`
**Scope**: ~30,000+ lines (inherently bimodal content)

Phase 4 is the largest by volume and depends on Phases 1–3 being complete. It
ports the full TM bimodal logic into CSLib, including the task frame semantics,
the 42-axiom Hilbert system, and all metalogical results.

| Task | Component | Lines | Depends On |
|------|-----------|-------|------------|
| 2 | Bimodal Syntax (Context, BigConj, Subformulas) | ~2,500 | BimodalLogic:291 toolchain |
| 3 | Task Frame Semantics (TaskFrame, WorldHistory, Truth) | ~2,200 | 2 |
| 4 | Bimodal Proof System (42-axiom Hilbert, DerivationTree) | ~2,000 | 2, 20, 22 |
| 5 | Perpetuity Theorems (bimodal fixed-point principles) | ~800 | 4, 21, 22 |
| 6 | Frame Conditions + Soundness | ~2,370 | 3, 4 |
| 7 | Deduction Theorem + MCS Theory | ~2,500 | 4, 5 |
| 8 | Strong Completeness | ~15,000 | 6, 7 |
| 9 | Decidability + Tableau | ~10,000 | 4, 7 |
| 10 | Separation Theorem | ~3,500 | 4, 5, 7 |
| 11 | Conservative Extension | ~1,500 | 4 |

**External dependency**: Task 2 requires BimodalLogic:291 (toolchain upgrade in the source repository) before porting can begin.

**Milestone**: All ~30,000+ lines of bimodal content ported. PR pipeline complete after Task 12 coordination.

---

## Task Dependency Structure

The 6-wave dependency graph enforces the import hierarchy. Tasks within the same wave can execute in parallel.

| Wave | Tasks | Blocked by | Description |
|------|-------|------------|-------------|
| 1 | 2, 12, 15, 16, 17, 18, 20, 24, 25 | — | Foundations + independent fixes; start immediately |
| 2 | 3, 21, 22 | 2, 16, 20 | Frame semantics; modal and temporal modules |
| 3 | 4, 23 | 2, 20, 22 | Bimodal proof system; temporal semantics |
| 4 | 5, 6, 11 | 3, 4, 21, 22 | Perpetuity; frame conditions + soundness; conservative ext. |
| 5 | 7 | 4, 5 | Deduction theorem + MCS theory |
| 6 | 8, 9, 10 | 4, 5, 6, 7 | Completeness; decidability; separation |

**Foundations-first invariant**: Task 20 (Foundations) is Wave 1. Tasks 21 and 22 depend on Task 20. All bimodal proof tasks (Wave 3+) depend on Foundations and the standalone modules. This enforces: Foundations → Modal/Temporal → Bimodal.

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
| Perpetuity theorems | 5 | ~800 |
| DeductionTheorem (stays per-logic) | 7 | ~500 |
| All remaining bimodal content | 2–11 | ~30,000+ |

**Total extractable to reusable modules**: ~6,800 lines (Tasks 20–22) plus ~400–600 new lines (Task 23).
**Inherently bimodal**: ~30,000+ lines (Tasks 2–11).
**BimodalLogic total**: ~84,547 lines (including ~51,332 in WeakCanonical/ discrete pipeline).

---

## Success Metrics

- [ ] Propositional theorems ported: all ~2,400 lines in `Foundations/Logic/Theorems/` (Task 20)
- [ ] Modal module complete: proof system + S4/S5 theorems in `Logics/Modal/` (Task 21)
- [ ] Temporal module complete: proof system + theorems in `Logics/Temporal/` (Task 22)
- [ ] Temporal semantics defined standalone on LinearOrder (Task 23: ~400–600 new lines)
- [ ] Temporal soundness theorem proved: `TemporalBXHilbert S → S ⊢ φ → Temporal.Valid φ`
- [ ] All standalone modules self-contained: Modal/ and Temporal/ import only Foundations
- [ ] Zero sorry in Phases 1–3 (Tasks 20–23)
- [ ] All bimodal tasks (2–11) ported to `Cslib/Logics/Bimodal/`
- [ ] `lake build` passes with zero errors after each task
- [ ] PR pipeline complete: all PRs merged to CSLib main (Task 12)
- [ ] No component double-counted: each theorem belongs to exactly one task
