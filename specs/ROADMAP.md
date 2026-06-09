# Project Roadmap: Porting BimodalLogic to CSLib

This document describes the ongoing effort to port the
[BimodalLogic](https://github.com/benbrastmckie/ProofChecker) repository into
CSLib, organized as modular standalone libraries for propositional, modal,
temporal, and bimodal logics. The porting is guided by a modular factoring
principle: every component lives at the most general level it can compile at.
Task descriptions and current statuses are tracked in [specs/TODO.md](TODO.md).

---

## What is TM Bimodal Logic?

The **Bimodal Logic of Tense and Modality (TM)** is a formal system combining
S5 modal operators with Since/Until linear tense operators. It is designed for
verified reasoning about future contingency in non-deterministic dynamical
systems.

**Paper**: ["The Construction of Possible Worlds"](https://benbrastmckie.com/wp-content/uploads/2026/05/possible_worlds.pdf)
(Brast-McKie, 2025) — compositional semantics grounded in non-deterministic
dynamical systems (under review).

### Primitive Connectives (5 total)

| Symbol | Lean | Reading |
|--------|------|---------|
| `⊥` | `bot` | falsum |
| `φ → ψ` | `imp φ ψ` | material conditional |
| `□φ` | `box φ` | necessity |
| `U(φ,ψ)` | `untl φ ψ` | "ψ until φ" |
| `S(φ,ψ)` | `snce φ ψ` | "ψ since φ" |

All other operators (negation, conjunction, disjunction, possibility, F/G/H/P,
always/sometimes, next/previous) are derived.

### Task Semantics

Truth is evaluated at a world-history `τ` and a time `x` inside a **task
model** `M = (F, I)` built from a task frame `F = (W, D, R)` where `R : W →
D → W → Prop` is the task relation encoding possible transitions between
world-states over durations. This enables reasoning about future contingency
even with incomplete information about which world-history is realized.

### Axiom Systems

| System | Axioms | Standard Model | Soundness | Completeness |
|--------|--------|----------------|-----------|--------------|
| Base | 37 | — | Sorry-free | Sorry-free |
| Dense | 38 | ℚ | Sorry-free | Sorry-free |
| Continuous | 39 | ℝ | — | — |
| Discrete | 40 | ℤ | Sorry-free | Pending (Doets 1989) |

**Metalogical results** (BimodalLogic): soundness, completeness (base, dense),
decidability, separation, conservative extension.

---

## Why Port to CSLib?

BimodalLogic is a standalone Lean 4 repository (~84,547 lines, 246 files).
Porting it to CSLib makes its theorems available as a reusable, importable
library. The modular factoring design amplifies this value: propositional
theorems become usable by _any_ Hilbert system, modal theorems become usable
standalone, and temporal theorems become usable standalone — before the bimodal
machinery is even introduced.

Concretely, this port contributes to CSLib:
- Generic propositional Hilbert-style theorems (reusable by all four logics)
- A standalone modal proof system and S4/S5 theorem library
- A standalone temporal proof system, theorem library, and semantics
- The full bimodal Hilbert system, task semantics, and metalogic including a
  verified decision procedure and completeness proof

---

## Design Decisions (Modular Factoring)

Task 19 (completed 2026-06-08) produced the architectural design through team
research. The central principle:

> **Every component lives at the most general level it can compile at.**

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

### Phase 1: Foundations — Propositional Hilbert Theorems (Task 20)

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

### Phase 4: Bimodal Porting (Tasks 2–11)

**Target**: `Cslib/Logics/Bimodal/`
**Scope**: ~30,000+ lines (inherently bimodal content)

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

- [ ] All ~6,800 extractable lines ported to correct modules (Tasks 20, 21, 22)
- [ ] Temporal semantics defined standalone on LinearOrder (Task 23: ~400–600 new lines)
- [ ] Zero sorry in new code (Tasks 20–23)
- [ ] `lake build` passes with zero errors after each task
- [ ] Temporal soundness theorem proved: `TemporalBXHilbert S → S ⊢ φ → Temporal.Valid φ`
- [ ] All standalone modules self-contained (Modal/ and Temporal/ import only Foundations)
- [ ] All bimodal tasks (2–11) ported to `Cslib/Logics/Bimodal/`
- [ ] PR pipeline complete: all PRs merged to CSLib main (Task 12)
- [ ] No component double-counted: each theorem belongs to exactly one task
