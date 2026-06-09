# Project Roadmap: Modular Logic Porting Plan

*Generated from task 19 research (2026-06-08). This plan reflects the modular factoring of BimodalLogic into standalone Propositional, Modal, Temporal, and Bimodal modules.*

---

## Overview

cslib's logic library is being populated by porting ~35,000 lines of BimodalLogic (Lean 4) into modular components. The porting is organized into four phases following the import hierarchy:

```
Foundations/Logic/Theorems/ (Task 20)
  ↓
Modal/ProofSystem/ + Modal/Theorems/ (Task 21)
Temporal/ProofSystem/ + Temporal/Theorems/ (Task 22)
  ↓
Temporal/Semantics/ (Task 23)
  ↓
Bimodal/ (Tasks 2-11)
```

This hierarchy enforces that generic content lives at the most reusable level, preventing duplication across logics.

---

## Phase 1: Foundations — Propositional Hilbert Theorems

**Task**: 20
**Target**: `Cslib/Foundations/Logic/Theorems/`
**Scope**: ~2,400 lines from BimodalLogic

Port propositional theorems as generic `[PropositionalHilbert S]` lemmas reusable by all four logics:

| Component | Lines | Source |
|-----------|-------|--------|
| Combinators (I, B, C, S) | ~300 | BimodalLogic/Theorems/Combinators.lean |
| Propositional/{Core,Connectives,Reasoning} | ~1,100 | BimodalLogic/Theorems/Propositional/ |
| ContextualProofs (weakening, cut) | ~500 | BimodalLogic/Theorems/ContextualProofs.lean |
| BigConj (generic) | ~500 | BimodalLogic/Syntax/BigConj.lean |

**Note**: DeductionTheorem stays per-logic (requires structural induction on DerivationTree; cannot be ported generically).

**Milestone**: *Foundations complete* — all four logics can import propositional theorems without bimodal dependency.

---

## Phase 2: Modal and Temporal Modules

**Tasks**: 21 (Modal) and 22 (Temporal) — can execute in parallel after Task 20

### Task 21: Modal Proof System and Theorems
**Target**: `Cslib/Logics/Modal/ProofSystem/` + `Cslib/Logics/Modal/Theorems/`
**Scope**: ~1,600 lines from BimodalLogic

| Component | Lines | Typeclass |
|-----------|-------|-----------|
| Modal.DerivationTree + ModalS5Hilbert instance | ~400 | Provides ModalHilbert, ModalS5Hilbert |
| S4/S5 derived theorems | ~800 | `[ModalHilbert S]` / `[ModalS5Hilbert S]` |
| GeneralizedNecessitation | ~400 | `[Necessitation S]` |

### Task 22: Temporal Infrastructure and Theorems
**Target**: Axioms.lean + ProofSystem.lean additions + `Cslib/Logics/Temporal/ProofSystem/` + `Cslib/Logics/Temporal/Theorems/`
**Scope**: ~1,500 lines (new infrastructure + ports from BimodalLogic)

| Component | Lines | Note |
|-----------|-------|------|
| ~20 temporal axiom abbrevs in Axioms.lean | ~100 | TK, T4, TT-F/P, TA, TL, Lin, BX axioms |
| ~20 HasAxiom* typeclasses in ProofSystem.lean | ~200 | HasAxiomTK, HasAxiomT4, etc. |
| TemporalBXHilbert restructuring | ~50 | Extend all temporal HasAxiom* classes |
| TemporalNecessitation non-empty | ~50 | Add actual derivation rule |
| BimodalTMHilbert compatibility instance | ~100 | Diamond-avoidance (mirrors BimodalConnectives) |
| Temporal.DerivationTree + TemporalBXHilbert instance | ~200 | New proof system |
| TemporalDerived theorems | ~790 | `[TemporalBXHilbert S]` |
| Frame condition typeclasses | ~130 | LinearTemporalFrame, DenseTemporalFrame, DiscreteTemporalFrame |

**Milestone**: *Standalone modules complete* — Modal/ and Temporal/ are self-contained modules with proof systems, theorems, and connections to Foundations.

---

## Phase 3: Temporal Semantics on Linear Orders

**Task**: 23
**Target**: `Cslib/Logics/Temporal/Semantics/`
**Scope**: ~400-600 lines (new infrastructure, not ported from BimodalLogic)

Define standalone temporal semantics:

```lean
structure TemporalModel (D : Type*) [LinearOrder D] (Atom : Type*) where
  valuation : D -> Atom -> Prop

def Temporal.Satisfies (M : TemporalModel D Atom) (t : D) : Temporal.Formula Atom -> Prop
  | .atom p  => M.valuation t p
  | .bot     => False
  | .imp φ ψ => Temporal.Satisfies M t φ -> Temporal.Satisfies M t ψ
  | .untl φ ψ => ∃ s, t < s ∧ Temporal.Satisfies M s φ ∧ ∀ r, t < r → r < s → Temporal.Satisfies M r ψ
  | .snce φ ψ => ∃ s, s < t ∧ Temporal.Satisfies M s φ ∧ ∀ r, s < r → r < t → Temporal.Satisfies M r ψ
```

This fills the critical gap identified by team research: temporal logic can now be studied standalone (soundness, completeness relative to linear orders) without bimodal machinery.

**Milestone**: *Temporal semantics complete* — `Temporal/` is a fully standalone module with syntax, proof system, theorems, and semantics.

---

## Phase 4: Bimodal Porting

**Tasks**: 2-11
**Target**: `Cslib/Logics/Bimodal/`
**Scope**: ~30,000+ lines (inherently bimodal content)

Bimodal porting tasks (in dependency order):

| Task | Component | Scope | Depends On |
|------|-----------|-------|------------|
| 2 | Bimodal Syntax (Context, BigConj, Subformulas) | ~2,500 lines | BimodalLogic:291 |
| 3 | Task Frame Semantics (TaskFrame, WorldHistory, Truth) | ~2,200 lines | 2 |
| 4 | Bimodal Proof System (42-axiom Axiom, DerivationTree) | ~2,000 lines | 2, 20, 22 |
| 5 | Perpetuity Theorems (bimodal fixed-point theorems) | ~800 lines | 4, 21, 22 |
| 6 | Frame Conditions + Soundness | ~2,370 lines | 3, 4 |
| 7 | Deduction + MCS Theory | ~2,500 lines | 4, 5 |
| 8 | Completeness | ~15,000 lines | 6, 7 |
| 9 | Decidability + Tableau | ~10,000 lines | 4, 7 |
| 10 | Separation Theorem | ~3,500 lines | 4, 5, 7 |
| 11 | Conservative Extension | ~1,500 lines | 4 |

**Milestone**: *Bimodal integration complete* — all ~30,000+ lines of bimodal-specific content ported to `Cslib/Logics/Bimodal/`.

**PR pipeline milestone**: PR pipeline complete after Task 12 finalized (all PRs merged to cslib main).

---

## Dependency Wave Structure

The import hierarchy enforces a clean wave structure:

| Wave | Tasks | Blocked by |
|------|-------|------------|
| 1 | 2, 12, 15, 16, 17, 18, 20 | -- (no logic-task dependencies) |
| 2 | 3 (dep 2), 21 (dep 16,20), 22 (dep 20) | Wave 1 |
| 3 | 4 (dep 2,20,22), 11 (dep 4) | Wave 2 |
| 4 | 5 (dep 4,21,22), 6 (dep 3,4), 23 (dep 22) | Wave 3 |
| 5 | 7 (dep 4,5) | Wave 4 |
| 6 | 8 (dep 6,7), 9 (dep 4,7), 10 (dep 4,5,7) | Wave 5 |

**Foundations-first invariant**: Task 20 is Wave 1 (no logic-task deps). Tasks 21 and 22 depend on Task 20 (Wave 2). Bimodal tasks (Wave 3+) depend on Foundations and standalone modules. This enforces: Foundations -> Modal/Temporal -> Bimodal.

---

## Component Accounting

Every extractable component maps to exactly one task:

| Component | Task | Lines |
|-----------|------|-------|
| Combinators + Propositional/ + ContextualProofs + BigConj | 20 | ~2,400 |
| Modal DerivationTree + S4/S5 theorems + GenNec | 21 | ~1,600 |
| Temporal infra + HasAxiom* + TemporalDerived + FrameConditions | 22 | ~1,500 |
| Temporal semantics on LinearOrder | 23 | ~400-600 |
| Perpetuity/ | 5 | ~800 |
| DeductionTheorem (stays per-logic) | 7 | ~500 |
| Bimodal-specific content | 2-11 | ~30,000+ |

**Total extractable**: ~2,400 + ~1,600 + ~1,500 + ~500 + ~800 = ~6,800 lines moved to reusable locations (plus ~400-600 new temporal semantics).

---

## Success Metrics

- [ ] All ~5,000 extractable lines ported to correct modules (Task 20: ~2,400, Task 21: ~1,600, Task 22: ~1,500)
- [ ] Temporal semantics defined standalone (Task 23: ~400-600 new lines)
- [ ] Zero sorry in new code (Tasks 20-23)
- [ ] `lake build` passes with zero errors after each task
- [ ] Temporal soundness theorem proved: `TemporalBXHilbert S → S ⊢ φ → Temporal.Valid φ`
- [ ] All bimodal tasks (2-11) ported to `Cslib/Logics/Bimodal/`
- [ ] PR pipeline complete: all PRs merged to cslib main
- [ ] No component double-counted: each theorem belongs to exactly one task
