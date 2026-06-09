# Seed Research Report: Task #21 — Modal Proof System and Theorems

**Task**: 21 — Port modal proof system and theorems
**Date**: 2026-06-08
**Sources**: Task 19 research synthesis (01_factoring-synthesis.md, 02_team-research.md)

---

## Overview

This seed report captures the relevant findings from Task 19's research for Task 21. No additional research is needed — proceed directly to planning and implementation.

Task 21 ports ~1,600 lines of purely modal content from BimodalLogic to `Cslib/Logics/Modal/ProofSystem/` and `Cslib/Logics/Modal/Theorems/`. This creates a standalone modal proof system that fills the gap in cslib's existing modal infrastructure (which currently has semantics but no concrete proof system).

---

## Current State of Modal/ in cslib

| Component | Status |
|-----------|--------|
| `Modal.Proposition` (formula type) | Complete |
| Kripke semantics (Model, Satisfies, Validity) | Complete — `Basic.lean`, `Cube.lean`, `Denotation.lean` |
| Frame correspondence (K/T/B/4/5/D) | Complete — `Cube.lean` |
| `ModalHilbert`, `ModalS5Hilbert` typeclasses | Exist in Foundations (uninstantiated) |
| `DecidableEq` on `Modal.Proposition` | Missing — Task 16 adds this |
| Concrete `DerivationTree` | Missing — Task 21 adds this |
| Derived theorems (S4/S5, GenNec) | Missing — Task 21 adds this |

---

## Component Classification

These components from BimodalLogic use `box` but never `untl`/`snce`. They can be stated at the `[ModalHilbert S]` / `[ModalS5Hilbert S]` typeclass level and are reusable by both Modal and Bimodal logics.

| Component | Source File | Lines | Generic Signature |
|-----------|-------------|-------|-------------------|
| DerivationTree + ModalHilbert instance | (new, based on BimodalLogic pattern) | ~400 | `Modal.DerivationTree`, `instance : ModalS5Hilbert Modal.HilbertS5` |
| S4 derived theorems | `Theories/Bimodal/Theorems/ModalS4.lean` | ~400 | `[ModalHilbert S]` |
| S5 derived theorems | `Theories/Bimodal/Theorems/ModalS5.lean` | ~400 | `[ModalS5Hilbert S]` |
| GeneralizedNecessitation | `Theories/Bimodal/Theorems/GeneralizedNecessitation.lean` | ~400 | `[Necessitation S]` |

**Total scope**: ~1,600 lines

---

## Modal.DerivationTree Design

The modal DerivationTree parallels the bimodal one but drops temporal constructors:

```lean
-- Rules: assumption, modus ponens, necessitation, axiom instantiation, weakening
inductive Modal.DerivationTree (S : Type*) [ModalHilbert S] :
    Context (Modal.Proposition Atom) -> Modal.Proposition Atom -> Type*
  | assumption (h : φ ∈ Γ) : DerivationTree S Γ φ
  | mp (d1 : DerivationTree S Γ (φ ⟶ ψ)) (d2 : DerivationTree S Γ φ) : DerivationTree S Γ ψ
  | nec (d : DerivationTree S [] φ) : DerivationTree S Γ (□φ)
  | axm (h : S ⊢ φ) : DerivationTree S Γ φ   -- using InferenceSystem axiom method
  | weak (d : DerivationTree S Γ φ) (h : Γ ⊆ Γ') : DerivationTree S Γ' φ
```

Then register instances:
```lean
instance : ModalS5Hilbert Modal.HilbertS5 := ...
instance : InferenceSystem Modal.HilbertS5 (Modal.Judgement Atom) := ...
```

---

## Key Dependencies

- **Task 16** (DecidableEq on Modal.Proposition): Required for unification/equality checks in derivation tree operations
- **Task 20** (Propositional Hilbert Theorems): The modal theorems can import and extend propositional lemmas; S4/S5 derived theorems build on propositional results

---

## Target Structure

```
Cslib/Logics/Modal/
├── ProofSystem/
│   ├── DerivationTree.lean    -- DerivationTree inductive, inference rules
│   ├── Derivable.lean         -- Derivable predicate, InferenceSystem instance
│   └── Substitution.lean      -- Modal.Proposition.subst + substitution theorem
└── Theorems/
    ├── ModalS4.lean           -- S4 derived theorems: [ModalHilbert S]
    ├── ModalS5.lean           -- S5 derived theorems: [ModalS5Hilbert S]
    └── GeneralizedNecessitation.lean  -- GenNec: [Necessitation S]
```

---

## Relationship to Other Tasks

- **Task 5** (Bimodal Derived Theorems): After Task 21 creates the modal theorems, Task 5 can import them rather than duplicating. Task 5 scope is reduced to Perpetuity/ only.
- **Task 7** (Bimodal MCS/Deduction): DeductionTheorem stays in Task 7 (bimodal-specific, requires bimodal DerivationTree induction)

---

## Mathlib Contribution Candidate

Once Task 21 is complete, `Modal/ProofSystem/` + `Modal/Theorems/` would be a strong Mathlib contribution candidate alongside the existing `Modal/Basic.lean` (frame correspondence). The team research notes this as one of the highest-readiness contributions.

---

## References

- Research synthesis: `specs/019_explore_modular_logic_factoring/reports/01_factoring-synthesis.md`
- Team research: `specs/019_explore_modular_logic_factoring/reports/02_team-research.md`
- Existing modal semantics: `Cslib/Logics/Modal/Basic.lean`, `Cube.lean`
- Typeclass hierarchy: `Cslib/Foundations/Logic/ProofSystem.lean`
- BimodalLogic source: `Theories/Bimodal/Theorems/ModalS4.lean`, `ModalS5.lean`, `GeneralizedNecessitation.lean`
