# Seed Research Report: Task #23 — Temporal Semantics on Linear Orders

**Task**: 23 — Define standalone temporal semantics on linear orders
**Date**: 2026-06-08
**Sources**: Task 19 research synthesis (01_factoring-synthesis.md, 02_team-research.md)

---

## Overview

This seed report captures the relevant findings from Task 19's research for Task 23. No additional research is needed — proceed directly to planning and implementation.

Task 23 is **new infrastructure** — it is NOT a port from BimodalLogic. Standalone temporal semantics on linear orders does not exist in either cslib or BimodalLogic. BimodalLogic's temporal operators are only evaluated within the bimodal `truth_at` function over `TaskFrame`/`WorldHistory` structures. Task 23 creates an independent temporal semantic framework that makes `Temporal/` a complete standalone module.

This task was added based on team research finding #4 (Critic teammate): "This is the most important gap the research uncovered."

---

## Motivation

The absence of standalone temporal semantics means:
1. Temporal logic cannot be studied independently of bimodal context
2. Temporal soundness cannot be proved without full bimodal machinery
3. `Temporal/` is incomplete as a standalone module

Creating `Temporal.Model` on `LinearOrder` resolves all three gaps with ~400-600 lines of new code — much less than porting from bimodal.

---

## Proposed Structure

### TemporalModel

```lean
structure TemporalModel (D : Type*) [LinearOrder D] (Atom : Type*) where
  valuation : D -> Atom -> Prop
```

### Temporal.Satisfies

```lean
def Temporal.Satisfies (M : TemporalModel D Atom) (t : D) : Temporal.Formula Atom -> Prop
  | .atom p => M.valuation t p
  | .bot    => False
  | .imp φ ψ => Temporal.Satisfies M t φ -> Temporal.Satisfies M t ψ
  | .untl φ ψ =>
      ∃ s, t < s ∧
        Temporal.Satisfies M s φ ∧
        ∀ r, t < r → r < s → Temporal.Satisfies M r ψ
  | .snce φ ψ =>
      ∃ s, s < t ∧
        Temporal.Satisfies M s φ ∧
        ∀ r, s < r → r < t → Temporal.Satisfies M r ψ
```

Note: This Until/Since semantic matches the BimodalLogic `truth_at` pattern but simplified to linear orders without world histories.

### Temporal Validity

```lean
def Temporal.Valid (φ : Temporal.Formula Atom) : Prop :=
  ∀ {D : Type*} [LinearOrder D] (M : TemporalModel D Atom) (t : D),
    Temporal.Satisfies M t φ
```

### Frame Conditions on Linear Orders

With the temporal semantics in place, we can state standard LTL frame conditions:
- **Linearity**: `∀ t s, t < s ∨ s < t ∨ t = s` (already enforced by `LinearOrder`)
- **Density**: `∀ t s, t < s → ∃ r, t < r ∧ r < s`
- **Discreteness**: `∀ t, ∃ s, ∀ r, t < r → s ≤ r` (immediate successor)
- **Seriality-F**: `∀ t, ∃ s, t < s` (future exists)
- **Seriality-P**: `∀ t, ∃ s, s < t` (past exists)

---

## Prior Art and References

### LeanLTL (ITP 2025)
- Repository: https://github.com/UCSCFormalMethods/LeanLTL
- Formalizes LTL over **infinite traces** (`ℕ → State`), not linear orders
- Temporal operators match standard LTL (next, until, globally, eventually)
- Does not use Hilbert-style proof systems — uses trace semantics directly
- CSLib's approach differs: Hilbert proof system via `TemporalBXHilbert` + model-theoretic semantics on LinearOrder

### FormalizedFormalLogic/Foundation
- Repository: https://github.com/FormalizedFormalLogic/Foundation
- Uses completely separate semantic frameworks per logic
- Each logic has its own `Kripke/` directory with independent semantics
- Temporal semantics in Foundation uses frame-based approach (distinct from LeanLTL)
- Pattern to follow: Foundation's clean separation of proof system from semantics

### CSLib Existing Patterns
- `Cslib/Logics/Modal/Basic.lean`: Kripke semantics via `structure Model`
- The temporal semantics should follow the same style (structure + satisfaction function + validity)

---

## Target Structure

```
Cslib/Logics/Temporal/Semantics/
├── Model.lean          -- TemporalModel structure on LinearOrder
├── Satisfies.lean      -- Temporal.Satisfies recursive definition
└── Validity.lean       -- Temporal.Valid, frame class validity
```

---

## Scope

**Estimated**: 400-600 lines across 3 files

This is new infrastructure. The main challenge is not porting but getting the semantics right:
- The Until/Since semantics must be consistent with BimodalLogic's `truth_at` (to later prove relationship theorems)
- Frame condition definitions must align with `TemporalBXHilbert` axioms from Task 22

---

## Relationship to Other Tasks

- **Task 22** (Temporal Infrastructure): Must complete first — provides `TemporalBXHilbert` axiom system that Task 23 proves sound
- **Task 6** (Bimodal Frame Conditions + Soundness): Task 23 enables temporal soundness; bimodal soundness remains in Task 6
- **Task 8** (Bimodal Completeness): Bimodal completeness continues to use `TaskFrame`/`WorldHistory` semantics — Task 23 is for standalone temporal, not bimodal

---

## Definition of Done

1. `TemporalModel` structure defined on `LinearOrder`
2. `Temporal.Satisfies` defined for all 5 formula constructors
3. `Temporal.Valid` and frame class validity defined
4. Basic validity lemmas (e.g., `modus_ponens_valid`, `valid_implies_satisfies`)
5. Temporal soundness theorem: `TemporalBXHilbert S → S ⊢ φ → Temporal.Valid φ` (stretch goal — may be a follow-up task)

---

## References

- Team research finding #4: `specs/019_explore_modular_logic_factoring/reports/02_team-research.md`
- BimodalLogic temporal truth: `Theories/Bimodal/Semantics/Truth.lean` (for Until/Since semantics reference)
- LeanLTL: https://github.com/UCSCFormalMethods/LeanLTL
- FormalizedFormalLogic/Foundation: https://github.com/FormalizedFormalLogic/Foundation
- CSLib modal semantics pattern: `Cslib/Logics/Modal/Basic.lean`
