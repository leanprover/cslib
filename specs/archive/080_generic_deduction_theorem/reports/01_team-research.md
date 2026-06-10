# Research Report: Task #80

**Task**: Generic DeductionTheorem interface across all logic domains
**Date**: 2026-06-10
**Mode**: Team Research (4 teammates)
**Revised**: 2026-06-10 (post-synthesis risk review)

## Summary

A fully generic deduction theorem (one proof serving all 4 logics) is infeasible in Lean 4 due to the fundamental constraint that pattern matching and well-founded recursion cannot operate through typeclass-mediated abstract types. The recommended approach is a **shared helper typeclass**: a lightweight `HasHilbertTree` typeclass in `Foundations/Logic/` that abstracts the 4 purely-constructive helper lemmas (`deduction_axiom`, `deduction_imp_self`, `deduction_assumption_other`, `deduction_mp`), while each logic retains its own thin `deduction_with_mem` and `deduction_theorem` calling the generic helpers. Estimated net savings: ~120 lines (from 952 total), with near-zero risk and improved maintainability through single-sourcing the helper logic. The approach prioritizes clarity, robustness, and ease of extension — qualities essential for a cornerstone library.

## Key Findings

### 1. The Duplication Is Real and Structural

All 4 DeductionTheorem files (952 lines total) follow an identical 7-component proof skeleton. The **only** differences are:

| Aspect | PL (4 ctors) | Modal (5) | Temporal (6) | Bimodal (7) |
|--------|-------------|-----------|-------------|-------------|
| Extra constructors | none | necessitation | temporal_nec, temporal_dual | all three |
| FrameClass param | none | none | `FrameClass.Base` (hardcoded) | `{fc : FrameClass}` (polymorphic) |
| Axiom K name | `.implyK` | `.implyK` | `.imp_s` (swapped!) | `.imp_s` (swapped!) |
| Axiom S name | `.implyS` | `.implyS` | `.imp_k` (swapped!) | `.imp_k` (swapped!) |
| `.ax` ctor args | 3 (no frame class) | 3 | 4 (+`h_fc`) | 4 (+`h_fc`) |
| Empty subset proof | `fun _ h => nomatch h` | same | `List.nil_subset _` | `List.nil_subset _` |
| Height lemma names | `height_modus_ponens_left` | same | same | `mp_height_gt_left` (different!) |

Every extra constructor requires empty context and is uniformly discharged by `simp at hA`.

### 2. The Fundamental Constraint: No Pattern Matching on Abstract Types

All 4 teammates independently identified the same critical constraint: **Lean 4 cannot `match` on a typeclass-provided type.** The `deduction_with_mem` and `deduction_theorem` proofs require:

```lean
match d with
| .ax _ ψ h_ax => ...
| .assumption _ ψ h_mem => ...
| .modus_ponens _ ψ χ d₁ d₂ => ...
| .weakening Γ'' _ ψ d' h_sub => ...
```

This is case analysis over an inductive type's constructors — not method dispatch. A typeclass exposing "constructor accessors" (as the task description proposes) is insufficient. The proof needs an **elimination principle**, not field getters.

### 3. Why the Full-Generic Approaches Fail

Three approaches for a single generic proof were evaluated and all have serious problems:

**`DerivationCase` inductive (Teammate B)**: Define a shared case-analysis type, match on that. Problem: the recursive calls in `deduction_with_mem` use `d₁`, `d₂`, `d'` — variables bound by `match`. These are structural sub-terms of `d`, which Lean's termination checker can see. If those variables instead come from a typeclass `cases` method, they're opaque outputs — Lean cannot verify `d₁.height < d.height`. The `DerivationCase` type would need height-decrease witnesses as extra fields, parameterized by the original tree. The type signature balloons and each logic's `cases` implementation must prove these height decreases. The generic proof becomes harder to read than the concrete proof it replaces.

**Parameterized single inductive (Teammate C)**: Define `GenericDerivationTree` with an `ExtraRule` parameter. Problem: requires refactoring all 4 logic domains' `DerivationTree` types and all downstream code that pattern-matches on them. Too invasive for the savings.

**Abstract recursor typeclass (Teammate B, Alternative B)**: Expose a hand-rolled `casesOn` in the typeclass. Problem: the motive-based recursor pattern becomes extremely complex for mutually-recursive functions (`deduction_with_mem` + `deduction_theorem`), and well-founded recursion still needs height witnesses.

### 4. What CAN Be Shared: The 4 Helper Lemmas

The 4 helper lemmas are purely constructive — they *build* derivation trees without pattern matching:

| Helper | What it does | Uses |
|--------|-------------|------|
| `deduction_axiom` | If `⊢ φ` then `Γ ⊢ A → φ` | `implyK`, `mp`, `weakening` |
| `deduction_imp_self` | `Γ ⊢ A → A` | `implyS`, `implyK`, `mp`, `weakening` |
| `deduction_assumption_other` | If `B ∈ Γ` then `Γ ⊢ A → B` | `assumption`, `implyK`, `mp`, `weakening` |
| `deduction_mp` | From `Γ ⊢ A→(C→D)` and `Γ ⊢ A→C`, get `Γ ⊢ A→D` | `implyS`, `mp`, `weakening` |

These need only 6 typeclass fields: `Tree`, `implyK`, `implyS`, `assumption`, `mp`, `weakening`. No height, no elimination, no termination issues. Each logic's instance is ~10 lines mapping directly to its existing constructors.

### 5. Axiom Naming Is Semantically Swapped (Must Fix First)

PL/Modal follow the standard naming (K = weakening `φ → ψ → φ`, S = distribution). Temporal/Bimodal have the names **backwards**: `.imp_s` means the K combinator, `.imp_k` means the S combinator. This was harmonized by Task 79 (now `[COMPLETED]`), which should have addressed naming consistency.

### 6. Prior Art Validates Conservative Approach

The FormalizedFormalLogic/Foundation project (largest Lean 4 multi-logic formalization) does **not** share deduction theorem proofs across logics. Each logic proves its own independently. This confirms that full generic abstraction is non-trivial even for the most mature Lean 4 logic libraries.

## Synthesis

### Approaches Evaluated

| Approach | Lines saved | Risk | Readability | Verdict |
|----------|-----------|------|-------------|---------|
| Full generic via `DerivationCase` | ~400-500 | High (termination checker) | Worse (indirection) | Rejected |
| Parameterized single inductive | ~500+ | High (invasive refactor) | Neutral | Rejected |
| Abstract recursor typeclass | ~400-500 | High (complex signatures) | Worse | Rejected |
| **Shared helpers typeclass** | **~120** | **Near-zero** | **Better** | **Recommended** |
| Tactic/macro generation | ~400-500 | Medium (maintenance) | Worse (hidden code) | Rejected |

### Why Shared Helpers Wins for a Cornerstone Library

For CSLib as a community resource, the criteria that matter most are:

1. **Readability**: A newcomer can read one file and understand the proof. The helper typeclass has 6 fields with obvious semantics. No indirection through `DerivationCase`, no height witnesses, no abstract elimination.

2. **Maintainability**: Adding logic #5 means writing ~10 lines of instance + copy-pasting a ~120-line thin wrapper (vs. understanding `DerivationCase` + height coherence + abstract termination). The helpers ensure the common parts stay consistent.

3. **Robustness**: The per-logic `deduction_with_mem`/`deduction_theorem` use native `match` and `termination_by` on concrete types. No risk of breakage from Lean version changes to the termination checker or typeclass resolution.

4. **Single-sourcing benefit**: The 4 helpers (`deduction_axiom`, `deduction_imp_self`, `deduction_assumption_other`, `deduction_mp`) contain the core mathematical insight. Having them in one place means a fix or improvement propagates to all logics automatically.

## Recommendations

### Design: `HasHilbertTree` Typeclass with Generic Helpers

```lean
-- In Cslib/Foundations/Logic/Metalogic/DeductionHelpers.lean

namespace Cslib.Logic

/-- Minimal interface for building Hilbert-style derivation trees.
    Enables generic helper lemmas for the deduction theorem. -/
class HasHilbertTree (F : Type*) [HasImp F] where
  /-- The derivation tree type, parameterized by context and formula. -/
  Tree : List F → F → Type*
  /-- Axiom K derivation: `⊢ φ → (ψ → φ)` -/
  implyK : (φ ψ : F) → Tree [] (HasImp.imp φ (HasImp.imp ψ φ))
  /-- Axiom S derivation: `⊢ (φ→ψ→χ)→(φ→ψ)→(φ→χ)` -/
  implyS : (φ ψ χ : F) → Tree [] (HasImp.imp
    (HasImp.imp φ (HasImp.imp ψ χ))
    (HasImp.imp (HasImp.imp φ ψ) (HasImp.imp φ χ)))
  /-- Assumption rule. -/
  assumption : (Γ : List F) → (φ : F) → φ ∈ Γ → Tree Γ φ
  /-- Modus ponens. -/
  mp : (Γ : List F) → (φ ψ : F) →
    Tree Γ (HasImp.imp φ ψ) → Tree Γ φ → Tree Γ ψ
  /-- Weakening. -/
  weakening : (Γ Δ : List F) → (φ : F) →
    Tree Γ φ → (∀ x ∈ Γ, x ∈ Δ) → Tree Δ φ

variable {F : Type*} [HasImp F] [HasHilbertTree F]

/-- If `⊢ φ` (empty-context derivation), then `Γ ⊢ A → φ`. -/
noncomputable def deduction_axiom (Γ : List F) (A : F)
    {φ : F} (d_empty : HasHilbertTree.Tree (F := F) [] φ) :
    HasHilbertTree.Tree Γ (HasImp.imp A φ) :=
  let k := HasHilbertTree.implyK φ A
  let step := HasHilbertTree.mp [] φ (HasImp.imp A φ) k d_empty
  HasHilbertTree.weakening [] Γ _ step (fun _ h => nomatch h)

/-- `Γ ⊢ A → A` (identity). -/
noncomputable def deduction_imp_self (Γ : List F) (A : F) :
    HasHilbertTree.Tree (F := F) Γ (HasImp.imp A A) :=
  let s := HasHilbertTree.implyS A (HasImp.imp A A) A
  let k1 := HasHilbertTree.implyK A (HasImp.imp A A)
  let k2 := HasHilbertTree.implyK A A
  let step1 := HasHilbertTree.mp [] _ _ s k1
  let result := HasHilbertTree.mp [] _ _ step1 k2
  HasHilbertTree.weakening [] Γ _ result (fun _ h => nomatch h)

/-- If `B ∈ Γ`, then `Γ ⊢ A → B`. -/
noncomputable def deduction_assumption_other (Γ : List F)
    (A B : F) (h_mem : B ∈ Γ) :
    HasHilbertTree.Tree (F := F) Γ (HasImp.imp A B) :=
  let b_deriv := HasHilbertTree.assumption Γ B h_mem
  let k := HasHilbertTree.implyK B A
  let k_weak := HasHilbertTree.weakening [] Γ _ k (fun _ h => nomatch h)
  HasHilbertTree.mp Γ B (HasImp.imp A B) k_weak b_deriv

/-- From `Γ ⊢ A→(C→D)` and `Γ ⊢ A→C`, derive `Γ ⊢ A→D`. -/
noncomputable def deduction_mp_under_imp (Γ : List F) (A C D : F)
    (h₁ : HasHilbertTree.Tree (F := F) Γ (HasImp.imp A (HasImp.imp C D)))
    (h₂ : HasHilbertTree.Tree (F := F) Γ (HasImp.imp A C)) :
    HasHilbertTree.Tree Γ (HasImp.imp A D) :=
  let s := HasHilbertTree.implyS A C D
  let s_weak := HasHilbertTree.weakening [] Γ _ s (fun _ h => nomatch h)
  let step1 := HasHilbertTree.mp Γ _ _ s_weak h₁
  HasHilbertTree.mp Γ _ _ step1 h₂
```

### Per-Logic Instance (Example: Modal)

```lean
instance : HasHilbertTree (Proposition Atom) where
  Tree := DerivationTree
  implyK := fun φ ψ => .ax [] _ (.implyK φ ψ)
  implyS := fun φ ψ χ => .ax [] _ (.implyS φ ψ χ)
  assumption := DerivationTree.assumption
  mp := DerivationTree.modus_ponens
  weakening := DerivationTree.weakening
```

### Per-Logic Thin Wrapper (Example: Modal `deduction_with_mem`)

Each logic's `deduction_with_mem` and `deduction_theorem` remain concrete (native `match`, native `termination_by`) but call the generic helpers:

```lean
noncomputable def deduction_with_mem
    (Γ' : List (Proposition Atom)) (A φ : Proposition Atom)
    (d : DerivationTree Γ' φ) (hA : A ∈ Γ') :
    DerivationTree (removeAll Γ' A) (A.imp φ) := by
  match d with
  | .ax _ ψ h_ax =>
    exact deduction_axiom (removeAll Γ' A) A (.ax [] ψ h_ax)
  | .assumption _ ψ h_mem =>
    by_cases h_eq : ψ = A
    · subst h_eq; exact deduction_imp_self _ ψ
    · exact deduction_assumption_other _ A ψ (mem_removeAll_of_mem_of_ne h_mem h_eq)
  | .modus_ponens _ ψ χ d₁ d₂ =>
    exact deduction_mp_under_imp _ A ψ χ
      (deduction_with_mem Γ' A _ d₁ hA) (deduction_with_mem Γ' A _ d₂ hA)
  | .necessitation ψ _d' => simp at hA
  | .weakening Γ'' _ ψ d' h_sub =>
    -- weakening case uses generic helpers for the K-axiom sub-proof
    ...
termination_by d.height
```

### Code Reduction Estimate

| Component | Current (4 files) | After (generic + instances) | Savings |
|-----------|-------------------|---------------------------|---------|
| 4 helper defs | 4 × ~8 = 32 lines each, ~120 total | 1 × ~40 (generic) | ~80 lines |
| `HasHilbertTree` class | 0 | ~20 lines | -20 lines |
| 4 instances | 0 | 4 × ~8 = 32 lines | -32 lines |
| `deduction_with_mem` | 4 × ~35 = ~140 lines | 4 × ~25 = ~100 lines | ~40 lines |
| `deduction_theorem` | 4 × ~40 = ~160 lines | 4 × ~30 = ~120 lines | ~40 lines |
| `*_has_deduction_theorem` | 4 × ~6 = ~24 lines | unchanged | 0 |
| **Total** | **~952 lines** | **~820 lines** | **~130 lines saved** |

The real value is not line count but **single-sourcing**: the 4 helpers encode the core mathematical insight (how K and S axioms build deduction sub-proofs). A bug fix or optimization in the generic helpers propagates to all logics automatically.

### Implementation Sequence

1. **Verify Task 79 harmonized axiom names** — confirm `.imp_s`/`.imp_k` are now consistent with `.implyK`/`.implyS` across all logics. If not, harmonize as a prerequisite.
2. **Create `Cslib/Foundations/Logic/Metalogic/DeductionHelpers.lean`** — `HasHilbertTree` typeclass + 4 generic helper defs.
3. **Add `HasHilbertTree` instance** in each logic's DeductionTheorem.lean.
4. **Refactor each `deduction_with_mem` and `deduction_theorem`** to call generic helpers instead of inline helper defs. Remove the per-logic helper def duplicates.
5. **Verify `lake build`** passes with zero errors.
6. **Verify each `*_has_deduction_theorem`** still connects to the MCS framework.

### Design Constraints

- **6 typeclass fields** — minimal, obvious semantics, easy to instantiate
- **No height, no elimination, no termination concerns** in the typeclass
- **No changes to existing `DerivationTree` inductives**
- **Per-logic files retain native `match` and `termination_by`** — robust against Lean version changes

### Why NOT the `DerivationCase` Approach

The `DerivationCase` approach was the original synthesis recommendation but was rejected after deeper analysis:

1. **Termination checker**: Recursive calls in `deduction_with_mem` use pattern-bound variables (`d₁`, `d₂`, `d'`). These are structural sub-terms visible to Lean's WF checker. When extracted via a `cases` method, they become opaque outputs. The `DerivationCase` type would need height-decrease witnesses as extra fields, parameterized by the original tree — making the type signature complex and each logic's instance non-trivial.

2. **Indirection cost**: A newcomer must understand `DerivationCase`, `HasDerivationTree`, the `cases` method, and height coherence before understanding any single logic's proof. For a cornerstone library, this indirection harms readability more than the duplication it eliminates.

3. **Fragility**: The generic proof depends on Lean 4's interaction between typeclass resolution, well-founded recursion, and abstract types. Changes to any of these in future Lean versions could break all 4 logics simultaneously. Concrete proofs are immune to this.

4. **Diminishing returns**: The helpers-only approach captures the genuinely shared mathematical content (K/S axiom manipulation). The remaining per-logic code (`match` + termination) is mechanical boilerplate that is stable and rarely needs updating.

## Teammate Contributions

| Teammate | Angle | Status | Confidence | Key Insight |
|----------|-------|--------|------------|-------------|
| A | Primary approach | completed | high | Two-layer hybrid; helpers-only is safest |
| B | Alternative patterns | completed | high | `DerivationCase` viable in theory, risk in practice |
| C | Critic | completed | high | Pattern matching + termination are true blockers |
| D | Strategic horizons | completed | high | FormalizedFormalLogic validates conservative approach |

## References

- `Cslib/Foundations/Logic/Metalogic/Consistency.lean` — existing MCS abstraction
- `Cslib/Foundations/Logic/ProofSystem.lean` — existing typeclass hierarchy
- `Cslib/Foundations/Logic/Helpers/ListHelpers.lean` — shared list utilities
- [FormalizedFormalLogic/Foundation](https://github.com/FormalizedFormalLogic/Foundation) — does not share deduction proofs across logics
- [James Oswald: Extending Inductive Types in Lean4](https://jamesoswald.dev/posts/meditation-extending-inductive-types/)
- [Lean 4 Inductive Types Reference](https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/)
