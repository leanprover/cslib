# Research Report: Task #80

**Task**: Generic DeductionTheorem interface across all logic domains
**Date**: 2026-06-10
**Mode**: Team Research (4 teammates)

## Summary

A generic deduction theorem is feasible but the task description's proposed typeclass design needs significant revision. The fundamental constraint is that Lean 4 cannot pattern-match on abstract types — the proof requires structural case analysis over concrete inductive constructors, which typeclasses cannot directly expose. The recommended approach is a **two-tier design**: a shared `DerivationCase` inductive that captures the 4 common constructor patterns plus a catch-all for empty-context-only extras, combined with a `HasDerivationTree` typeclass whose `cases` method maps each logic's concrete tree into `DerivationCase`. This enables a single generic proof with pattern matching on the shared type. Estimated net savings: 400-500 lines (from 952 total). Fallback if termination checking fails: share only the 4 helper lemmas (~105 lines saved).

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

All 4 teammates independently identified the same critical constraint: **Lean 4 cannot `match` on a typeclass-provided type.** The deduction theorem proof requires:

```lean
match d with
| .ax _ ψ h_ax => ...
| .assumption _ ψ h_mem => ...
| .modus_ponens _ ψ χ d₁ d₂ => ...
| .weakening Γ'' _ ψ d' h_sub => ...
```

This is case analysis over an inductive type's constructors — not method dispatch. A typeclass exposing "constructor accessors" (as the task description proposes) is insufficient. The proof needs an **elimination principle**, not field getters.

### 3. Axiom Naming Is Semantically Swapped (Must Fix First)

PL/Modal follow the standard naming (K = weakening `φ → ψ → φ`, S = distribution). Temporal/Bimodal have the names **backwards**: `.imp_s` means the K combinator, `.imp_k` means the S combinator. This must be harmonized before or during implementation, likely as part of Task 79.

### 4. Prior Art Validates Typeclass Direction

The FormalizedFormalLogic/Foundation project (largest Lean 4 multi-logic formalization, with Gödel incompleteness formalized) uses a similar architecture: `Entailment`, `Deduction`, `Axiomatized` typeclasses abstracting over proof systems. However, it works at `Prop`-level (derivability), not `Type`-level (concrete trees). CSLib's additional challenge is exposing tree structure for pattern matching.

## Synthesis

### Conflicts Between Teammates

| Question | Teammate A | Teammate B | Teammate C | Teammate D |
|----------|-----------|-----------|-----------|-----------|
| Can full generic proof work? | No — share helpers only | Yes — via `DerivationCase` inductive | Unlikely — recommend parameterized inductive | Yes — with ≤8-field typeclass |
| Lines saved | ~105 | ~400-500 | ~500+ (but invasive) | ~500 |
| Risk level | Low | Medium (termination checker) | High (requires refactoring all trees) | Medium |

### Resolution

The approaches form a natural **tiered strategy**:

**Tier 1 (Safe)**: Share the 4 helper lemmas via `HasHilbertTree` typeclass (Teammate A). These build derivation trees and don't require pattern matching. Guaranteed to work. ~105 lines saved.

**Tier 2 (Recommended)**: Full generic proof via `DerivationCase` inductive (Teammate B). Define a concrete shared case-analysis type that the generic proof matches on. Each logic maps its constructors into `DerivationCase` via a typeclass `cases` method. This enables writing `deduction_with_mem` and `deduction_theorem` once. ~400-500 lines saved. **Risk**: Lean 4's well-founded recursion checker may struggle with `termination_by (cases d).height` through an abstract height function.

**Tier 3 (Fallback if Tier 2 termination fails)**: Combine Tier 1 helpers with thin per-logic wrappers that call generic helpers for common cases and `simp at hA` for extras. ~200-300 lines saved.

**Rejected**: Parameterized single inductive (Teammate C) — too invasive, requires refactoring all downstream code. Tactic/macro approach — high maintenance cost for 4 instances.

### Gaps Identified

1. **Well-founded recursion through `cases` method**: Untested. The `decreasing_by` blocks reference pattern-bound variables (`d₁`, `d₂`, `d'`) that exist only inside `match` arms. If `cases` is a typeclass method rather than a native `match`, these variables live in continuation closures. Lean's WF elaborator may reject.

2. **FrameClass three-way split**: PL/Modal have none, Temporal hardcodes `FrameClass.Base`, Bimodal is polymorphic. The generic interface needs one consistent approach (likely parameterize and let PL/Modal use `Unit`).

3. **Task 79 dependency status**: Task 79 is `[PLANNED]` — its Phase 1 (list helpers) is done, but axiom naming harmonization hasn't happened. Task 80 may need to handle or defer this.

## Recommendations

### Primary: Tier 2 Design with Tier 1 Fallback

```lean
-- In Foundations/Logic/Metalogic/DeductionGeneric.lean

/-- Common cases for derivation tree case analysis. Each logic maps its
    concrete constructors into this type. -/
inductive DerivationCase (F : Type*) [HasImp F]
    (Tree : List F → F → Type*) (Γ : List F) (φ : F) where
  | ax : Tree [] φ → DerivationCase F Tree Γ φ
  | assumption : φ ∈ Γ → DerivationCase F Tree Γ φ
  | mp : (ψ : F) → Tree Γ (HasImp.imp ψ φ) → Tree Γ ψ →
      DerivationCase F Tree Γ φ
  | weakening : (Γ' : List F) → Tree Γ' φ → (Γ' ⊆ Γ) →
      DerivationCase F Tree Γ φ
  | extraEmptyCtx : Γ = [] → DerivationCase F Tree Γ φ

/-- Typeclass for derivation trees supporting the generic deduction theorem. -/
class HasDerivationTree (F : Type*) [HasImp F] [HasBot F] where
  Tree : List F → F → Type*
  height : Tree Γ φ → Nat
  cases : Tree Γ φ → DerivationCase F Tree Γ φ
  -- Constructors (for building new trees in the generic proof)
  mk_assumption : (Γ : List F) → (φ : F) → φ ∈ Γ → Tree Γ φ
  mk_mp : (Γ : List F) → (φ ψ : F) → Tree Γ (HasImp.imp φ ψ) → Tree Γ φ → Tree Γ ψ
  mk_weakening : (Γ Δ : List F) → (φ : F) → Tree Γ φ → (Γ ⊆ Δ) → Tree Δ φ
  mk_implyK : (φ ψ : F) → Tree [] (HasImp.imp φ (HasImp.imp ψ φ))
  mk_implyS : (φ ψ χ : F) → Tree [] (HasImp.imp
    (HasImp.imp φ (HasImp.imp ψ χ))
    (HasImp.imp (HasImp.imp φ ψ) (HasImp.imp φ χ)))
  -- Height lemmas (for termination)
  height_mp_left : ∀ {Γ φ ψ} (d₁ : Tree Γ (HasImp.imp φ ψ)) (d₂ : Tree Γ φ),
    d₁.height < (mk_mp Γ φ ψ d₁ d₂).height  -- may need adjustment
  height_mp_right : ...
  height_weakening : ...
  -- Case/height coherence
  height_cases_mp : ∀ ... -- extracted components have smaller height
```

### Per-Logic Instance (Example: Modal)

```lean
instance : HasDerivationTree (Proposition Atom) where
  Tree := DerivationTree
  height := DerivationTree.height
  cases := fun d => match d with
    | .ax _ φ h_ax => .ax (.ax [] φ h_ax)
    | .assumption _ φ h_mem => .assumption h_mem
    | .modus_ponens _ φ ψ d₁ d₂ => .mp φ d₁ d₂
    | .necessitation _ _ => .extraEmptyCtx rfl
    | .weakening Γ' _ φ d' h_sub => .weakening Γ' d' h_sub
  mk_assumption := DerivationTree.assumption
  mk_mp := DerivationTree.modus_ponens
  mk_weakening := DerivationTree.weakening
  mk_implyK := fun φ ψ => .ax [] _ (.implyK φ ψ)
  mk_implyS := fun φ ψ χ => .ax [] _ (.implyS φ ψ χ)
  ...
```

### Implementation Sequence

1. **Harmonize axiom names** (as part of task 79 or as a prerequisite): Rename Temporal/Bimodal `.imp_s`→`.implyK`, `.imp_k`→`.implyS` to match PL/Modal standard.
2. **Harmonize height lemma names**: Rename Bimodal `mp_height_gt_left`→`height_modus_ponens_left` etc.
3. **Create `DerivationCase` inductive** and `HasDerivationTree` typeclass in `Foundations/Logic/Metalogic/`.
4. **Attempt generic `deduction_with_mem` and `deduction_theorem`** over `HasDerivationTree`. Test termination checker.
5. **If termination works**: Provide instances for all 4 logics. Each domain file becomes ~20-30 lines.
6. **If termination fails**: Fall back to Tier 1 (shared helper lemmas only). Each domain file becomes ~120-150 lines using generic helpers.

### Design Constraints

- **≤10 typeclass fields** to keep instance construction manageable
- **Callback-based dispatch** for extra constructors (not hard-coded names) — supports future logics
- **No changes to existing `DerivationTree` inductives** — only add new generic infrastructure and instances
- **FrameClass**: Parameterize generically; PL/Modal instances can ignore it

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Primary approach (typeclass design) | completed | high |
| B | Alternative approaches (prior art) | completed | high overall, medium on API surface |
| C | Critic (risks and blind spots) | completed | high |
| D | Strategic horizons | completed | high |

## References

- `Cslib/Foundations/Logic/Metalogic/Consistency.lean` — existing MCS abstraction
- `Cslib/Foundations/Logic/ProofSystem.lean` — existing typeclass hierarchy
- `Cslib/Foundations/Logic/Helpers/ListHelpers.lean` — shared list utilities
- [FormalizedFormalLogic/Foundation](https://github.com/FormalizedFormalLogic/Foundation) — Lean 4 multi-logic formalization
- [James Oswald: Extending Inductive Types in Lean4](https://jamesoswald.dev/posts/meditation-extending-inductive-types/)
- [LeanLTL: ITP 2025](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2025.37)
- [Lean 4 Inductive Types Reference](https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/)
