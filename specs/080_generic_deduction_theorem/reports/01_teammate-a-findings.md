# Teammate A Findings: Primary Approach — Typeclass Design for Generic Deduction Theorem

**Task**: 80 — Generic DeductionTheorem interface across all logic domains
**Date**: 2026-06-10
**Angle**: Primary implementation approach and typeclass design
**Confidence**: High

## Key Findings

### 1. Structure of the Duplication

All 4 DeductionTheorem files (952 total lines) follow an identical proof skeleton:

| Component | PL | Modal | Temporal | Bimodal |
|-----------|----|----|----------|---------|
| `deduction_axiom` | ✓ | ✓ | ✓ | ✓ |
| `deduction_imp_self` | ✓ | ✓ | ✓ | ✓ (as `deduction_assumption_same`) |
| `deduction_assumption_other` | ✓ | ✓ | ✓ | ✓ |
| `deduction_mp` | ✓ | ✓ | ✓ | ✓ |
| `deduction_with_mem` | ✓ | ✓ | ✓ | ✓ |
| `deduction_theorem` | ✓ | ✓ | ✓ | ✓ |
| `*_has_deduction_theorem` | ✓ | ✓ | ✓ | ✓ |

The only difference is **extra constructors** that all get discharged by `simp at hA` because they require empty context:

| Logic | Extra Constructors (empty-context-only) |
|-------|-----------------------------------------|
| Propositional | (none) |
| Modal | `necessitation` |
| Temporal | `temporal_necessitation`, `temporal_duality` |
| Bimodal | `necessitation`, `temporal_necessitation`, `temporal_duality` |

### 2. Type-Level Differences

| Aspect | PL | Modal | Temporal | Bimodal |
|--------|-----|-------|----------|---------|
| Formula type | `PL.Proposition Atom` | `Proposition Atom` | `Formula Atom` | `Formula Atom` |
| Context type | `List (PL.Proposition Atom)` | `List (Proposition Atom)` | `Context Atom` (= `List (Formula Atom)`) | `Context Atom` (= `List (Formula Atom)`) |
| DerivationTree params | `Γ → φ → Type` | `Γ → φ → Type` | `fc → Γ → φ → Type` | `fc → Γ → φ → Type` |
| Has FrameClass? | No | No | Yes | Yes |
| Axiom type | `PropositionalAxiom` | `ModalAxiom` | `Axiom` | `Axiom` |
| `ax` constructor | `.ax Γ φ h_ax` | `.ax Γ φ h_ax` | `.axiom Γ φ h_ax h_fc` | `.axiom Γ φ h_ax h_fc` |
| implyK axiom name | `.implyK φ A` | `.implyK φ A` | `.imp_s φ A` | `Axiom.imp_s φ A` |
| implyS axiom name | `.implyS A C D` | `.implyS A C D` | `.imp_k A C D` | `Axiom.imp_k A C D` |
| Empty subset proof | `fun _ h => nomatch h` | `fun _ h => nomatch h` | `List.nil_subset _` | `List.nil_subset _` |

**Critical observation**: The Temporal/Bimodal axiom naming swaps K and S relative to PL/Modal. `imp_s` in Temporal = what PL calls `implyK` (i.e., φ → ψ → φ). `imp_k` in Temporal = what PL calls `implyS` (i.e., the distribution axiom). This is a naming discrepancy only — the axiom *content* is the same.

### 3. The Core Insight for Abstraction

The deduction theorem proof only needs 5 capabilities from a derivation tree:

1. **Construct from axiom**: Given an axiom witness, build a derivation in empty context
2. **Construct from assumption**: Given membership proof, build a derivation
3. **Construct modus ponens**: Combine two derivations  
4. **Construct weakening**: Lift a derivation to a larger context
5. **Eliminate/case-split**: Pattern match on a derivation, handling all constructor cases. The common cases (ax, assumption, mp, weakening) are handled identically; any extra cases are discharged by contradiction on the context being non-empty.

Additionally, the proof needs a **height measure** with ordering lemmas, and the ability to build axiom derivations for `implyK` and `implyS`.

## Recommended Approach

### Design: Prop-Level Abstraction (Not Type-Level)

**Key decision**: Do NOT try to abstract over the inductive `DerivationTree` types themselves. Instead, work at the `Prop`-level (`Deriv : List F → F → Prop`) where all 4 logics already converge.

**Rationale**: 
- Pattern matching on a foreign inductive type through a typeclass is not directly possible in Lean 4 — you cannot abstract over constructors of different inductives.
- The `deduction_theorem` proof uses `match` on specific constructors, which is inherently tied to the concrete inductive type.
- Each logic already provides a `Deriv` wrapper (`Nonempty (DerivationTree ...)`), and these all satisfy the same `DerivationSystem` interface from `Consistency.lean`.
- The existing `DerivationSystem` structure in `Consistency.lean` already abstracts over `Deriv`, `weakening`, `assumption`, and `mp`.

**Therefore**: The deduction theorem proof must remain at the concrete `DerivationTree` level in each logic. What CAN be shared are the **helper lemmas** (`deduction_axiom`, `deduction_imp_self`, `deduction_assumption_other`, `deduction_mp`) which all work via `Deriv`-level combinators.

### Alternative: Type-Level Elimination Typeclass

If we still want to share the `deduction_with_mem` and `deduction_theorem` proofs, we need a typeclass that provides a **custom elimination principle**:

```lean
class HasDeductionElim (F : Type*) [DecidableEq F] [HasBot F] [HasImp F] where
  /-- The derivation tree type. -/
  Tree : List F → F → Type*
  /-- Height measure for termination. -/
  height : Tree Γ φ → Nat
  /-- Build axiom derivation in empty context, then weaken. -/
  ax_deriv : (Γ : List F) → (φ : F) → Tree [] φ → Tree Γ φ
  /-- Build assumption derivation. -/
  assumption : (Γ : List F) → (φ : F) → φ ∈ Γ → Tree Γ φ
  /-- Build modus ponens. -/
  modus_ponens : (Γ : List F) → (φ ψ : F) → Tree Γ (HasImp.imp φ ψ) → Tree Γ φ → Tree Γ ψ
  /-- Build weakening. -/
  weakening : (Γ Δ : List F) → (φ : F) → Tree Γ φ → (∀ x ∈ Γ, x ∈ Δ) → Tree Δ φ
  /-- Build implyK axiom derivation (φ → ψ → φ) in empty context. -/
  implyK_ax : (φ ψ : F) → Tree [] (HasImp.imp φ (HasImp.imp ψ φ))
  /-- Build implyS axiom derivation ((φ→ψ→χ)→(φ→ψ)→(φ→χ)) in empty context. -/
  implyS_ax : (φ ψ χ : F) → Tree [] (HasImp.imp (HasImp.imp φ (HasImp.imp ψ χ)) 
    (HasImp.imp (HasImp.imp φ ψ) (HasImp.imp φ χ)))
  /-- Case analysis: either the tree matches a common constructor, or the context is empty. -/
  cases_on : {Γ : List F} → {φ : F} → (d : Tree Γ φ) →
    -- Axiom case
    (∀ ψ, Tree [] ψ → ψ = φ → Tree Γ φ → Prop) →  -- too complex...
```

**This approach quickly becomes unwieldy.** The elimination principle needs to provide access to:
- The specific constructor
- Subderivations with their contexts
- Height decrease proofs

This is essentially re-stating the entire recursor of the inductive type, which defeats the purpose.

### Recommended Hybrid Approach

The most practical design is a **two-layer** approach:

#### Layer 1: Shared Helper Lemmas (in `Foundations/Logic/`)

Extract the 4 helper lemmas that build derivation trees from axioms. These are purely constructive and don't require pattern matching:

```lean
-- In Cslib/Foundations/Logic/DeductionHelpers.lean

namespace Cslib.Logic.DeductionHelpers

variable {F : Type*} [DecidableEq F] [HasBot F] [HasImp F]

/-- Abstract derivation tree interface for building proofs. -/
class HasHilbertTree (F : Type*) [HasBot F] [HasImp F] where
  /-- The derivation tree type, parameterized by context and formula. -/
  Tree : List F → F → Type*
  /-- Empty-context axiom derivation for implyK: φ → (ψ → φ). -/
  implyK : (φ ψ : F) → Tree [] (HasImp.imp φ (HasImp.imp ψ φ))
  /-- Empty-context axiom derivation for implyS:
      (φ → ψ → χ) → (φ → ψ) → (φ → χ). -/
  implyS : (φ ψ χ : F) → Tree [] (HasImp.imp 
    (HasImp.imp φ (HasImp.imp ψ χ))
    (HasImp.imp (HasImp.imp φ ψ) (HasImp.imp φ χ)))
  /-- Assumption rule. -/
  assumption : (Γ : List F) → (φ : F) → φ ∈ Γ → Tree Γ φ  
  /-- Modus ponens. -/
  mp : (Γ : List F) → (φ ψ : F) → Tree Γ (HasImp.imp φ ψ) → Tree Γ φ → Tree Γ ψ
  /-- Weakening. -/
  weakening : (Γ Δ : List F) → (φ : F) → Tree Γ φ → (∀ x ∈ Γ, x ∈ Δ) → Tree Δ φ

variable [HasHilbertTree F]

/-- Generic: If φ is derivable in empty context, then Γ ⊢ A → φ. -/
noncomputable def deduction_axiom (Γ : List F) (A : F)
    (d_empty : HasHilbertTree.Tree (F := F) [] φ) :
    HasHilbertTree.Tree Γ (HasImp.imp A φ) := by
  have k := HasHilbertTree.implyK φ A
  have step := HasHilbertTree.mp [] φ (HasImp.imp A φ) k d_empty
  exact HasHilbertTree.weakening [] Γ _ step (fun _ h => nomatch h)
  -- Note: `nomatch h` only works when `[]` is empty; 
  -- alternatively use `(List.nil_subset _)` if needed

/-- Generic: Γ ⊢ A → A. -/
noncomputable def deduction_imp_self (Γ : List F) (A : F) :
    HasHilbertTree.Tree (F := F) Γ (HasImp.imp A A) := by
  let s := HasHilbertTree.implyS A (HasImp.imp A A) A
  let k1 := HasHilbertTree.implyK A (HasImp.imp A A)
  let k2 := HasHilbertTree.implyK A A
  let step1 := HasHilbertTree.mp [] _ _ s k1
  let result := HasHilbertTree.mp [] _ _ step1 k2
  exact HasHilbertTree.weakening [] Γ _ result (fun _ h => nomatch h)

/-- Generic: If B ∈ Γ, then Γ ⊢ A → B. -/
noncomputable def deduction_assumption_other (Γ : List F) (A B : F) 
    (h_mem : B ∈ Γ) :
    HasHilbertTree.Tree (F := F) Γ (HasImp.imp A B) := by
  have b_deriv := HasHilbertTree.assumption Γ B h_mem
  have k := HasHilbertTree.implyK B A
  have k_weak := HasHilbertTree.weakening [] Γ _ k (fun _ h => nomatch h)
  exact HasHilbertTree.mp Γ B (HasImp.imp A B) k_weak b_deriv

/-- Generic: From Γ ⊢ A → (C → D) and Γ ⊢ A → C, derive Γ ⊢ A → D. -/
noncomputable def deduction_mp (Γ : List F) (A C D : F)
    (h₁ : HasHilbertTree.Tree (F := F) Γ (HasImp.imp A (HasImp.imp C D)))
    (h₂ : HasHilbertTree.Tree (F := F) Γ (HasImp.imp A C)) :
    HasHilbertTree.Tree Γ (HasImp.imp A D) := by
  have s := HasHilbertTree.implyS A C D
  have s_weak := HasHilbertTree.weakening [] Γ _ s (fun _ h => nomatch h)
  have step1 := HasHilbertTree.mp Γ _ _ s_weak h₁
  exact HasHilbertTree.mp Γ _ _ step1 h₂

end Cslib.Logic.DeductionHelpers
```

#### Layer 2: Per-Logic Thin Wrapper

Each logic provides a `HasHilbertTree` instance and a thin deduction theorem that uses:
1. Generic helpers for the 4 common cases
2. `simp at hA` for the extra empty-context constructors

```lean
-- Example for Modal logic (shortened)
instance : HasHilbertTree (Proposition Atom) where
  Tree := DerivationTree
  implyK := fun φ ψ => .ax [] _ (.implyK φ ψ)
  implyS := fun φ ψ χ => .ax [] _ (.implyS φ ψ χ)
  assumption := DerivationTree.assumption
  mp := DerivationTree.modus_ponens
  weakening := DerivationTree.weakening

noncomputable def deduction_with_mem (...) := by
  match d with
  | .ax _ ψ h_ax =>
    exact DeductionHelpers.deduction_axiom (removeAll Γ' A) A (.ax [] ψ h_ax)
  | .assumption _ ψ h_mem =>
    by_cases h_eq : ψ = A
    · subst h_eq; exact DeductionHelpers.deduction_imp_self _ ψ
    · exact DeductionHelpers.deduction_assumption_other _ A ψ (mem_removeAll_of_mem_of_ne h_mem h_eq)
  | .modus_ponens _ ψ χ d₁ d₂ =>
    exact DeductionHelpers.deduction_mp _ A ψ χ 
      (deduction_with_mem Γ' A (ψ.imp χ) d₁ hA)
      (deduction_with_mem Γ' A ψ d₂ hA)
  | .necessitation ψ _d' => simp at hA
  | .weakening Γ'' _ ψ d' h_sub => ... -- uses generic helpers
```

### Code Reduction Estimate

| Component | Current (total) | Generic | Per-logic instance | Net savings |
|-----------|----------------|---------|-------------------|-------------|
| `deduction_axiom` | 4 × ~8 lines = 32 | ~8 lines | 0 (use generic) | ~24 lines |
| `deduction_imp_self` | 4 × ~8 lines = 32 | ~8 lines | 0 (use generic) | ~24 lines |
| `deduction_assumption_other` | 4 × ~6 lines = 24 | ~6 lines | 0 (use generic) | ~18 lines |
| `deduction_mp` | 4 × ~8 lines = 32 | ~8 lines | 0 (use generic) | ~24 lines |
| `HasHilbertTree` class | 0 | ~25 lines | 4 × ~10 lines = 40 | -65 lines |
| `deduction_with_mem` | 4 × ~35 lines = 140 | 0 | 4 × ~25 lines = 100 | ~40 lines |
| `deduction_theorem` | 4 × ~40 lines = 160 | 0 | 4 × ~30 lines = 120 | ~40 lines |
| `*_has_deduction_theorem` | 4 × ~6 lines = 24 | 0 | 4 × ~6 lines = 24 | 0 |
| **Total** | **~444 lines** | **~55 lines** | **~284 lines** | **~105 lines saved** |

**Savings**: ~105 lines (24% reduction), plus the significant maintenance benefit of having the helper logic in one place.

### Why Not Full Generic `deduction_with_mem` and `deduction_theorem`?

The main `deduction_with_mem` and `deduction_theorem` functions **cannot** be fully generic because:

1. **Pattern matching**: They `match` on the concrete inductive constructors. Lean 4 typeclasses cannot provide custom eliminators that support `match` syntax with `termination_by`.
2. **Well-founded recursion**: The `termination_by d.height` and `decreasing_by` blocks reference concrete height lemmas tied to specific constructors.
3. **Extra constructors**: Each logic has different numbers of extra constructors (0/1/2/3). While they're all discharged identically (`simp at hA`), the match exhaustiveness checker needs all constructors present.

A theoretical alternative would be to define a **generic elimination principle** as a typeclass field, but this would essentially duplicate the recursor with all its complexity, and the resulting proof would be harder to read and maintain than the current 4 thin copies.

## Alternative Approaches Considered

### Approach B: Prop-Level Only (via `DerivationSystem`)

Prove the deduction theorem generically at the `DerivationSystem` level using only `Deriv`, `weakening`, `assumption`, and `mp`. This would require adding `implyK` and `implyS` derivability fields to `DerivationSystem`.

**Problem**: The current proof uses well-founded recursion on `height`, which requires the `Type`-level `DerivationTree`. At the `Prop`-level (`Nonempty (DerivationTree ...)`), you can't extract and recurse on the tree. The deduction theorem is **not provable** from just the `DerivationSystem` interface — it requires structural induction on the tree.

### Approach C: Macro/Metaprogramming

Use Lean 4 metaprogramming to generate the deduction theorem proof for each logic from a template.

**Problem**: Over-engineering for 4 instances. The maintenance burden of a macro is worse than the duplication it eliminates.

### Approach D: Single Universal DerivationTree

Define one polymorphic `DerivationTree` parameterized by the set of extra constructors.

**Problem**: This would require refactoring all 4 logic domains to use a shared inductive type, which contradicts the project's architecture where each logic defines its own self-contained types. Also very invasive.

## Verdict

**Recommended**: Layer 1 + Layer 2 hybrid approach (shared `HasHilbertTree` typeclass with 4 generic helper lemmas, thin per-logic deduction theorem wrappers).

**Confidence**: High. The helper lemma extraction is straightforward and safe. The per-logic thin wrappers are mechanically derivable from the current code. The typeclass instance for each logic maps directly to its existing constructors.

**Risk**: The `fun _ h => nomatch h` pattern for empty-list subset proof may need adjustment depending on how Lean 4 handles this in the generic context (might need `List.nil_subset _` or `fun _ h => absurd h (List.not_mem_nil _)` instead). This is a minor implementation detail.

## References

- `Cslib/Foundations/Logic/Metalogic/Consistency.lean` — existing `DerivationSystem` abstraction
- `Cslib/Foundations/Logic/Helpers/ListHelpers.lean` — already-shared `removeAll` infrastructure
- `Cslib/Foundations/Logic/Connectives.lean` — `HasBot`, `HasImp` typeclasses
- `Cslib/Foundations/Logic/ProofSystem.lean` — `PropositionalHilbert` etc. bundled classes
- [Lean 4 Inductive Types Reference](https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/)
- [Lean 4 Recursive Definitions](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/)
- [Lean 4.29.0 Release Notes](https://lean-lang.org/doc/reference/latest/releases/v4.29.0/)
