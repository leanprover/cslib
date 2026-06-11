/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Semantics.Kripke
public import Cslib.Logics.Propositional.Metalogic.MinSoundness
public import Cslib.Logics.Propositional.Metalogic.MinLindenbaum

/-! # Completeness Theorem for Minimal Propositional Logic

This module proves completeness for minimal propositional logic via the
canonical Kripke model construction with MinTheory (deductively closed sets)
as worlds.

## Main Results

- `MinCanonicalWorld`: Canonical world type (MinTheory for MinPropAxiom)
- `min_truth_lemma`: `IForces v bf S φ ↔ φ ∈ S.val` for canonical worlds
- `min_completeness`: `MValid φ → Derivable MinPropAxiom φ`
- `min_soundness_completeness`: `MValid φ ↔ Derivable MinPropAxiom φ`

## Key Differences from Intuitionistic Completeness

- Worlds are MinTheory (no consistency requirement) instead of IntDCCS
- `bot_forces w = (⊥ ∈ w.val)` is a genuine predicate, not trivially `False`
- Bot case of truth lemma is `Iff.rfl` (trivial) instead of multi-step reasoning
- MValid quantifies over arbitrary upward-closed `bot_forces`, not just `fun _ => False`

## References

* CZ Theorem 2.43
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic

universe u

variable {Atom : Type u}

/-! ## Canonical Model -/

/-- A canonical world for minimal logic is a MinTheory for MinPropAxiom. -/
def MinCanonicalWorld (Atom : Type*) :=
  { S : Set (PL.Proposition Atom) // MinTheory S }

/-- The canonical preorder on MinCanonicalWorld: set inclusion. -/
instance : Preorder (MinCanonicalWorld Atom) where
  le S T := S.val ⊆ T.val
  le_refl _ := Set.Subset.refl _
  le_trans _ _ _ h₁ h₂ := Set.Subset.trans h₁ h₂

/-- The canonical valuation: atom `p` is true at world `S` iff `atom p ∈ S`. -/
def min_canonical_val (w : MinCanonicalWorld Atom) (p : Atom) : Prop :=
  Proposition.atom p ∈ w.val

/-- The canonical valuation is upward-closed. -/
theorem min_canonical_val_upward_closed
    {w w' : MinCanonicalWorld Atom} (p : Atom)
    (hw : w ≤ w') (hv : min_canonical_val w p) : min_canonical_val w' p :=
  hw hv

/-- The canonical `bot_forces`: `⊥` is forced at world `S` iff `⊥ ∈ S`. -/
def min_bot_forces (w : MinCanonicalWorld Atom) : Prop :=
  Proposition.bot ∈ w.val

/-- `bot_forces` is upward-closed: if `⊥ ∈ S` and `S ⊆ T`, then `⊥ ∈ T`. -/
theorem min_bot_forces_upward_closed
    {w w' : MinCanonicalWorld Atom}
    (hw : w ≤ w') (hbf : min_bot_forces w) : min_bot_forces w' :=
  hw hbf

/-! ## Truth Lemma -/

/-- **Truth Lemma**: For any canonical world `S` and formula `φ`,
`IForces min_canonical_val min_bot_forces S φ ↔ φ ∈ S.val`.

Proof by structural induction on `φ` (3 cases: atom, bot, imp).
The bot case is `Iff.rfl` -- the key simplification vs intuitionistic. -/
theorem min_truth_lemma
    (S : MinCanonicalWorld Atom) :
    (φ : PL.Proposition Atom) →
    (IForces min_canonical_val min_bot_forces S φ ↔ φ ∈ S.val)
  | .atom p => Iff.rfl
  | .bot => Iff.rfl
  | .imp φ ψ => by
    constructor
    · -- Forward: IForces S (φ → ψ) → (φ → ψ) ∈ S.val
      intro h_forces
      by_contra h_not_mem
      obtain ⟨T_set, hST, hT_theory, hφT, hψT⟩ :=
        min_imp_witness S.property h_not_mem
      let T : MinCanonicalWorld Atom := ⟨T_set, hT_theory⟩
      have hle : S ≤ T := hST
      have hf_φ := (min_truth_lemma T φ).mpr hφT
      have hf_ψ := h_forces T hle hf_φ
      exact hψT ((min_truth_lemma T ψ).mp hf_ψ)
    · -- Backward: (φ → ψ) ∈ S.val → IForces S (φ → ψ)
      intro h_mem T hle hf_φ
      have h_imp_T : φ.imp ψ ∈ T.val := hle h_mem
      have h_φ_T : φ ∈ T.val := (min_truth_lemma T φ).mp hf_φ
      have h_ψ_T : ψ ∈ T.val := min_theory_imp_property T.property h_imp_T h_φ_T
      exact (min_truth_lemma T ψ).mpr h_ψ_T

/-! ## Completeness -/

/-- **Completeness Theorem for Minimal Propositional Logic**:

If `φ` is minimally valid (forced at every world of every minimal
Kripke model), then `φ` is derivable from the empty context using MinPropAxiom. -/
theorem min_completeness {φ : PL.Proposition Atom}
    (h_valid : MValid.{u, u} φ) : Derivable MinPropAxiom φ := by
  by_contra h_not_deriv
  have h_not_mem : φ ∉ {ψ : PL.Proposition Atom | Derivable MinPropAxiom ψ} :=
    h_not_deriv
  let W₀ : MinCanonicalWorld Atom :=
    ⟨{ψ | Derivable MinPropAxiom ψ}, min_theorems_theory⟩
  have h_not_forced : ¬ IForces min_canonical_val min_bot_forces W₀ φ := by
    intro h; exact h_not_mem ((min_truth_lemma W₀ φ).mp h)
  have h_forced : IForces min_canonical_val min_bot_forces W₀ φ :=
    h_valid (MinCanonicalWorld Atom) min_canonical_val min_bot_forces
      (fun {_ _} p hw hv => min_canonical_val_upward_closed p hw hv)
      (fun {_ _} hw hbf => min_bot_forces_upward_closed hw hbf)
      W₀
  exact h_not_forced h_forced

/-! ## Biconditional Wrapper -/

/-- **Soundness and Completeness**: `φ` is minimally valid iff `φ` is
derivable from the empty context using MinPropAxiom. -/
theorem min_soundness_completeness
    {φ : PL.Proposition Atom} :
    MValid.{u, u} φ ↔ Derivable MinPropAxiom φ :=
  ⟨min_completeness, min_soundness_derivable⟩

end Cslib.Logic.PL
