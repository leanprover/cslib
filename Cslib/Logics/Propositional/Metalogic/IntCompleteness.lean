/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Semantics.Kripke
public import Cslib.Logics.Propositional.Metalogic.IntSoundness
public import Cslib.Logics.Propositional.Metalogic.IntLindenbaum

/-! # Completeness Theorem for Intuitionistic Propositional Logic

This module proves completeness for intuitionistic propositional logic via the
canonical Kripke model construction with DCCS (deductively closed consistent sets)
as worlds.

## Main Results

- `IntCanonicalWorld`: Canonical world type (DCCS for IntPropAxiom)
- `int_truth_lemma`: `IForces v bf S φ ↔ φ ∈ S.val` for canonical worlds
- `int_completeness`: `IValid φ → Derivable IntPropAxiom φ`
- `int_soundness_completeness`: `IValid φ ↔ Derivable IntPropAxiom φ`

## References

* CZ Theorem 2.43
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic

universe u

variable {Atom : Type u}

/-! ## Canonical Model -/

/-- A canonical world for intuitionistic logic is a DCCS for IntPropAxiom. -/
def IntCanonicalWorld (Atom : Type*) :=
  { S : Set (PL.Proposition Atom) // IntDCCS S }

/-- The canonical preorder on IntCanonicalWorld: set inclusion. -/
instance : Preorder (IntCanonicalWorld Atom) where
  le S T := S.val ⊆ T.val
  le_refl _ := Set.Subset.refl _
  le_trans _ _ _ h₁ h₂ := Set.Subset.trans h₁ h₂

/-- The canonical valuation: atom `p` is true at world `S` iff `atom p ∈ S`. -/
def intCanonicalVal (w : IntCanonicalWorld Atom) (p : Atom) : Prop :=
  Proposition.atom p ∈ w.val

/-- The canonical valuation is upward-closed. -/
theorem intCanonicalVal_upward_closed
    {w w' : IntCanonicalWorld Atom} (p : Atom)
    (hw : w ≤ w') (hv : intCanonicalVal w p) : intCanonicalVal w' p :=
  hw hv

/-! ## Truth Lemma -/

/-- **Truth Lemma**: For any canonical world `S` and formula `φ`,
`IForces intCanonicalVal (fun _ => False) S φ ↔ φ ∈ S.val`.

Proof by structural induction on `φ` (3 cases: atom, bot, imp). -/
theorem int_truth_lemma
    (S : IntCanonicalWorld Atom) :
    (φ : PL.Proposition Atom) →
    (IForces intCanonicalVal (fun _ => False) S φ ↔ φ ∈ S.val)
  | .atom p => Iff.rfl
  | .bot => by
    constructor
    · intro h; exact absurd h id
    · intro h; exact absurd h (int_dccs_bot_not_mem S.property)
  | .imp φ ψ => by
    constructor
    · -- Forward: IForces S (φ → ψ) → (φ → ψ) ∈ S.val
      intro h_forces
      by_contra h_not_mem
      obtain ⟨T_set, hST, hT_dccs, hφT, hψT⟩ :=
        int_imp_witness S.property h_not_mem
      let T : IntCanonicalWorld Atom := ⟨T_set, hT_dccs⟩
      have hle : S ≤ T := hST
      have hf_φ := (int_truth_lemma T φ).mpr hφT
      have hf_ψ := h_forces T hle hf_φ
      exact hψT ((int_truth_lemma T ψ).mp hf_ψ)
    · -- Backward: (φ → ψ) ∈ S.val → IForces S (φ → ψ)
      intro h_mem T hle hf_φ
      have h_imp_T : (φ → ψ) ∈ T.val := hle h_mem
      have h_φ_T : φ ∈ T.val := (int_truth_lemma T φ).mp hf_φ
      have h_ψ_T : ψ ∈ T.val := int_dccs_imp_property T.property h_imp_T h_φ_T
      exact (int_truth_lemma T ψ).mpr h_ψ_T

/-! ## Completeness -/

/-- **Completeness Theorem for Intuitionistic Propositional Logic**:

If `φ` is intuitionistically valid (forced at every world of every intuitionistic
Kripke model), then `φ` is derivable from the empty context using IntPropAxiom. -/
theorem int_completeness {φ : PL.Proposition Atom}
    (h_valid : IValid.{u, u} φ) : Derivable IntPropAxiom φ := by
  by_contra h_not_deriv
  have h_dccs := @int_theorems_dccs Atom
  have h_not_mem : φ ∉ {ψ : PL.Proposition Atom | Derivable IntPropAxiom ψ} :=
    h_not_deriv
  let W₀ : IntCanonicalWorld Atom :=
    ⟨{ψ | Derivable IntPropAxiom ψ}, h_dccs⟩
  have h_not_forced : ¬ IForces intCanonicalVal (fun _ => False) W₀ φ := by
    intro h; exact h_not_mem ((int_truth_lemma W₀ φ).mp h)
  have h_forced : IForces intCanonicalVal (fun _ => False) W₀ φ :=
    h_valid (IntCanonicalWorld Atom) intCanonicalVal
      (fun {_ _} p hw hv => intCanonicalVal_upward_closed p hw hv) W₀
  exact h_not_forced h_forced

/-! ## Biconditional Wrapper -/

/-- **Soundness and Completeness**: `φ` is intuitionistically valid iff `φ` is
derivable from the empty context using IntPropAxiom. -/
theorem int_soundness_completeness
    {φ : PL.Proposition Atom} :
    IValid.{u, u} φ ↔ Derivable IntPropAxiom φ :=
  ⟨int_completeness, int_soundness_derivable⟩

end Cslib.Logic.PL
