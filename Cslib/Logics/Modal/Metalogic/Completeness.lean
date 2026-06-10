/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import Cslib.Logics.Modal.Metalogic.MCS
import Cslib.Logics.Modal.Metalogic.Soundness

/-! # Completeness Theorem for S5 Modal Logic

This module proves completeness for S5 modal logic via the canonical Kripke model
construction: every formula valid over all S5 frames is derivable.

## Main Results

- `CanonicalWorld`: The type of worlds in the canonical model (MCS).
- `CanonicalModel`: The canonical Kripke model with accessibility and valuation.
- `canonical_refl`, `canonical_trans`, `canonical_eucl`: The canonical model is an S5 frame.
- `truth_lemma`: `Satisfies (CanonicalModel) S φ ↔ φ ∈ S.val` (by structural induction on φ).
- `completeness`: If `φ` is valid over all S5 frames, then `φ` is derivable.

## Design

The canonical model has:
- **Worlds**: Maximally consistent sets (MCS) of the modal derivation system.
- **Accessibility**: `R S T ↔ ∀ ψ, □ψ ∈ S → ψ ∈ T` (the standard canonical relation).
- **Valuation**: `v S p ↔ atom p ∈ S`.

For S5, this relation is reflexive (by axiom T / box_closure), transitive
(by axiom 4 / box_box), and Euclidean (by axiom B + T + 4).

## References

* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Canonical Models)
-/

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

/-! ## Canonical Model Definition -/

/-- A canonical world is a maximally consistent set of the modal derivation system. -/
def CanonicalWorld (Atom : Type*) :=
  { S : Set (Proposition Atom) // Modal.SetMaximalConsistent S }

/-- The canonical model for S5 modal logic.

- Accessibility: `R S T ↔ ∀ ψ, □ψ ∈ S → ψ ∈ T`.
- Valuation: `v S p ↔ atom p ∈ S`. -/
noncomputable def CanonicalModel (Atom : Type*) : Model (CanonicalWorld Atom) Atom where
  r := fun S T => ∀ φ, Proposition.box φ ∈ S.val → φ ∈ T.val
  v := fun S p => Proposition.atom p ∈ S.val

/-! ## Canonical Frame Properties -/

/-- The canonical accessibility relation is reflexive (from axiom T). -/
theorem canonical_refl (S : CanonicalWorld Atom) :
    (CanonicalModel Atom).r S S := by
  intro φ h_box
  exact mcs_box_closure S.property h_box

/-- The canonical accessibility relation is transitive (from axiom 4). -/
theorem canonical_trans (S T U : CanonicalWorld Atom) :
    (CanonicalModel Atom).r S T → (CanonicalModel Atom).r T U →
    (CanonicalModel Atom).r S U := by
  intro hST hTU φ h_box
  -- □φ ∈ S → □□φ ∈ S (by axiom 4)
  have h_box_box := mcs_box_box S.property h_box
  -- □□φ ∈ S → □φ ∈ T (by hST)
  have h_box_T := hST (Proposition.box φ) h_box_box
  -- □φ ∈ T → φ ∈ U (by hTU)
  exact hTU φ h_box_T

/-- The canonical accessibility relation is Euclidean (from axioms B, T, 4).

Given R S T and R S U and □φ ∈ T, we need φ ∈ U. The proof proceeds by
contradiction: suppose □φ ∉ S. Then ¬□φ ∈ S. By B: □◇(¬□φ) ∈ S.
Since R S T: ◇(¬□φ) ∈ T. So □(¬(¬□φ)) ∉ T.
But □□φ ∈ T (from axiom 4 applied to h_box_T via box_box).
By DNI (double negation intro) and K: □(¬(¬□φ)) ∈ T. Contradiction.
So □φ ∈ S, and since R S U: φ ∈ U. -/
theorem canonical_eucl (S T U : CanonicalWorld Atom) :
    (CanonicalModel Atom).r S T → (CanonicalModel Atom).r S U →
    (CanonicalModel Atom).r T U := by
  intro hST hSU φ h_box_T
  -- □□φ ∈ T from axiom 4
  have h_bb_T := mcs_box_box T.property h_box_T
  -- Show □φ ∈ S by contradiction
  by_contra h_phi_not_U
  apply h_phi_not_U
  -- φ ∈ U follows from □φ ∈ S and R S U
  apply hSU
  -- Need □φ ∈ S. Suppose not.
  by_contra h_box_not_S
  -- ¬□φ ∈ S
  have h_neg_box := mcs_neg_of_not_mem S.property h_box_not_S
  -- B: ¬□φ → □◇(¬□φ). So □◇(¬□φ) ∈ S.
  have h_bd := mcs_box_diamond S.property h_neg_box
  -- R S T: ◇(¬□φ) ∈ T
  have h_diam_T := hST _ h_bd
  -- ◇(¬□φ) ∈ T means □(¬(¬□φ)) ∉ T
  have h_box_dne_not_T : Proposition.box (Proposition.neg (Proposition.neg (Proposition.box φ))) ∉ T.val :=
    mcs_not_mem_of_neg T.property h_diam_T
  -- Build ⊢ □φ → ¬¬□φ (DNI for □φ) via deduction theorem
  let bp := Proposition.box φ
  have d_bot : DerivationTree [bp.imp .bot, bp] Proposition.bot :=
    .modus_ponens [bp.imp .bot, bp] bp .bot
      (.assumption _ (bp.imp .bot) (by simp [List.mem_cons]))
      (.assumption _ bp (by simp [List.mem_cons]))
  have d_dne := deduction_theorem [bp] (bp.imp .bot) .bot d_bot
  have d_dni := deduction_theorem [] bp ((bp.imp .bot).imp .bot) d_dne
  -- Necessitation: ⊢ □(□φ → ¬¬□φ)
  have d_nec := DerivationTree.necessitation _ d_dni
  -- □(□φ → ¬¬□φ) ∈ T via closed_under_derivation
  have h_box_dni_T : Proposition.box (bp.imp ((bp.imp .bot).imp .bot)) ∈ T.val :=
    modal_closed_under_derivation T.property (L := []) (fun _ h => nomatch h) ⟨d_nec⟩
  -- By K: □□φ ∈ T → □¬¬□φ ∈ T. Use h_bb_T for □□φ.
  have h_box_dne_T := mcs_box_mp T.property h_box_dni_T h_bb_T
  -- □¬¬□φ = □(¬(¬□φ)) definitionally. Contradiction with h_box_dne_not_T.
  exact h_box_dne_not_T h_box_dne_T

/-! ## Truth Lemma -/

/-- **Truth Lemma**: For any canonical world `S` and formula `φ`,
`Satisfies (CanonicalModel Atom) S φ ↔ φ ∈ S.val`.

Proved by structural induction on `φ`:
- `atom p`: By definition of canonical valuation.
- `bot`: `False ↔ ⊥ ∈ S.val` (⊥ is never in an MCS).
- `imp φ ψ`: From the implication property and negation completeness.
- `box φ`: Forward from canonical accessibility; reverse from box_witness. -/
theorem truth_lemma (S : CanonicalWorld Atom) :
    (φ : Proposition Atom) → (Satisfies (CanonicalModel Atom) S φ ↔ φ ∈ S.val)
  | .atom p => by
    -- By definition: Satisfies ... S (atom p) = CanonicalModel.v S p = (atom p) ∈ S.val
    constructor
    · intro h; exact h
    · intro h; exact h
  | .bot => by
    constructor
    · intro h; exact absurd h id
    · intro h; exact absurd h (mcs_bot_not_mem S.property)
  | .imp φ ψ => by
    constructor
    · -- Forward: Satisfies m S (φ → ψ) → (φ → ψ) ∈ S
      intro h_sat
      -- h_sat : Satisfies m S φ → Satisfies m S ψ
      -- By negation completeness: either (φ → ψ) ∈ S or ¬(φ → ψ) ∈ S.
      rcases modal_negation_complete S.property (φ.imp ψ) with h | h
      · exact h
      · -- ¬(φ → ψ) ∈ S. Derive contradiction:
        -- From (φ→ψ)→⊥ ∈ S, derive φ ∈ S (via Peirce + EFQ),
        -- then ψ ∈ S (via h_sat), then ¬ψ ∈ S (from (φ→ψ)→⊥ via implyK). Contradiction.
        exfalso
        have h_phi_S : φ ∈ S.val := by
          apply modal_closed_under_derivation S.property (L := [(φ.imp ψ).imp .bot])
            (fun x hx => by simp [List.mem_cons] at hx; exact hx ▸ h)
          unfold modalDerivationSystem Deriv
          -- Build [φ→ψ, (φ→ψ)→⊥] ⊢ φ via EFQ, then DT + Peirce
          have d_bot' : DerivationTree [φ.imp ψ, (φ.imp ψ).imp .bot] Proposition.bot :=
            .modus_ponens _ (φ.imp ψ) .bot
              (.assumption _ _ (by simp [List.mem_cons]))
              (.assumption _ _ (by simp [List.mem_cons]))
          have d_efq : DerivationTree [φ.imp ψ, (φ.imp ψ).imp .bot] φ :=
            .modus_ponens _ .bot φ
              (.weakening [] _ _ (.ax [] _ (.efq φ)) (fun _ h => nomatch h))
              d_bot'
          have d_dt := deduction_theorem [(φ.imp ψ).imp .bot] (φ.imp ψ) φ d_efq
          have d_peirce : DerivationTree [(φ.imp ψ).imp .bot] (((φ.imp ψ).imp φ).imp φ) :=
            .weakening [] _ _ (.ax [] _ (.peirce φ ψ)) (fun _ h => nomatch h)
          exact ⟨.modus_ponens _ _ _ d_peirce d_dt⟩
        have h_sat_phi := (truth_lemma S φ).mpr h_phi_S
        have h_psi_S := (truth_lemma S ψ).mp (h_sat h_sat_phi)
        have h_neg_psi_S : Proposition.neg ψ ∈ S.val := by
          apply modal_closed_under_derivation S.property (L := [(φ.imp ψ).imp .bot])
            (fun x hx => by simp [List.mem_cons] at hx; exact hx ▸ h)
          unfold modalDerivationSystem Deriv
          -- Build [(φ→ψ)→⊥] ⊢ ψ→⊥ via implyK
          have d_imp : DerivationTree [ψ, (φ.imp ψ).imp .bot] (φ.imp ψ) :=
            .modus_ponens _ ψ (φ.imp ψ)
              (.weakening [] _ _ (.ax [] _ (.implyK ψ φ)) (fun _ h => nomatch h))
              (.assumption _ _ (by simp [List.mem_cons]))
          have d_bot'' : DerivationTree [ψ, (φ.imp ψ).imp .bot] Proposition.bot :=
            .modus_ponens _ (φ.imp ψ) .bot
              (.assumption _ _ (by simp [List.mem_cons]))
              d_imp
          exact ⟨deduction_theorem [(φ.imp ψ).imp .bot] ψ .bot d_bot''⟩
        exact mcs_bot_not_mem S.property (modal_implication_property S.property h_neg_psi_S h_psi_S)
    · intro h_mem h_sat_phi
      exact (truth_lemma S ψ).mpr (modal_implication_property S.property h_mem
        ((truth_lemma S φ).mp h_sat_phi))
  | .box φ => by
    constructor
    · intro h_sat
      by_contra h_not_box
      obtain ⟨T, hT_mcs, hST, h_phi_not_T⟩ := mcs_box_witness S.property h_not_box
      exact h_phi_not_T ((truth_lemma ⟨T, hT_mcs⟩ φ).mp (h_sat ⟨T, hT_mcs⟩ hST))
    · intro h_box T hST
      exact (truth_lemma T φ).mpr (hST φ h_box)

/-! ## Completeness Theorem -/

/-- **Completeness Theorem for S5 Modal Logic**:

If `φ` is valid over all S5 frames (reflexive, transitive, Euclidean), then `φ`
is derivable from the empty context.

**Proof**: By contrapositive. If `φ` is not derivable, then `{¬φ}` is consistent
(otherwise we could derive `φ`). By Lindenbaum's lemma, `{¬φ}` extends to an MCS `M`.
The canonical model is an S5 frame (reflexive, transitive, Euclidean). By the truth
lemma, `M` does not satisfy `φ` (since `¬φ ∈ M`). This contradicts validity. -/
theorem completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      (∀ w, m.r w w) →
      (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
      (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
      ∀ w, Satisfies m w φ) :
    Derivable φ := by
  -- Contrapositive: suppose φ is not derivable
  by_contra h_not_deriv
  -- {¬φ} is consistent
  have h_cons : Modal.SetConsistent ({Proposition.neg φ} : Set (Proposition Atom)) := by
    intro L hL
    unfold Metalogic.Consistent
    intro ⟨d⟩
    -- Weaken d to [¬φ] (all elements of L are ¬φ by hL), then DT gives ⊢ (φ→⊥)→⊥,
    -- and Peirce + EFQ derives ⊢ φ, contradicting h_not_deriv.
    have d_weak : DerivationTree [Proposition.neg φ] Proposition.bot :=
      .weakening L [Proposition.neg φ] .bot d (fun x hx => by
        have := hL x hx; simp at this; exact List.mem_cons.mpr (Or.inl this))
    have d_dne := deduction_theorem [] (Proposition.neg φ) .bot d_weak
    let neg_phi := Proposition.neg φ
    have efq : DerivationTree (Atom := Atom) [] (Proposition.bot.imp φ) :=
      .ax [] _ (.efq φ)
    have ik : DerivationTree (Atom := Atom) [] ((Proposition.bot.imp φ).imp (neg_phi.imp (Proposition.bot.imp φ))) :=
      .ax [] _ (.implyK (Proposition.bot.imp φ) neg_phi)
    have step_k := DerivationTree.modus_ponens [] _ _ ik efq
    have is_ax : DerivationTree (Atom := Atom) []
        ((neg_phi.imp (Proposition.bot.imp φ)).imp
         ((neg_phi.imp Proposition.bot).imp (neg_phi.imp φ))) :=
      .ax [] _ (.implyS neg_phi Proposition.bot φ)
    have step_s := DerivationTree.modus_ponens [] _ _ is_ax step_k
    have step3 := DerivationTree.modus_ponens [] _ _ step_s d_dne
    have peirce_ax : DerivationTree (Atom := Atom) [] (((φ.imp Proposition.bot).imp φ).imp φ) :=
      .ax [] _ (.peirce φ Proposition.bot)
    have d_phi := DerivationTree.modus_ponens [] _ _ peirce_ax step3
    exact h_not_deriv ⟨d_phi⟩
  obtain ⟨M, hM_sup, hM_mcs⟩ := modal_lindenbaum h_cons
  let w : CanonicalWorld Atom := ⟨M, hM_mcs⟩
  exact mcs_not_mem_of_neg hM_mcs (hM_sup (Set.mem_singleton _))
    ((truth_lemma w φ).mp (h_valid (CanonicalWorld Atom) (CanonicalModel Atom)
      canonical_refl canonical_trans canonical_eucl w))

end Cslib.Logic.Modal
