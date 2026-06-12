/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.MCS
public import Cslib.Logics.Modal.Metalogic.Soundness

/-! # Completeness Theorem for Normal Modal Logics

This module proves completeness via the canonical Kripke model
construction, parameterized over an axiom predicate `Axioms`. The
parameterized infrastructure supports all normal modal logics; an
S5-specific wrapper instantiates at `ModalAxiom`.

## Main Results

- `CanonicalWorld Axioms`: The type of worlds in the canonical model (MCS).
- `CanonicalModel Axioms`: The canonical Kripke model.
- `canonical_refl`, `canonical_trans`, `canonical_eucl`: Frame properties.
- `truth_lemma`: `Satisfies (CanonicalModel Axioms) S phi <-> phi in S.val`.
- `completeness`: If `phi` is valid over all S5 frames, then `phi` is S5-derivable.

## Design

The parameterized canonical model and truth lemma take explicit axiom hypotheses
for the propositional axioms (implyK, implyS, efq, peirce) and modal axioms
(K, T, 4, B) as needed. The S5-specific `completeness` theorem instantiates
these at `ModalAxiom`.

## References

* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Canonical Models)
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

-- Universe constraint: canonical worlds live at the same universe as `Atom`
-- because `CanonicalWorld Axioms` is a subtype of `Set (Proposition Atom)`.
-- This means worlds and atoms share universe `u` in the completeness proof.
universe u
variable {Atom : Type u}

/-! ## Canonical Model Definition -/

/-- A canonical world is a maximally consistent set of the parameterized
modal derivation system. -/
def CanonicalWorld (Axioms : Proposition Atom → Prop) :=
  { S : Set (Proposition Atom) // SetMaximalConsistent Axioms S }

/-- The canonical model parameterized over an axiom predicate.

- Accessibility: `R S T <-> forall psi, box psi in S -> psi in T`.
- Valuation: `v S p <-> atom p in S`. -/
noncomputable def CanonicalModel (Axioms : Proposition Atom → Prop) :
    Model (CanonicalWorld Axioms) Atom where
  r := fun S T => ∀ φ, (□φ) ∈ S.val → φ ∈ T.val
  v := fun S p => Proposition.atom p ∈ S.val

/-! ## Canonical Frame Properties -/

/-- The canonical accessibility relation is reflexive (from axiom T). -/
theorem canonical_refl
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_T : ∀ (φ : Proposition Atom),
      Axioms ((Proposition.box φ).imp φ))
    (S : CanonicalWorld Axioms) :
    (CanonicalModel Axioms).r S S := by
  intro φ h_box
  exact mcs_box_closure h_implyK h_implyS h_T S.property h_box

/-- The canonical accessibility relation is transitive (from axiom 4). -/
theorem canonical_trans
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_4 : ∀ (φ : Proposition Atom),
      Axioms ((Proposition.box φ).imp (Proposition.box (Proposition.box φ))))
    (S T U : CanonicalWorld Axioms) :
    (CanonicalModel Axioms).r S T →
    (CanonicalModel Axioms).r T U →
    (CanonicalModel Axioms).r S U := by
  intro hST hTU φ h_box
  have h_box_box := mcs_box_box h_implyK h_implyS h_4 S.property h_box
  have h_box_T := hST (□φ) h_box_box
  exact hTU φ h_box_T

/-- The canonical accessibility relation is symmetric (from axiom B).

This is the canonicity of axiom B (BRV Theorem 4.28 clause 2):
if `R S T` and `□φ ∈ T`, then `φ ∈ S` by contradiction using axiom B
and the double-negation introduction derivation. -/
theorem canonical_symm
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_K : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp
        ((Proposition.box φ).imp (Proposition.box ψ))))
    (h_B : ∀ (φ : Proposition Atom),
      Axioms (φ.imp (Proposition.box (Proposition.diamond φ))))
    (S T : CanonicalWorld Axioms) :
    (CanonicalModel Axioms).r S T →
    (CanonicalModel Axioms).r T S := by
  intro hST φ h_box_T
  by_contra h_phi_not_S
  have h_neg_S := mcs_neg_of_not_mem h_implyK h_implyS S.property h_phi_not_S
  have h_bd_S := mcs_box_diamond h_implyK h_implyS h_B S.property h_neg_S
  have h_diam_T := hST _ h_bd_S
  -- h_diam_T : (Proposition.box ((φ.imp .bot).imp .bot)).imp .bot ∈ T.val
  -- Need: box((φ.imp .bot).imp .bot) ∈ T.val to get contradiction
  -- Build derivation: φ → ((φ.imp .bot).imp .bot)  (double negation introduction)
  let bp := φ
  have d_bot : DerivationTree Axioms [bp.imp .bot, bp] Proposition.bot :=
    .modus_ponens [bp.imp .bot, bp] bp .bot
      (.assumption _ (bp.imp .bot) (by simp [List.mem_cons]))
      (.assumption _ bp (by simp [List.mem_cons]))
  have d_dne := deductionTheorem h_implyK h_implyS [bp] (bp.imp .bot) .bot d_bot
  have d_dni := deductionTheorem h_implyK h_implyS [] bp
    ((bp.imp .bot).imp .bot) d_dne
  have d_nec := DerivationTree.necessitation _ d_dni
  have h_box_dni_T :
      Proposition.box (bp.imp ((bp.imp .bot).imp .bot)) ∈ T.val :=
    modal_closed_under_derivation h_implyK h_implyS T.property
      (L := []) (fun _ h => nomatch h) ⟨d_nec⟩
  have h_box_dne_T := mcs_box_mp h_implyK h_implyS h_K T.property
    h_box_dni_T h_box_T
  -- h_box_dne_T : box((φ.imp .bot).imp .bot) ∈ T.val
  -- h_diam_T : (box((φ.imp .bot).imp .bot)).imp .bot ∈ T.val
  -- Together: bot ∈ T.val — contradiction
  exact mcs_bot_not_mem T.property
    (modal_implication_property h_implyK h_implyS T.property h_diam_T h_box_dne_T)

/-- The canonical accessibility relation is Euclidean (from axioms B, T, 4). -/
theorem canonical_eucl
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (_h_T : ∀ (φ : Proposition Atom),
      Axioms ((Proposition.box φ).imp φ))
    (h_4 : ∀ (φ : Proposition Atom),
      Axioms ((Proposition.box φ).imp (Proposition.box (Proposition.box φ))))
    (h_B : ∀ (φ : Proposition Atom),
      Axioms (φ.imp (Proposition.box (Proposition.diamond φ))))
    (h_K : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp
        ((Proposition.box φ).imp (Proposition.box ψ))))
    (S T U : CanonicalWorld Axioms) :
    (CanonicalModel Axioms).r S T →
    (CanonicalModel Axioms).r S U →
    (CanonicalModel Axioms).r T U := by
  intro hST hSU φ h_box_T
  have h_bb_T := mcs_box_box h_implyK h_implyS h_4 T.property h_box_T
  by_contra h_phi_not_U
  apply h_phi_not_U
  apply hSU
  by_contra h_box_not_S
  have h_neg_box := mcs_neg_of_not_mem h_implyK h_implyS S.property h_box_not_S
  have h_bd := mcs_box_diamond h_implyK h_implyS h_B S.property h_neg_box
  have h_diam_T := hST _ h_bd
  have h_box_dne_not_T :
      (□¬¬□φ)
        ∉ T.val :=
    mcs_not_mem_of_neg h_implyK h_implyS T.property h_diam_T
  let bp := Proposition.box φ
  have d_bot : DerivationTree Axioms [bp.imp .bot, bp] Proposition.bot :=
    .modus_ponens [bp.imp .bot, bp] bp .bot
      (.assumption _ (bp.imp .bot) (by simp [List.mem_cons]))
      (.assumption _ bp (by simp [List.mem_cons]))
  have d_dne := deductionTheorem h_implyK h_implyS [bp] (bp.imp .bot) .bot d_bot
  have d_dni := deductionTheorem h_implyK h_implyS [] bp
    ((bp.imp .bot).imp .bot) d_dne
  have d_nec := DerivationTree.necessitation _ d_dni
  have h_box_dni_T :
      Proposition.box (bp.imp ((bp.imp .bot).imp .bot)) ∈ T.val :=
    modal_closed_under_derivation h_implyK h_implyS T.property
      (L := []) (fun _ h => nomatch h) ⟨d_nec⟩
  have h_box_dne_T := mcs_box_mp h_implyK h_implyS h_K T.property
    h_box_dni_T h_bb_T
  exact h_box_dne_not_T h_box_dne_T

/-- The canonical accessibility relation is Euclidean (from axiom 5 alone).

If a normal logic contains axiom 5 (`◇φ → □◇φ`), then its canonical frame
is Euclidean. This is stronger than `canonical_eucl` which requires B + T + 4. -/
theorem canonical_eucl_from_5
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_K : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp
        ((Proposition.box φ).imp (Proposition.box ψ))))
    (h_5 : ∀ (φ : Proposition Atom),
      Axioms ((Proposition.diamond φ).imp
        (Proposition.box (Proposition.diamond φ))))
    (S T U : CanonicalWorld Axioms) :
    (CanonicalModel Axioms).r S T →
    (CanonicalModel Axioms).r S U →
    (CanonicalModel Axioms).r T U := by
  intro hST hSU φ h_box_T
  -- Goal: φ ∈ U.val
  by_contra h_phi_not_U
  -- Step 1: neg φ ∈ U.val
  have h_neg_U := mcs_neg_of_not_mem h_implyK h_implyS U.property h_phi_not_U
  -- Step 2: diamond(neg φ) ∈ S.val (by sub-contradiction)
  have h_diam_S : (◇¬φ) ∈ S.val := by
    -- diamond(neg φ) = (box(neg(neg φ))).imp .bot = (box((φ.imp .bot).imp .bot)).imp .bot
    by_contra h_diam_not_S
    -- If diamond(neg φ) not in S, then neg(diamond(neg φ)) in S
    -- i.e. box(neg(neg φ)) = box((φ.imp .bot).imp .bot) in S
    have h_neg_diam := mcs_neg_of_not_mem h_implyK h_implyS S.property h_diam_not_S
    -- neg(diamond(neg φ)) = (diamond(neg φ)).imp .bot
    -- diamond(neg φ) = (box((φ.imp .bot).imp .bot)).imp .bot
    -- So neg(diamond(neg φ)) = ((box((φ.imp .bot).imp .bot)).imp .bot).imp .bot
    -- This is neg(neg(box(neg neg φ))) = neg neg (box(neg neg φ))
    -- We need box(neg neg φ) ∈ S to derive neg neg φ ∈ U via hSU
    -- Actually, neg(diamond(neg φ)) = box(neg neg φ) definitionally
    -- diamond(neg φ) = neg(box(neg(neg φ))) = (box(neg neg φ)).imp .bot
    -- neg(diamond(neg φ)) = ((box(neg neg φ)).imp .bot).imp .bot
    -- But that's neg neg (box(neg neg φ)), not box(neg neg φ) itself.
    -- We need a different approach: use mcs_mem_iff_neg_not_mem
    -- Actually: diamond(x) = neg(box(neg x)) by definition
    -- So not(diamond(neg φ)) means diamond(neg φ) not in S
    -- which means neg(diamond(neg φ)) in S
    -- neg(diamond(neg φ)) = neg(neg(box(neg(neg φ)))) = neg neg (box((φ.imp .bot).imp .bot))
    -- We have neg neg (box(neg neg φ)) ∈ S.val
    -- This is ((box((φ.imp .bot).imp .bot)).imp .bot).imp .bot ∈ S.val
    -- We need to derive: (φ.imp .bot).imp .bot ∈ U.val from box((φ.imp .bot).imp .bot) ∈ S.val
    -- But we don't have box((φ.imp .bot).imp .bot) ∈ S.val directly
    -- We have neg neg (box(neg neg φ)) ∈ S.val
    -- Hmm, let me reconsider. The straightforward approach:
    -- h_diam_not_S : diamond(neg φ) ∉ S.val
    -- By definition, diamond(neg φ) = (box(neg(neg φ))).imp .bot
    -- So (box((φ.imp .bot).imp .bot)).imp .bot ∉ S.val
    -- By mcs_mem_iff_neg_not_mem (reverse): box((φ.imp .bot).imp .bot) ∈ S.val
    -- (because neg X ∉ S ↔ X ∈ S, and diamond(neg φ) IS neg(box(neg neg φ)))
    -- Wait: diamond(neg φ) = neg(box(neg(neg φ)))
    -- So diamond(neg φ) = (box((φ.imp .bot).imp .bot)).imp .bot
    -- This is the negation of box((φ.imp .bot).imp .bot)
    -- So if diamond(neg φ) ∉ S, i.e. neg(box(neg neg φ)) ∉ S
    -- then by negation_complete: box(neg neg φ) ∈ S  OR  neg(box(neg neg φ)) ∈ S
    -- Since neg(box(neg neg φ)) = diamond(neg φ) ∉ S, we get box(neg neg φ) ∈ S
    -- That gives us what we need!
    have h_box_dne_S : (□¬¬φ) ∈ S.val := by
      rcases modal_negation_complete h_implyK h_implyS S.property
        (□¬¬φ) with h | h
      · exact h
      · -- h : neg(box((φ.imp .bot).imp .bot)) ∈ S.val
        -- neg(box((φ.imp .bot).imp .bot)) = (box((φ.imp .bot).imp .bot)).imp .bot
        -- = diamond(neg φ) by definition
        -- But h_diam_not_S says diamond(neg φ) ∉ S.val
        exact absurd h h_diam_not_S
    -- By hSU: (φ.imp .bot).imp .bot ∈ U.val, i.e. neg neg φ ∈ U.val
    have h_dne_U := hSU _ h_box_dne_S
    -- h_dne_U : (φ.imp .bot).imp .bot ∈ U.val
    -- h_neg_U : φ.imp .bot ∈ U.val
    -- MP gives bot ∈ U.val — contradiction
    exact mcs_bot_not_mem U.property
      (modal_implication_property h_implyK h_implyS U.property h_dne_U h_neg_U)
  -- Step 3: axiom 5 gives box(diamond(neg φ)) ∈ S.val
  have h_box_diam_S := mcs_mp_axiom h_implyK h_implyS S.property h_diam_S
    (h_5 (¬φ))
  -- Step 4: by hST, diamond(neg φ) ∈ T.val
  have h_diam_T := hST _ h_box_diam_S
  -- Step 5: from box φ ∈ T.val, derive box(neg neg φ) ∈ T.val
  let bp := φ
  have d_bot : DerivationTree Axioms [bp.imp .bot, bp] Proposition.bot :=
    .modus_ponens [bp.imp .bot, bp] bp .bot
      (.assumption _ (bp.imp .bot) (by simp [List.mem_cons]))
      (.assumption _ bp (by simp [List.mem_cons]))
  have d_dne := deductionTheorem h_implyK h_implyS [bp] (bp.imp .bot) .bot d_bot
  have d_dni := deductionTheorem h_implyK h_implyS [] bp
    ((bp.imp .bot).imp .bot) d_dne
  have d_nec := DerivationTree.necessitation _ d_dni
  have h_box_dni_T :
      Proposition.box (bp.imp ((bp.imp .bot).imp .bot)) ∈ T.val :=
    modal_closed_under_derivation h_implyK h_implyS T.property
      (L := []) (fun _ h => nomatch h) ⟨d_nec⟩
  have h_box_dne_T := mcs_box_mp h_implyK h_implyS h_K T.property
    h_box_dni_T h_box_T
  -- Step 6: diamond(neg φ) and box(neg neg φ) in T.val → bot ∈ T.val
  exact mcs_bot_not_mem T.property
    (modal_implication_property h_implyK h_implyS T.property h_diam_T h_box_dne_T)

/-! ## Truth Lemma

There are three truth lemma families in the metalogic, each parameterized over
the axiom set and differing in which box-witness lemma they use:

- **`truth_lemma`** (this file): For logics containing axiom T. Uses
  `mcs_box_witness` from MCS.lean which relies on axiom T for the box-witness
  consistency argument. Used by: S5, T, S4, TB.

- **`k_truth_lemma`** (KCompleteness.lean): For logics NOT containing axiom T.
  Uses a K-specific box witness (`mcs_box_witness_k`) that avoids axiom T.
  Used by: K, B, K4, K5, K45, KB5.

- **`truth_lemma_d`** (DCompleteness.lean): For logics containing axiom D but
  NOT axiom T. Uses a D-specific box witness (`mcs_box_witness_d`) that replaces
  axiom T with axiom D + necessitation for the seriality argument. Used by: D,
  D4, D5, D45, DB.

All three families share the same canonical model definition (`CanonicalModel`)
from this file. Logics differ only in which frame properties are provable for
the canonical accessibility relation. -/

/-- **Truth Lemma**: For any canonical world `S` and formula `phi`,
`Satisfies (CanonicalModel Axioms) S phi <-> phi in S.val`. -/
theorem truth_lemma
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_efq : ∀ (φ : Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_peirce : ∀ (φ ψ : Proposition Atom),
      Axioms (((φ.imp ψ).imp φ).imp φ))
    (h_K : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp
        ((Proposition.box φ).imp (Proposition.box ψ))))
    (h_T : ∀ (φ : Proposition Atom),
      Axioms ((Proposition.box φ).imp φ))
    (S : CanonicalWorld Axioms) :
    (φ : Proposition Atom) →
    (Satisfies (CanonicalModel Axioms) S φ ↔ φ ∈ S.val)
  | .atom p => by
    constructor
    · intro h; exact h
    · intro h; exact h
  | .bot => by
    constructor
    · intro h; exact absurd h id
    · intro h; exact absurd h (mcs_bot_not_mem S.property)
  | .imp φ ψ => by
    constructor
    · intro h_sat
      rcases modal_negation_complete h_implyK h_implyS S.property (φ.imp ψ)
        with h | h
      · exact h
      · exfalso
        have h_phi_S : φ ∈ S.val := by
          apply modal_closed_under_derivation h_implyK h_implyS S.property
            (L := [(φ.imp ψ).imp .bot])
            (fun x hx => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
              exact hx ▸ h)
          unfold modalDerivationSystem Deriv
          have d_bot' : DerivationTree Axioms
              [φ.imp ψ, (φ.imp ψ).imp .bot] Proposition.bot :=
            .modus_ponens _ (φ.imp ψ) .bot
              (.assumption _ _ (by simp [List.mem_cons]))
              (.assumption _ _ (by simp [List.mem_cons]))
          have d_efq' : DerivationTree Axioms
              [φ.imp ψ, (φ.imp ψ).imp .bot] φ :=
            .modus_ponens _ .bot φ
              (.weakening [] _ _ (.ax [] _ (h_efq φ)) (fun _ h => nomatch h))
              d_bot'
          have d_dt := deductionTheorem h_implyK h_implyS
            [(φ.imp ψ).imp .bot] (φ.imp ψ) φ d_efq'
          have d_peirce' : DerivationTree Axioms
              [(φ.imp ψ).imp .bot] (((φ.imp ψ).imp φ).imp φ) :=
            .weakening [] _ _ (.ax [] _ (h_peirce φ ψ)) (fun _ h => nomatch h)
          exact ⟨.modus_ponens _ _ _ d_peirce' d_dt⟩
        have h_sat_phi :=
          (truth_lemma h_implyK h_implyS h_efq h_peirce h_K h_T S φ).mpr h_phi_S
        have h_psi_S :=
          (truth_lemma h_implyK h_implyS h_efq h_peirce h_K h_T S ψ).mp
            (h_sat h_sat_phi)
        have h_neg_psi_S : (¬ψ) ∈ S.val := by
          apply modal_closed_under_derivation h_implyK h_implyS S.property
            (L := [(φ.imp ψ).imp .bot])
            (fun x hx => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
              exact hx ▸ h)
          unfold modalDerivationSystem Deriv
          have d_imp : DerivationTree Axioms
              [ψ, (φ.imp ψ).imp .bot] (φ.imp ψ) :=
            .modus_ponens _ ψ (φ.imp ψ)
              (.weakening [] _ _ (.ax [] _ (h_implyK ψ φ))
                (fun _ h => nomatch h))
              (.assumption _ _ (by simp [List.mem_cons]))
          have d_bot'' : DerivationTree Axioms
              [ψ, (φ.imp ψ).imp .bot] Proposition.bot :=
            .modus_ponens _ (φ.imp ψ) .bot
              (.assumption _ _ (by simp [List.mem_cons]))
              d_imp
          exact ⟨deductionTheorem h_implyK h_implyS
            [(φ.imp ψ).imp .bot] ψ .bot d_bot''⟩
        exact mcs_bot_not_mem S.property
          (modal_implication_property h_implyK h_implyS S.property
            h_neg_psi_S h_psi_S)
    · intro h_mem h_sat_phi
      exact (truth_lemma h_implyK h_implyS h_efq h_peirce h_K h_T S ψ).mpr
        (modal_implication_property h_implyK h_implyS S.property h_mem
          ((truth_lemma h_implyK h_implyS h_efq h_peirce h_K h_T S φ).mp
            h_sat_phi))
  | .box φ => by
    constructor
    · intro h_sat
      by_contra h_not_box
      obtain ⟨T, hT_mcs, hST, h_phi_not_T⟩ :=
        mcs_box_witness h_implyK h_implyS h_efq h_peirce h_K h_T
          S.property h_not_box
      exact h_phi_not_T
        ((truth_lemma h_implyK h_implyS h_efq h_peirce h_K h_T
          ⟨T, hT_mcs⟩ φ).mp (h_sat ⟨T, hT_mcs⟩ hST))
    · intro h_box T hST
      exact (truth_lemma h_implyK h_implyS h_efq h_peirce h_K h_T T φ).mpr
        (hST φ h_box)

/-! ## Consistency of Negation -/

/-- If `phi` is not derivable from `Axioms`, then `{neg phi}` is consistent
with respect to the `Axioms` derivation system. This is the standard
Peirce-based double-negation elimination argument factored out from all
completeness theorems.

The proof constructs a derivation `[] |- phi` from any hypothetical
derivation `L |- bot` where `L` is drawn from `{neg phi}`, contradicting
the assumption that `phi` is not derivable. -/
theorem neg_consistent_of_not_derivable
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_efq : ∀ (φ : Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_peirce : ∀ (φ ψ : Proposition Atom),
      Axioms (((φ.imp ψ).imp φ).imp φ))
    {φ : Proposition Atom} (h_not_deriv : ¬Derivable Axioms φ) :
    SetConsistent Axioms ({(¬φ)} : Set (Proposition Atom)) := by
  intro L hL
  unfold Metalogic.Consistent
  intro ⟨d⟩
  have d_weak : DerivationTree Axioms [(¬φ)]
      ⊥ :=
    .weakening L [(¬φ)] ⊥ d (fun x hx => by
      have := hL x hx; simp only [Set.mem_singleton_iff] at this
      exact List.mem_cons.mpr (Or.inl this))
  have d_dne := deductionTheorem h_implyK h_implyS
    [] (¬φ) ⊥ d_weak
  let neg_phi := (¬φ)
  have efq_ax : DerivationTree Axioms (Atom := Atom) []
      (Proposition.bot.imp φ) :=
    .ax [] _ (h_efq φ)
  have ik : DerivationTree Axioms (Atom := Atom) []
      ((Proposition.bot.imp φ).imp
        (neg_phi.imp (Proposition.bot.imp φ))) :=
    .ax [] _ (h_implyK (Proposition.bot.imp φ) neg_phi)
  have step_k := DerivationTree.modus_ponens [] _ _ ik efq_ax
  have is_ax : DerivationTree Axioms (Atom := Atom) []
      ((neg_phi.imp (Proposition.bot.imp φ)).imp
       ((neg_phi.imp Proposition.bot).imp (neg_phi.imp φ))) :=
    .ax [] _ (h_implyS neg_phi Proposition.bot φ)
  have step_s := DerivationTree.modus_ponens [] _ _ is_ax step_k
  have step3 := DerivationTree.modus_ponens [] _ _ step_s d_dne
  have peirce_ax : DerivationTree Axioms (Atom := Atom) []
      (((φ.imp Proposition.bot).imp φ).imp φ) :=
    .ax [] _ (h_peirce φ Proposition.bot)
  have d_phi := DerivationTree.modus_ponens [] _ _ peirce_ax step3
  exact h_not_deriv ⟨d_phi⟩

end Cslib.Logic.Modal
