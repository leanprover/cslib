/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Completeness
public import Cslib.Logics.Modal.Metalogic.DSoundness

/-! # Completeness Theorem for Modal Logic D (KD)

This module proves completeness for modal logic D over serial Kripke frames
via the canonical model construction (completeness-via-canonicity).

## Main Results

- `derive_box_from_inconsistency_d`: Box witness consistency using axiom D + NEC
  instead of axiom T.
- `mcs_box_witness_d`: Box witness for D (K-style, without axiom T).
- `canonical_serial`: The canonical model for any DAxiom-containing system is serial
  (Blackburn Theorem 4.28 clause 3).
- `truth_lemma_d`: Truth lemma using D-style box witness.
- `d_completeness`: Completeness for D over serial frames.

## References

* Blackburn, de Rijke, Venema, "Modal Logic" (2002), Chapter 4
  - Theorem 4.28 clause 3 (KD seriality is canonical)
  - Lemma 4.21 (Truth Lemma)
  - Proposition 4.12 (Completeness criterion)
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

/-! ## Box Witness Consistency for D -/

/-- From `L |- bot` where `L <= {psi | box psi in S} union {neg phi}`,
derive `False`, using axiom D instead of axiom T.

This adapts `derive_box_from_inconsistency` from MCS.lean:
- Case 1 (neg phi in L): Identical to S5 -- filter, deduction theorem, derive box phi.
- Case 2 (neg phi not in L): All elements have box versions in S. From L |- bot,
  derive box bot in S. Then axiom D gives diamond bot in S. Since top (= bot -> bot)
  is derivable, NEC gives box top in S. MP with diamond bot gives bot in S.
  Contradiction with MCS consistency. -/
theorem derive_box_from_inconsistency_d
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
    (h_D : ∀ (φ : Proposition Atom),
      Axioms ((Proposition.box φ).imp
        ((Proposition.box (φ.imp .bot)).imp .bot)))
    {S : Set (Proposition Atom)} (h_mcs : Modal.SetMaximalConsistent Axioms S)
    {φ : Proposition Atom} (h_not_box : Proposition.box φ ∉ S)
    {L : List (Proposition Atom)}
    (hL : ∀ x ∈ L, x ∈ {ψ | Proposition.box ψ ∈ S} ∪ {Proposition.neg φ})
    (d_bot : DerivationTree Axioms L Proposition.bot) : False := by
  classical
  let L' := L.filter (· ≠ Proposition.neg φ)
  have h_L'_box : ∀ ψ ∈ L', Proposition.box ψ ∈ S := by
    intro ψ hψ
    simp only [L', List.mem_filter, decide_eq_true_eq] at hψ
    rcases hL ψ hψ.1 with h | h
    · exact h
    · exact absurd h hψ.2
  by_cases h_neg_in_L : Proposition.neg φ ∈ L
  · -- Case 1: neg phi in L -- identical to S5 version
    have h_perm : ∀ x, x ∈ L → x ∈ Proposition.neg φ :: L' := by
      intro x hx
      by_cases hxn : x = Proposition.neg φ
      · exact List.mem_cons.mpr (Or.inl hxn)
      · exact List.mem_cons.mpr (Or.inr (by
          simp only [L', List.mem_filter, decide_eq_true_eq]; exact ⟨hx, hxn⟩))
    have d_reord := DerivationTree.weakening L (Proposition.neg φ :: L')
      Proposition.bot d_bot h_perm
    have d_dne := deductionTheorem h_implyK h_implyS L' (Proposition.neg φ)
      Proposition.bot d_reord
    let neg_phi := Proposition.neg φ
    have efq_ax : DerivationTree Axioms L' (Proposition.bot.imp φ) :=
      .weakening [] L' _ (.ax [] _ (h_efq φ)) (fun _ h => nomatch h)
    have ik : DerivationTree Axioms L'
        ((Proposition.bot.imp φ).imp (neg_phi.imp (Proposition.bot.imp φ))) :=
      .weakening [] L' _ (.ax [] _ (h_implyK (Proposition.bot.imp φ) neg_phi))
        (fun _ h => nomatch h)
    have step_k := DerivationTree.modus_ponens L' _ _ ik efq_ax
    have is_ax : DerivationTree Axioms L'
        ((neg_phi.imp (Proposition.bot.imp φ)).imp
         ((neg_phi.imp Proposition.bot).imp (neg_phi.imp φ))) :=
      .weakening [] L' _ (.ax [] _ (h_implyS neg_phi Proposition.bot φ))
        (fun _ h => nomatch h)
    have step_s := DerivationTree.modus_ponens L' _ _ is_ax step_k
    have step3 := DerivationTree.modus_ponens L' _ _ step_s d_dne
    have peirce_ax : DerivationTree Axioms L'
        (((φ.imp Proposition.bot).imp φ).imp φ) :=
      .weakening [] L' _ (.ax [] _ (h_peirce φ Proposition.bot))
        (fun _ h => nomatch h)
    have d_phi := DerivationTree.modus_ponens L' _ _ peirce_ax step3
    exact h_not_box (derive_box_from_box_context h_implyK h_implyS h_K h_mcs
      d_phi h_L'_box)
  · -- Case 2: neg phi not in L -- D-specific argument (replaces T fallback)
    -- All elements of L have box versions in S
    have h_all_box : ∀ x ∈ L, Proposition.box x ∈ S := by
      intro x hx
      rcases hL x hx with h | h
      · exact h
      · exact absurd (h ▸ hx) h_neg_in_L
    -- From L |- bot and all box x in S, derive box bot in S
    have h_box_bot : Proposition.box Proposition.bot ∈ S :=
      derive_box_from_box_context h_implyK h_implyS h_K h_mcs d_bot h_all_box
    -- Axiom D at bot: box bot -> diamond bot = box bot -> (box top) -> bot
    -- where top = bot -> bot and diamond bot = (box (bot -> bot)) -> bot
    have h_diamond_bot : Proposition.diamond Proposition.bot ∈ S :=
      mcs_mp_axiom h_implyK h_implyS h_mcs h_box_bot (h_D Proposition.bot)
    -- top = bot -> bot is derivable: from implyK bot bot we get bot -> (bot -> bot)
    -- which gives us bot -> bot after simplification. Actually, let's build it directly.
    -- We need: [] |- bot -> bot
    -- This is immediate from implyK: K gives φ → (ψ → φ), instantiate at bot, bot
    -- to get bot -> (bot -> bot). But we need bot -> bot.
    -- Actually, from efq: bot -> (bot -> bot), and from implyK: bot -> ((bot -> bot) -> bot)...
    -- Simpler: use the identity derivation via implyK + implyS
    -- I (φ) = S φ (K φ) K = ((φ→((ψ→φ)→φ))→((φ→(ψ→φ))→(φ→φ)))
    -- Let's just construct it step by step:
    -- efq gives bot -> bot directly? No, efq gives bot -> phi for any phi.
    -- So efq bot gives bot -> bot. Wait: h_efq (Proposition.bot) gives
    -- Axioms (Proposition.bot.imp Proposition.bot). Yes! That's bot -> bot.
    have d_top : DerivationTree Axioms [] (Proposition.imp .bot .bot) :=
      .ax [] _ (h_efq Proposition.bot)
    -- NEC: box top is derivable from empty context
    have d_box_top : DerivationTree Axioms [] (Proposition.box (Proposition.imp .bot .bot)) :=
      .necessitation _ d_top
    -- box top in S (derivable formula in MCS)
    have h_box_top : Proposition.box (Proposition.imp .bot .bot) ∈ S :=
      modal_closed_under_derivation h_implyK h_implyS h_mcs
        (L := []) (fun _ h => nomatch h) ⟨d_box_top⟩
    -- diamond bot = (box(bot -> bot)) -> bot = (box top) -> bot
    -- h_diamond_bot : (box(bot -> bot)).imp bot ∈ S
    -- h_box_top : box(bot -> bot) ∈ S
    -- By MP: bot in S
    have h_bot : Proposition.bot ∈ S :=
      modal_implication_property h_implyK h_implyS h_mcs h_diamond_bot h_box_top
    -- Contradiction: bot not in MCS
    exact mcs_bot_not_mem h_mcs h_bot

/-! ## Box Witness for D -/

/-- **Box Witness for D**: If `box phi not in S` and `S` is MCS, then there exists
an MCS `T` such that `forall psi, box psi in S -> psi in T` and `phi not in T`.

This uses axiom D instead of axiom T for the consistency argument. -/
theorem mcs_box_witness_d
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
    (h_D : ∀ (φ : Proposition Atom),
      Axioms ((Proposition.box φ).imp
        ((Proposition.box (φ.imp .bot)).imp .bot)))
    {S : Set (Proposition Atom)} (h_mcs : Modal.SetMaximalConsistent Axioms S)
    {φ : Proposition Atom} (h_not_box : Proposition.box φ ∉ S) :
    ∃ T : Set (Proposition Atom), Modal.SetMaximalConsistent Axioms T ∧
      (∀ ψ, Proposition.box ψ ∈ S → ψ ∈ T) ∧ φ ∉ T := by
  let W := {ψ : Proposition Atom | Proposition.box ψ ∈ S} ∪ {Proposition.neg φ}
  have hW : Modal.SetConsistent Axioms W := by
    intro L hL
    unfold Metalogic.Consistent
    intro ⟨d_bot⟩
    exact derive_box_from_inconsistency_d h_implyK h_implyS h_efq h_peirce h_K h_D
      h_mcs h_not_box hL d_bot
  obtain ⟨T, hWT, hT_mcs⟩ := modal_lindenbaum hW
  refine ⟨T, hT_mcs, ?_, ?_⟩
  · intro ψ h_box
    exact hWT (Set.mem_union_left _ h_box)
  · have h_neg : Proposition.neg φ ∈ T :=
      hWT (Set.mem_union_right _ (Set.mem_singleton _))
    exact mcs_not_mem_of_neg h_implyK h_implyS hT_mcs h_neg

/-! ## Canonical Seriality (Blackburn Theorem 4.28 clause 3) -/

/-- **Canonical Seriality**: The canonical model for any DAxiom-containing system
is serial.

This is Blackburn Theorem 4.28 clause 3: "it suffices to show that the canonical model
for KD is right-unbounded [serial]."

The proof shows {psi | box psi in S} is consistent using a D+NEC contradiction argument,
then extends to MCS via Lindenbaum. -/
theorem canonical_serial
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_efq : ∀ (φ : Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_K : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp
        ((Proposition.box φ).imp (Proposition.box ψ))))
    (h_D : ∀ (φ : Proposition Atom),
      Axioms ((Proposition.box φ).imp
        ((Proposition.box (φ.imp .bot)).imp .bot)))
    (S : CanonicalWorld Axioms) :
    ∃ T : CanonicalWorld Axioms, (CanonicalModel Axioms).r S T := by
  -- Let W = {psi | box psi in S.val}
  let W := {ψ : Proposition Atom | Proposition.box ψ ∈ S.val}
  -- Show W is consistent
  have hW : Modal.SetConsistent Axioms W := by
    intro L hL
    unfold Metalogic.Consistent
    intro ⟨d_bot⟩
    -- All elements of L have box versions in S
    have h_all_box : ∀ x ∈ L, Proposition.box x ∈ S.val := fun x hx => hL x hx
    -- From L |- bot, derive box bot in S
    have h_box_bot : Proposition.box Proposition.bot ∈ S.val :=
      derive_box_from_box_context h_implyK h_implyS h_K S.property d_bot h_all_box
    -- Axiom D at bot: box bot -> diamond bot
    have h_diamond_bot : Proposition.diamond Proposition.bot ∈ S.val :=
      mcs_mp_axiom h_implyK h_implyS S.property h_box_bot (h_D Proposition.bot)
    -- top = bot -> bot is derivable via efq
    have d_top : DerivationTree Axioms [] (Proposition.imp .bot .bot) :=
      .ax [] _ (h_efq Proposition.bot)
    have d_box_top : DerivationTree Axioms []
        (Proposition.box (Proposition.imp .bot .bot)) :=
      .necessitation _ d_top
    have h_box_top : Proposition.box (Proposition.imp .bot .bot) ∈ S.val :=
      modal_closed_under_derivation h_implyK h_implyS S.property
        (L := []) (fun _ h => nomatch h) ⟨d_box_top⟩
    -- diamond bot = (box top) -> bot; MP with box top gives bot in S
    have h_bot : Proposition.bot ∈ S.val :=
      modal_implication_property h_implyK h_implyS S.property
        h_diamond_bot h_box_top
    exact mcs_bot_not_mem S.property h_bot
  -- Extend W to MCS T via Lindenbaum
  obtain ⟨T, hWT, hT_mcs⟩ := modal_lindenbaum hW
  -- Construct CanonicalWorld from T
  let T' : CanonicalWorld Axioms := ⟨T, hT_mcs⟩
  refine ⟨T', ?_⟩
  -- Show (CanonicalModel Axioms).r S T': for any phi, box phi in S -> phi in T
  intro φ h_box
  exact hWT h_box

/-! ## Truth Lemma for D -/

/-- **Truth Lemma for D**: For any canonical world `S` and formula `phi`,
`Satisfies (CanonicalModel Axioms) S phi <-> phi in S.val`.

This follows Blackburn Lemma 4.21. The only difference from the S5 truth lemma
is the box case, which uses `mcs_box_witness_d` (axiom D) instead of
`mcs_box_witness` (axiom T). -/
theorem truth_lemma_d
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
    (h_D : ∀ (φ : Proposition Atom),
      Axioms ((Proposition.box φ).imp
        ((Proposition.box (φ.imp .bot)).imp .bot)))
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
            (fun x hx => by simp [List.mem_cons] at hx; exact hx ▸ h)
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
          (truth_lemma_d h_implyK h_implyS h_efq h_peirce h_K h_D S φ).mpr h_phi_S
        have h_psi_S :=
          (truth_lemma_d h_implyK h_implyS h_efq h_peirce h_K h_D S ψ).mp
            (h_sat h_sat_phi)
        have h_neg_psi_S : Proposition.neg ψ ∈ S.val := by
          apply modal_closed_under_derivation h_implyK h_implyS S.property
            (L := [(φ.imp ψ).imp .bot])
            (fun x hx => by simp [List.mem_cons] at hx; exact hx ▸ h)
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
      exact (truth_lemma_d h_implyK h_implyS h_efq h_peirce h_K h_D S ψ).mpr
        (modal_implication_property h_implyK h_implyS S.property h_mem
          ((truth_lemma_d h_implyK h_implyS h_efq h_peirce h_K h_D S φ).mp
            h_sat_phi))
  | .box φ => by
    constructor
    · intro h_sat
      by_contra h_not_box
      obtain ⟨T, hT_mcs, hST, h_phi_not_T⟩ :=
        mcs_box_witness_d h_implyK h_implyS h_efq h_peirce h_K h_D
          S.property h_not_box
      exact h_phi_not_T
        ((truth_lemma_d h_implyK h_implyS h_efq h_peirce h_K h_D
          ⟨T, hT_mcs⟩ φ).mp (h_sat ⟨T, hT_mcs⟩ hST))
    · intro h_box T hST
      exact (truth_lemma_d h_implyK h_implyS h_efq h_peirce h_K h_D T φ).mpr
        (hST φ h_box)

/-! ## Completeness Theorem for D -/

/-- **Completeness Theorem for Modal Logic D**:

If `phi` is valid over all serial frames, then `phi` is derivable from the empty
context in the D proof system.

This follows Blackburn Proposition 4.12 + Theorem 4.28 clause 3:
1. Assume phi is not derivable.
2. Then {neg phi} is consistent.
3. By Lindenbaum, extend to MCS M containing neg phi.
4. The canonical model is serial (canonical_serial, Theorem 4.28 clause 3).
5. By validity hypothesis, phi is satisfied at M in the canonical model.
6. By truth lemma, phi in M.
7. But neg phi in M, contradiction. -/
theorem d_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      Relation.Serial m.r →
      ∀ w, Satisfies m w φ) :
    Derivable (@DAxiom Atom) φ := by
  by_contra h_not_deriv
  have h_cons : Modal.SetConsistent (@DAxiom Atom)
      ({Proposition.neg φ} : Set (Proposition Atom)) := by
    intro L hL
    unfold Metalogic.Consistent
    intro ⟨d⟩
    have d_weak : DerivationTree (@DAxiom Atom) [Proposition.neg φ]
        Proposition.bot :=
      .weakening L [Proposition.neg φ] .bot d (fun x hx => by
        have := hL x hx; simp at this
        exact List.mem_cons.mpr (Or.inl this))
    have d_dne := deductionTheorem
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      [] (Proposition.neg φ) .bot d_weak
    let neg_phi := Proposition.neg φ
    have efq_ax : DerivationTree (@DAxiom Atom) (Atom := Atom) []
        (Proposition.bot.imp φ) :=
      .ax [] _ (.efq φ)
    have ik : DerivationTree (@DAxiom Atom) (Atom := Atom) []
        ((Proposition.bot.imp φ).imp
          (neg_phi.imp (Proposition.bot.imp φ))) :=
      .ax [] _ (.implyK (Proposition.bot.imp φ) neg_phi)
    have step_k := DerivationTree.modus_ponens [] _ _ ik efq_ax
    have is_ax : DerivationTree (@DAxiom Atom) (Atom := Atom) []
        ((neg_phi.imp (Proposition.bot.imp φ)).imp
         ((neg_phi.imp Proposition.bot).imp (neg_phi.imp φ))) :=
      .ax [] _ (.implyS neg_phi Proposition.bot φ)
    have step_s := DerivationTree.modus_ponens [] _ _ is_ax step_k
    have step3 := DerivationTree.modus_ponens [] _ _ step_s d_dne
    have peirce_ax : DerivationTree (@DAxiom Atom) (Atom := Atom) []
        (((φ.imp Proposition.bot).imp φ).imp φ) :=
      .ax [] _ (.peirce φ Proposition.bot)
    have d_phi := DerivationTree.modus_ponens [] _ _ peirce_ax step3
    exact h_not_deriv ⟨d_phi⟩
  obtain ⟨M, hM_sup, hM_mcs⟩ := modal_lindenbaum h_cons
  let w : CanonicalWorld (@DAxiom Atom) := ⟨M, hM_mcs⟩
  -- Show canonical model is serial
  have h_serial : Relation.Serial (CanonicalModel (@DAxiom Atom)).r := by
    constructor
    intro S
    exact canonical_serial
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      (fun φ => .efq φ)
      (fun φ ψ => .modalK φ ψ)
      (fun φ => .modalD φ)
      S
  exact mcs_not_mem_of_neg
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    hM_mcs (hM_sup (Set.mem_singleton _))
    ((truth_lemma_d
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      (fun φ => .efq φ)
      (fun φ ψ => .peirce φ ψ)
      (fun φ ψ => .modalK φ ψ)
      (fun φ => .modalD φ)
      w φ).mp
      (h_valid (CanonicalWorld (@DAxiom Atom))
        (CanonicalModel (@DAxiom Atom))
        h_serial
        w))

end Cslib.Logic.Modal
