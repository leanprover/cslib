/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Temporal.Metalogic.CompletenessHelpers
public import Cslib.Logics.Temporal.Metalogic.Chronicle.TruthLemma

/-! # Completeness Theorem for Temporal Logic BX

This module proves completeness for temporal BX logic: every formula valid over
all serial linear temporal orders is derivable.

## Main Results

- `completeness`: If `φ` is valid over serial linear orders, then `Temporal.ThDerivable φ`.

## Design

The proof proceeds by contrapositive:
1. If `φ` is not derivable, `{¬φ}` is consistent (using Peirce + EFQ).
2. Extend `{¬φ}` to an MCS `M` via `temporal_lindenbaum`.
3. Construct a chronicle countermodel from `M` using the omega-chain limit
   construction. The chronicle subtype inherits `LinearOrder`, `Nontrivial`,
   `NoMaxOrder`, and `NoMinOrder` from the limit domain.
4. The truth lemma (`chronicle_truth_lemma`) establishes that satisfaction in
   the chronicle model corresponds exactly to membership in the limit point
   function.
5. Applying validity gives `φ ∈ limitF(0) = M`, contradicting `φ ∉ M`.

MCS helper lemmas (G/H-transitivity, canonical model types, etc.) are in
`CompletenessHelpers.lean` to avoid circular imports with the chronicle
construction.

## References

* Burgess (1982) — BX axiom system and completeness
* Xu (1988) — Temporal completeness proofs
* Cslib/Logics/Modal/Metalogic/Completeness.lean — structural template
-/

set_option linter.style.setOption false
set_option maxHeartbeats 3200000

@[expose] public section

namespace Cslib.Logic.Temporal

open Cslib.Logic

variable {Atom : Type*}

attribute [local instance] Classical.propDecidable

/-! ## Completeness Theorem -/

/-- If φ is not derivable, then {¬φ} is consistent. -/
theorem neg_consistent_of_not_derivable
    {φ : Formula Atom} (h_not : ¬ Temporal.ThDerivable φ) :
    Temporal.SetConsistent ({¬φ} : Set (Formula Atom)) := by
  intro L hL
  unfold Metalogic.Consistent
  intro ⟨d⟩
  have d_weak : DerivationTree FrameClass.Base [¬φ] ⊥ :=
    .weakening L [¬φ] .bot d (fun x hx => by
      have := hL x hx; simp only [Set.mem_singleton_iff] at this
      exact List.mem_cons.mpr (Or.inl this))
  have d_dne := deductionTheorem [] (¬φ) .bot d_weak
  let neg_phi := Formula.neg φ
  have efq : DerivationTree (Atom := Atom) FrameClass.Base []
      (Formula.bot.imp φ) := .axiom [] _ (.efq φ) trivial
  have ik : DerivationTree (Atom := Atom) FrameClass.Base []
      ((Formula.bot.imp φ).imp (neg_phi.imp (Formula.bot.imp φ))) :=
    .axiom [] _ (.imp_s (Formula.bot.imp φ) neg_phi) trivial
  have step_k := DerivationTree.modus_ponens [] _ _ ik efq
  have is_ax : DerivationTree (Atom := Atom) FrameClass.Base []
      ((neg_phi.imp (Formula.bot.imp φ)).imp
       ((neg_phi.imp Formula.bot).imp (neg_phi.imp φ))) :=
    .axiom [] _ (.imp_k neg_phi Formula.bot φ) trivial
  have step_s := DerivationTree.modus_ponens [] _ _ is_ax step_k
  have step3 := DerivationTree.modus_ponens [] _ _ step_s d_dne
  have peirce_ax : DerivationTree (Atom := Atom) FrameClass.Base []
      (((φ.imp Formula.bot).imp φ).imp φ) :=
    .axiom [] _ (.peirce φ Formula.bot) trivial
  exact h_not ⟨DerivationTree.modus_ponens [] _ _ peirce_ax step3⟩

/-- **Completeness Theorem for Temporal Logic BX**:

If `φ` is valid over all serial linear temporal orders (linear orders with
`NoMaxOrder` and `NoMinOrder`), then `φ` is derivable in the BX proof system.

The proof proceeds by contrapositive: if `φ` is not derivable, then `{¬φ}` is
consistent and extends to an MCS `M` via Lindenbaum's lemma. The chronicle
limit construction builds a countermodel on a subtype of `ℚ` with the required
order properties. The truth lemma (Burgess Claim 2.11) connects satisfaction
to MCS membership. Since `φ ∉ M` but validity forces `φ ∈ M`, we obtain a
contradiction. -/
theorem completeness [Denumerable (Formula Atom)] {φ : Formula Atom}
    (h_valid : ∀ (D : Type) [LinearOrder D] [Nontrivial D]
      [NoMaxOrder D] [NoMinOrder D]
      (M : TemporalModel D Atom) (t : D), Satisfies M t φ) :
    Temporal.ThDerivable φ := by
  by_contra h_not_deriv
  have h_cons := neg_consistent_of_not_derivable h_not_deriv
  obtain ⟨M, hM_sup, hM_mcs⟩ := temporal_lindenbaum h_cons
  have h_neg_in_M : (¬φ) ∈ M := hM_sup (Set.mem_singleton _)
  have h_phi_not_M : φ ∉ M := mcs_not_mem_of_neg hM_mcs h_neg_in_M
  -- Build the chronicle countermodel from the MCS M.
  -- The chronicle construction produces limitDom and limitF with:
  --   0 ∈ limitDom, limitF(0) = M, C0/C4/C5 satisfaction.
  -- ChronicleToCountermodel provides the TemporalModel on ChronicleSubtype
  -- with LinearOrder, Nontrivial, NoMaxOrder, NoMinOrder.
  let D := Metalogic.Chronicle.ChronicleSubtype M hM_mcs
  let model := Metalogic.Chronicle.chronicleModel M hM_mcs
  let t₀ : D := Metalogic.Chronicle.chronicleZero M hM_mcs
  -- Apply validity: φ is true at t₀ in the chronicle model.
  have h_sat := h_valid D model t₀
  -- By the truth lemma: Satisfies model t₀ φ ↔ φ ∈ limitF M hM_mcs t₀.val
  have h_mem := (Metalogic.Chronicle.chronicle_truth_lemma M hM_mcs t₀ φ).mp h_sat
  -- t₀.val = 0 and limitF(0) = M, so φ ∈ M.
  have h_zero : t₀.val = 0 := rfl
  rw [h_zero, Metalogic.Chronicle.limit_f_zero] at h_mem
  -- Contradiction: φ ∈ M but φ ∉ M.
  exact h_phi_not_M h_mem

end Cslib.Logic.Temporal
