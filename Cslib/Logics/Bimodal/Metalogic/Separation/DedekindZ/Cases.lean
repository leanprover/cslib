/-
Copyright (c) 2025 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.Separation.DedekindZ.QLemma

set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.style.show false
set_option linter.style.maxHeartbeats false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

/-!
# Cases 5-8 Separability on Z via Replacement and Direct-Formula Construction

Replace-U infrastructure, congruence lemmas, and Cases 5-8 separability proofs
for Dedekind-complete integer orders (GHR94 Lemma 10.3.11 items 5-8 on Z).
-/

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.Separation

open Cslib.Logic.Bimodal
open Classical

variable {Atom : Type*} [DecidableEq Atom]

/-! ## Cases 5-8 Separability (Non-Circular)

Cases 5-8 are proved separable without using the `all_separable` axiom.
Each case uses GHR94 direct formulas (items 5-8 of Lemma 10.2.3) to
decompose the S-formula into terms that reduce to earlier cases.

The case3_equiv_Z_general theorem above provides the key semantic decomposition.
The hierarchy provides the inductive framework to handle the nested temporal
operators that appear in the decomposed formulas.

Mathematical justification: GHR94 Lemma 10.3.11 items 5-8 specialized to Z. -/

/-! ## Helper lemmas for Cases 5-8 -/

/-- case3_alpha(a∧U, q, A, B) implies U(A,B): the alpha event always makes U true.
    alpha = (a∧U) ∨ ((¬q ∧ S(a∧U, q)) ∧ (q∨U))
    First disjunct has U. Second disjunct: ¬q ∧ (q∨U) → ¬q ∧ U → U. -/
theorem case3_alpha_aU_implies_U (a q A B : Formula Atom) (M : IntStructure Atom) (t : ℤ)
    (h : intTruth M t (case3_alpha (Formula.and a (.untl A B)) q A B)) :
    intTruth M t (.untl A B) := by
  simp only [case3_alpha] at h
  -- h : intTruth M t ((a∧U) ∨ ((¬q ∧ S(a∧U, q)) ∧ (q∨U)))
  rcases (int_truth_or M t _ _).mp h with h_left | h_right
  · -- Case (a∧U): extract U from the ∧
    exact ((int_truth_and M t _ _).mp h_left).2
  · -- Case (¬q ∧ S(a∧U, q)) ∧ (q∨U):
    have hand := (int_truth_and M t _ _).mp h_right
    have h_nq_and_s := hand.1
    have h_q_or_u := hand.2
    have h_nq := ((int_truth_and M t _ _).mp h_nq_and_s).1
    -- h_q_or_u : intTruth M t (q∨U), h_nq : intTruth M t (¬q) = ¬ intTruth M t q
    rcases (int_truth_or M t _ _).mp h_q_or_u with h_q | h_u
    · exact absurd h_q h_nq
    · exact h_u

/-- alpha(a∧U, q, A, B) is intEquiv to (a ∨ (¬q ∧ S(a∧U, q))) ∧ U(A,B).
    This factoring allows us to extract a U-free event for Case 1 application. -/
theorem case3_alpha_aU_factor (a q A B : Formula Atom) :
    intEquiv (case3_alpha (Formula.and a (.untl A B)) q A B)
      (Formula.and (Formula.or a (Formula.and (Formula.neg q)
        (.snce (Formula.and a (.untl A B)) q))) (.untl A B)) := by
  intro M t; constructor
  · intro h
    have hU := case3_alpha_aU_implies_U a q A B M t h
    apply (int_truth_and M t _ _).mpr
    constructor
    · -- (a ∨ (¬q ∧ S(a∧U, q))) from alpha
      simp only [case3_alpha] at h
      rcases (int_truth_or M t _ _).mp h with h_left | h_right
      · exact (int_truth_or M t _ _).mpr (Or.inl ((int_truth_and M t _ _).mp h_left).1)
      · have hand := (int_truth_and M t _ _).mp h_right
        exact (int_truth_or M t _ _).mpr (Or.inr hand.1)
    · exact hU
  · intro h
    have ⟨h_or, hU⟩ := (int_truth_and M t _ _).mp h
    simp only [case3_alpha]
    rcases (int_truth_or M t _ _).mp h_or with h_a | h_nq_s
    · exact (int_truth_or M t _ _).mpr (Or.inl ((int_truth_and M t _ _).mpr ⟨h_a, hU⟩))
    · exact (int_truth_or M t _ _).mpr (Or.inr ((int_truth_and M t _ _).mpr ⟨h_nq_s, (int_truth_or M t _ _).mpr (Or.inr hU)⟩))

/-! ## Replace U(A,B) with True Infrastructure

When U(A,B) appears only under boolean connectives (not under temporal operators),
replacing it with True (= neg bot) preserves truth at any time where U(A,B) holds.
This enables extracting a U-free event from S-formulas for Case 1 application. -/

/-- Replace all occurrences of `.untl A B` with `neg bot` (True) in a formula. -/
def replaceUntlWithTop (phi A B : Formula Atom) : Formula Atom :=
  match phi with
  | .atom a => .atom a
  | .bot => .bot
  | .imp p q => .imp (replaceUntlWithTop p A B) (replaceUntlWithTop q A B)
  | .box p => .box (replaceUntlWithTop p A B)
  | .untl p q => if p = A ∧ q = B then Formula.neg .bot else
      .untl (replaceUntlWithTop p A B) (replaceUntlWithTop q A B)
  | .snce p q => .snce (replaceUntlWithTop p A B) (replaceUntlWithTop q A B)

/-- If phi is U-free, replaceUntlWithTop is the identity. -/
theorem replace_id_of_U_free (phi A B : Formula Atom) (h : isUFree phi = true) :
    replaceUntlWithTop phi A B = phi := by
  induction phi with
  | atom _ => rfl | bot => rfl
  | imp p q ihp ihq => simp [isUFree] at h; simp [replaceUntlWithTop, ihp h.1, ihq h.2]
  | box p ih => simp [isUFree] at h; simp [replaceUntlWithTop, ih h]
  | untl _ _ => simp [isUFree] at h
  | snce p q ihp ihq => simp [isUFree] at h; simp [replaceUntlWithTop, ihp h.1, ihq h.2]

/-- U(A,B) appears only under boolean connectives (imp), not under
    temporal operators (.snce, .untl, .allPast, .allFuture, .box).
    At any time where U(A,B) holds, replacing U(A,B) with True preserves truth. -/
def untlUnderBoolOnly : Formula Atom → Formula Atom → Formula Atom → Prop
  | .atom _, _, _ => True
  | .bot, _, _ => True
  | .imp p q, A, B => untlUnderBoolOnly p A B ∧ untlUnderBoolOnly q A B
  | .box p, _, _ => isUFree p = true
  | .untl p q, A, B => (p = A ∧ q = B) ∨ (isUFree (.untl p q) = true)
  | .snce p q, _, _ => isUFree p = true ∧ isUFree q = true

/-- U-free formulas satisfy untlUnderBoolOnly trivially. -/
theorem u_free_untl_under_bool (phi A B : Formula Atom) (h : isUFree phi = true) :
    untlUnderBoolOnly phi A B := by
  induction phi with
  | atom _ => trivial | bot => trivial
  | imp p q ihp ihq => simp [isUFree] at h; exact ⟨ihp h.1, ihq h.2⟩
  | box _ => simp [isUFree] at h; exact h
  | untl _ _ => simp [isUFree] at h
  | snce p q _ _ => simp [isUFree] at h; exact h

/-- replaceUntlWithTop produces U-free result when untlUnderBoolOnly holds. -/
theorem replace_U_free_of_bool (phi A B : Formula Atom)
    (h_bool : untlUnderBoolOnly phi A B) :
    isUFree (replaceUntlWithTop phi A B) = true := by
  induction phi with
  | atom _ => rfl | bot => rfl
  | imp p q ihp ihq =>
    have ⟨hp, hq⟩ := h_bool
    simp [replaceUntlWithTop, isUFree, ihp hp, ihq hq]
  | box p _ =>
    simp only [replaceUntlWithTop]; simp only [isUFree, replace_id_of_U_free p A B h_bool]
    exact h_bool
  | untl p q _ _ =>
    simp only [replaceUntlWithTop]
    rcases h_bool with ⟨rfl, rfl⟩ | h_uf
    · simp [isUFree, Formula.neg]
    · simp [isUFree] at h_uf
  | snce p q _ _ =>
    have ⟨hp, hq⟩ := h_bool
    show isUFree (.snce (replaceUntlWithTop p A B) (replaceUntlWithTop q A B)) = true
    simp [isUFree, replace_id_of_U_free p A B hp, replace_id_of_U_free q A B hq, hp, hq]

/-- For formulas where U(A,B) is only under boolean connectives,
    at a time where U(A,B) holds, truth is preserved by replacement. -/
theorem replace_correct_bool (phi A B : Formula Atom) (M : IntStructure Atom) (t : ℤ)
    (h_bool : untlUnderBoolOnly phi A B)
    (hU : intTruth M t (.untl A B)) :
    intTruth M t phi ↔ intTruth M t (replaceUntlWithTop phi A B) := by
  induction phi generalizing t with
  | atom _ => simp [replaceUntlWithTop]
  | bot => simp [replaceUntlWithTop]
  | imp p q ihp ihq =>
    have ⟨hp, hq⟩ := h_bool
    simp only [replaceUntlWithTop, intTruth]
    exact Iff.imp (ihp t hp hU) (ihq t hq hU)
  | box _ => simp [replaceUntlWithTop, intTruth]
  | untl p q _ _ =>
    simp only [replaceUntlWithTop]
    rcases h_bool with ⟨rfl, rfl⟩ | h_uf
    · simp [intTruth, Formula.neg]; exact hU
    · simp [isUFree] at h_uf
  | snce p q _ _ =>
    have ⟨hp, hq⟩ := h_bool
    simp only [replaceUntlWithTop, intTruth, replace_id_of_U_free p A B hp,
               replace_id_of_U_free q A B hq]

/-- case1_psi satisfies untlUnderBoolOnly: its only .untl is .untl A B,
    and all .snce args are U-free. -/
theorem case1_psi_bool_only (a q A B : Formula Atom)
    (ha : isUFree a = true) (hq : isUFree q = true)
    (hA : isUFree A = true) (hB : isUFree B = true) :
    untlUnderBoolOnly (case1_psi a q A B) A B := by
  have h_and : ∀ p q, untlUnderBoolOnly p A B → untlUnderBoolOnly q A B →
      untlUnderBoolOnly (Formula.and p q) A B := by
    intro p q hp hq; show untlUnderBoolOnly (.imp (.imp p (.imp q .bot)) .bot) A B
    exact ⟨⟨hp, hq, trivial⟩, trivial⟩
  have h_or : ∀ p q, untlUnderBoolOnly p A B → untlUnderBoolOnly q A B →
      untlUnderBoolOnly (Formula.or p q) A B := by
    intro p q hp hq; show untlUnderBoolOnly (.imp (.imp p .bot) q) A B
    exact ⟨⟨hp, trivial⟩, hq⟩
  unfold case1_psi
  apply h_or; apply h_or
  · apply h_and; apply h_and; apply h_and
    · exact (⟨ha, hq⟩ : untlUnderBoolOnly (.snce a q) A B)
    · exact (⟨ha, hB⟩ : untlUnderBoolOnly (.snce a B) A B)
    · exact u_free_untl_under_bool B A B hB
    · exact Or.inl ⟨rfl, rfl⟩
  · apply h_and; apply h_and
    · exact u_free_untl_under_bool A A B hA
    · exact (⟨ha, hB⟩ : untlUnderBoolOnly (.snce a B) A B)
    · exact (⟨ha, hq⟩ : untlUnderBoolOnly (.snce a q) A B)
  · have hev_uf : isUFree (Formula.and (Formula.and (Formula.and A q) (.snce a B)) (.snce a q)) = true := by
      simp [Formula.and, Formula.neg, isUFree, hA, hq, ha, hB]
    exact (⟨hev_uf, hq⟩ : untlUnderBoolOnly (.snce _ q) A B)

/-! ## Congruence Lemmas -/

/-- If at every time where U(A,B) holds, C₁ ↔ C₂, then
    S(C₁ ∧ U, guard) ↔ S(C₂ ∧ U, guard). -/
theorem snce_event_congr_with_U (C₁ C₂ guard A B : Formula Atom)
    (h_eq : ∀ M : IntStructure Atom, ∀ t : ℤ, intTruth M t (.untl A B) →
      (intTruth M t C₁ ↔ intTruth M t C₂)) :
    intEquiv (.snce (Formula.and C₁ (.untl A B)) guard)
              (.snce (Formula.and C₂ (.untl A B)) guard) := by
  intro M t; constructor
  · rintro ⟨s, hst, h_event, h_guard⟩
    have ⟨hC₁, hU⟩ := (int_truth_and M s _ _).mp h_event
    exact ⟨s, hst, (int_truth_and M s _ _).mpr ⟨(h_eq M s hU).mp hC₁, hU⟩, h_guard⟩
  · rintro ⟨s, hst, h_event, h_guard⟩
    have ⟨hC₂, hU⟩ := (int_truth_and M s _ _).mp h_event
    exact ⟨s, hst, (int_truth_and M s _ _).mpr ⟨(h_eq M s hU).mpr hC₂, hU⟩, h_guard⟩

/-- snce congrence on event. -/
theorem snce_event_congr {φ₁ φ₂ ψ : Formula Atom} (h : intEquiv φ₁ φ₂) :
    intEquiv (.snce φ₁ ψ) (.snce φ₂ ψ) := by
  intro M t; constructor
  · rintro ⟨s, hst, hφ, hψ⟩; exact ⟨s, hst, (h M s).mp hφ, hψ⟩
  · rintro ⟨s, hst, hφ, hψ⟩; exact ⟨s, hst, (h M s).mpr hφ, hψ⟩

/-- and congrence on left. -/
theorem and_left_congr {φ₁ φ₂ ψ : Formula Atom} (h : intEquiv φ₁ φ₂) :
    intEquiv (Formula.and φ₁ ψ) (Formula.and φ₂ ψ) := by
  intro M t; constructor
  · intro h'; have ⟨hφ, hψ⟩ := (int_truth_and M t _ _).mp h'
    exact (int_truth_and M t _ _).mpr ⟨(h M t).mp hφ, hψ⟩
  · intro h'; have ⟨hφ, hψ⟩ := (int_truth_and M t _ _).mp h'
    exact (int_truth_and M t _ _).mpr ⟨(h M t).mpr hφ, hψ⟩

/-- Boolean distribution: (a ∨ b) ∧ c ↔ (a ∧ c) ∨ (b ∧ c). -/
theorem and_or_distrib (a b c : Formula Atom) :
    intEquiv (Formula.and (Formula.or a b) c)
              (Formula.or (Formula.and a c) (Formula.and b c)) := by
  intro M t; constructor
  · intro h
    have ⟨hab, hc⟩ := (int_truth_and M t _ _).mp h
    rcases (int_truth_or M t _ _).mp hab with ha | hb
    · exact (int_truth_or M t _ _).mpr (Or.inl ((int_truth_and M t _ _).mpr ⟨ha, hc⟩))
    · exact (int_truth_or M t _ _).mpr (Or.inr ((int_truth_and M t _ _).mpr ⟨hb, hc⟩))
  · intro h
    rcases (int_truth_or M t _ _).mp h with h1 | h2
    · have ⟨ha, hc⟩ := (int_truth_and M t _ _).mp h1
      exact (int_truth_and M t _ _).mpr ⟨(int_truth_or M t _ _).mpr (Or.inl ha), hc⟩
    · have ⟨hb, hc⟩ := (int_truth_and M t _ _).mp h2
      exact (int_truth_and M t _ _).mpr ⟨(int_truth_or M t _ _).mpr (Or.inr hb), hc⟩

/-- Q_Z with negated q argument is U-free. -/
theorem Q_Z_neg_q_U_free (A B q : Formula Atom)
    (hA : isUFree A = true) (hB : isUFree B = true) (hq : isUFree q = true) :
    isUFree (Q_Z A B (Formula.neg q)) = true :=
  Q_Z_U_free A B (Formula.neg q) hA hB (by simp [Formula.neg, isUFree, hq])

/-! ## Replace U(A,B) with False (bot) Infrastructure

When U(A,B) appears only under boolean connectives and ¬U(A,B) holds,
replacing U(A,B) with False (bot) preserves truth.
This enables extracting a U-free event for Case 2 application. -/

/-- Replace all occurrences of `.untl A B` with `bot` (False) in a formula. -/
def replaceUntlWithBot (phi A B : Formula Atom) : Formula Atom :=
  match phi with
  | .atom a => .atom a
  | .bot => .bot
  | .imp p q => .imp (replaceUntlWithBot p A B) (replaceUntlWithBot q A B)
  | .box p => .box (replaceUntlWithBot p A B)
  | .untl p q => if p = A ∧ q = B then .bot else
      .untl (replaceUntlWithBot p A B) (replaceUntlWithBot q A B)
  | .snce p q => .snce (replaceUntlWithBot p A B) (replaceUntlWithBot q A B)

/-- If phi is U-free, replaceUntlWithBot is the identity. -/
theorem replace_bot_id_of_U_free (phi A B : Formula Atom) (h : isUFree phi = true) :
    replaceUntlWithBot phi A B = phi := by
  induction phi with
  | atom _ => rfl | bot => rfl
  | imp p q ihp ihq => simp [isUFree] at h; simp [replaceUntlWithBot, ihp h.1, ihq h.2]
  | box p ih => simp [isUFree] at h; simp [replaceUntlWithBot, ih h]
  | untl _ _ => simp [isUFree] at h
  | snce p q ihp ihq => simp [isUFree] at h; simp [replaceUntlWithBot, ihp h.1, ihq h.2]

/-- replaceUntlWithBot produces U-free result when untlUnderBoolOnly holds. -/
theorem replace_bot_U_free_of_bool (phi A B : Formula Atom)
    (h_bool : untlUnderBoolOnly phi A B) :
    isUFree (replaceUntlWithBot phi A B) = true := by
  induction phi with
  | atom _ => rfl | bot => rfl
  | imp p q ihp ihq =>
    have ⟨hp, hq⟩ := h_bool
    simp [replaceUntlWithBot, isUFree, ihp hp, ihq hq]
  | box p _ =>
    simp only [replaceUntlWithBot]; simp only [isUFree, replace_bot_id_of_U_free p A B h_bool]
    exact h_bool
  | untl p q _ _ =>
    simp only [replaceUntlWithBot]
    rcases h_bool with ⟨rfl, rfl⟩ | h_uf
    · simp [isUFree]
    · simp [isUFree] at h_uf
  | snce p q _ _ =>
    have ⟨hp, hq⟩ := h_bool
    show isUFree (.snce (replaceUntlWithBot p A B) (replaceUntlWithBot q A B)) = true
    simp [isUFree, replace_bot_id_of_U_free p A B hp, replace_bot_id_of_U_free q A B hq, hp, hq]

/-- For formulas where U(A,B) is only under boolean connectives,
    at a time where ¬U(A,B) holds, truth is preserved by replacing U with bot. -/
theorem replace_correct_bot (phi A B : Formula Atom) (M : IntStructure Atom) (t : ℤ)
    (h_bool : untlUnderBoolOnly phi A B)
    (hnotU : ¬ intTruth M t (.untl A B)) :
    intTruth M t phi ↔ intTruth M t (replaceUntlWithBot phi A B) := by
  induction phi generalizing t with
  | atom _ => simp [replaceUntlWithBot]
  | bot => simp [replaceUntlWithBot]
  | imp p q ihp ihq =>
    have ⟨hp, hq⟩ := h_bool
    simp only [replaceUntlWithBot, intTruth]
    exact Iff.imp (ihp t hp hnotU) (ihq t hq hnotU)
  | box _ => simp [replaceUntlWithBot, intTruth]
  | untl p q _ _ =>
    simp only [replaceUntlWithBot]
    rcases h_bool with ⟨rfl, rfl⟩ | h_uf
    · simp only [and_self, ite_true]
      exact ⟨fun h => absurd h hnotU, False.elim⟩
    · simp [isUFree] at h_uf
  | snce p q _ _ =>
    have ⟨hp, hq⟩ := h_bool
    simp only [replaceUntlWithBot, intTruth, replace_bot_id_of_U_free p A B hp,
               replace_bot_id_of_U_free q A B hq]

/-! ## Congruence for ¬U branch -/

/-- If at every time where ¬U(A,B) holds, C₁ ↔ C₂, then
    S(C₁ ∧ ¬U, guard) ↔ S(C₂ ∧ ¬U, guard). -/
theorem snce_event_congr_with_notU (C₁ C₂ guard A B : Formula Atom)
    (h_eq : ∀ M : IntStructure Atom, ∀ t : ℤ, ¬ intTruth M t (.untl A B) →
      (intTruth M t C₁ ↔ intTruth M t C₂)) :
    intEquiv (.snce (Formula.and C₁ (Formula.neg (.untl A B))) guard)
              (.snce (Formula.and C₂ (Formula.neg (.untl A B))) guard) := by
  intro M t; constructor
  · rintro ⟨s, hst, h_event, h_guard⟩
    have ⟨hC₁, hnotU⟩ := (int_truth_and M s _ _).mp h_event
    exact ⟨s, hst, (int_truth_and M s _ _).mpr ⟨(h_eq M s hnotU).mp hC₁, hnotU⟩, h_guard⟩
  · rintro ⟨s, hst, h_event, h_guard⟩
    have ⟨hC₂, hnotU⟩ := (int_truth_and M s _ _).mp h_event
    exact ⟨s, hst, (int_truth_and M s _ _).mpr ⟨(h_eq M s hnotU).mpr hC₂, hnotU⟩, h_guard⟩

/-! ## Core Helper: S(COMBINED ∧ ¬U, guard) Separable -/

/-- S(COMBINED ∧ ¬U(A,B), guard) is separable when COMBINED satisfies
    untlUnderBoolOnly and guard is U-free with S-free A, B.
    Works by replacing U with bot in the event and applying Case 2. -/
theorem snce_combined_notU_separable
    (combined guard : Formula Atom) (A B : Formula Atom)
    (hA : isUFree A = true) (hB : isUFree B = true)
    (hA' : isSFree A = true) (hB' : isSFree B = true)
    (hg_uf : isUFree guard = true)
    (h_bool : untlUnderBoolOnly combined A B) :
    isSeparable (.snce (Formula.and combined (Formula.neg (.untl A B))) guard) := by
  let combined' := replaceUntlWithBot combined A B
  have h_uf : isUFree combined' = true := replace_bot_U_free_of_bool combined A B h_bool
  have h_congr := snce_event_congr_with_notU combined combined' guard A B
    (fun M t hnotU => replace_correct_bot combined A B M t h_bool hnotU)
  apply is_separable_of_equiv h_congr
  obtain ⟨psi, hequiv, hsep⟩ := elim_case_2_gen combined' guard A B h_uf hg_uf hA hB hA' hB'
  exact ⟨psi, hsep, hequiv⟩

/-! ## D2.1 Explicit Formula for D3

The separated equivalent of S(alpha, Q_Z) needs to be constructed explicitly
(not just existentially) so we can prove it satisfies untlUnderBoolOnly.
This is needed for the D3 proof where S(alpha, Q_Z) appears inside the event. -/

/-- The explicit separated equivalent of S(alpha, Q_Z) from D2.1.
    = or (case1_psi a Q_Z_nq A B) (case1_psi (replaceUntlWithTop (¬q ∧ σ) A B) Q_Z_nq A B)
    where σ = case1_psi a q A B and Q_Z_nq = Q_Z A B (neg q). -/
def d21_sep (a q A B : Formula Atom) : Formula Atom :=
  let σ := case1_psi a q A B
  let Q_Z_nq := Q_Z A B (Formula.neg q)
  Formula.or
    (case1_psi a Q_Z_nq A B)
    (case1_psi (replaceUntlWithTop (Formula.and (Formula.neg q) σ) A B) Q_Z_nq A B)

/-- d21_sep satisfies untlUnderBoolOnly. -/
theorem d21_sep_bool_only (a q A B : Formula Atom)
    (ha : isUFree a = true) (hq : isUFree q = true)
    (hA : isUFree A = true) (hB : isUFree B = true) :
    untlUnderBoolOnly (d21_sep a q A B) A B := by
  have h_or : ∀ p q, untlUnderBoolOnly p A B → untlUnderBoolOnly q A B →
      untlUnderBoolOnly (Formula.or p q) A B := by
    intro p q hp hq; show untlUnderBoolOnly (.imp (.imp p .bot) q) A B
    exact ⟨⟨hp, trivial⟩, hq⟩
  unfold d21_sep
  apply h_or
  · exact case1_psi_bool_only a (Q_Z A B (Formula.neg q)) A B ha
      (Q_Z_neg_q_U_free A B q hA hB hq) hA hB
  · have h_nqσ_bool : untlUnderBoolOnly (Formula.and (Formula.neg q) (case1_psi a q A B)) A B := by
      show untlUnderBoolOnly (.imp (.imp (Formula.neg q) (.imp (case1_psi a q A B) .bot)) .bot) A B
      refine ⟨⟨?_, case1_psi_bool_only a q A B ha hq hA hB, trivial⟩, trivial⟩
      exact ⟨u_free_untl_under_bool q A B hq, trivial⟩
    have h_replaced_uf : isUFree (replaceUntlWithTop (Formula.and (Formula.neg q) (case1_psi a q A B)) A B) = true :=
      replace_U_free_of_bool _ A B h_nqσ_bool
    exact case1_psi_bool_only
      (replaceUntlWithTop (Formula.and (Formula.neg q) (case1_psi a q A B)) A B)
      (Q_Z A B (Formula.neg q)) A B h_replaced_uf
      (Q_Z_neg_q_U_free A B q hA hB hq) hA hB

set_option maxHeartbeats 3200000 in
/-- d21_sep is intEquiv to S(alpha, Q_Z) where alpha = case3_alpha(a∧U, q, A, B).
    This non-existential form allows using d21_sep in D3's event. -/
theorem d21_sep_equiv (a q A B : Formula Atom)
    (ha : isUFree a = true) (hq : isUFree q = true)
    (hA : isUFree A = true) (hB : isUFree B = true)
    (hA' : isSFree A = true) (hB' : isSFree B = true) :
    intEquiv (.snce (case3_alpha (Formula.and a (.untl A B)) q A B) (Q_Z A B (Formula.neg q)))
              (d21_sep a q A B) := by
  -- Step 1: alpha ↔ (a ∨ (¬q ∧ S(a∧U,q))) ∧ U
  have step1 : intEquiv
    (.snce (case3_alpha (Formula.and a (.untl A B)) q A B) (Q_Z A B (Formula.neg q)))
    (.snce (Formula.and (Formula.or a (Formula.and (Formula.neg q) (.snce (Formula.and a (.untl A B)) q))) (.untl A B)) (Q_Z A B (Formula.neg q))) :=
    snce_event_congr (case3_alpha_aU_factor a q A B)
  -- Step 2: Distribute → S(a∧U, Q_Z) ∨ S((¬q∧S(a∧U,q))∧U, Q_Z)
  have step2 : intEquiv
    (.snce (Formula.and (Formula.or a (Formula.and (Formula.neg q) (.snce (Formula.and a (.untl A B)) q))) (.untl A B)) (Q_Z A B (Formula.neg q)))
    (Formula.or (.snce (Formula.and a (.untl A B)) (Q_Z A B (Formula.neg q)))
                (.snce (Formula.and (Formula.and (Formula.neg q) (.snce (Formula.and a (.untl A B)) q)) (.untl A B)) (Q_Z A B (Formula.neg q)))) :=
    int_equiv_trans
      (snce_event_congr (and_or_distrib a
        (Formula.and (Formula.neg q) (.snce (Formula.and a (.untl A B)) q))
        (.untl A B)))
      (since_distrib_or_left _ _ (Q_Z A B (Formula.neg q)))
  have steps12 := int_equiv_trans step1 step2
  -- Now: S(alpha, Q_Z) ↔ S(a∧U, Q_Z) ∨ S((¬q∧S(a∧U,q))∧U, Q_Z)
  -- Step 3: Replace S(a∧U,q) with σ = case1_psi
  let σ := case1_psi a q A B
  have hσ_equiv : intEquiv (.snce (Formula.and a (.untl A B)) q) σ :=
    (case1_psi_properties a q A B ha hq hA hB hA' hB').1
  have hY_congr : intEquiv
    (Formula.and (Formula.neg q) (.snce (Formula.and a (.untl A B)) q))
    (Formula.and (Formula.neg q) σ) := by
    intro M t; constructor
    · intro h; have ⟨hnq, hS⟩ := (int_truth_and M t _ _).mp h
      exact (int_truth_and M t _ _).mpr ⟨hnq, (hσ_equiv M t).mp hS⟩
    · intro h; have ⟨hnq, hσ'⟩ := (int_truth_and M t _ _).mp h
      exact (int_truth_and M t _ _).mpr ⟨hnq, (hσ_equiv M t).mpr hσ'⟩
  have step3 : intEquiv
    (.snce (Formula.and (Formula.and (Formula.neg q) (.snce (Formula.and a (.untl A B)) q)) (.untl A B))
           (Q_Z A B (Formula.neg q)))
    (.snce (Formula.and (Formula.and (Formula.neg q) σ) (.untl A B))
           (Q_Z A B (Formula.neg q))) :=
    snce_event_congr (and_left_congr hY_congr)
  -- Step 4: Replace U with True in event of each disjunct
  let Q_Z_nq := Q_Z A B (Formula.neg q)
  have hQ_uf : isUFree Q_Z_nq = true := Q_Z_neg_q_U_free A B q hA hB hq
  -- For S(a∧U, Q_Z): a is U-free → replace a with a (identity) → case1_psi a Q_Z A B
  have h_a_congr : ∀ M : IntStructure Atom, ∀ t : ℤ, intTruth M t (.untl A B) →
      (intTruth M t a ↔ intTruth M t (replaceUntlWithTop a A B)) :=
    fun M t _ => by rw [replace_id_of_U_free a A B ha]
  have step4a_congr := snce_event_congr_with_U a (replaceUntlWithTop a A B) Q_Z_nq A B h_a_congr
  have h_a_uf : isUFree (replaceUntlWithTop a A B) = true := by
    rw [replace_id_of_U_free a A B ha]; exact ha
  have step4a := (case1_psi_properties (replaceUntlWithTop a A B) Q_Z_nq A B
    h_a_uf hQ_uf hA hB hA' hB').1
  have step4a_full : intEquiv
    (.snce (Formula.and a (.untl A B)) Q_Z_nq) (case1_psi a Q_Z_nq A B) := by
    have : replaceUntlWithTop a A B = a := replace_id_of_U_free a A B ha
    rw [this] at step4a step4a_congr
    exact int_equiv_trans step4a_congr step4a
  -- For S((¬q∧σ)∧U, Q_Z): (¬q∧σ) satisfies untlUnderBoolOnly
  have h_nqσ_bool : untlUnderBoolOnly (Formula.and (Formula.neg q) σ) A B := by
    show untlUnderBoolOnly (.imp (.imp (Formula.neg q) (.imp σ .bot)) .bot) A B
    refine ⟨⟨?_, case1_psi_bool_only a q A B ha hq hA hB, trivial⟩, trivial⟩
    exact ⟨u_free_untl_under_bool q A B hq, trivial⟩
  let nqσ' := replaceUntlWithTop (Formula.and (Formula.neg q) σ) A B
  have h_nqσ_congr : ∀ M : IntStructure Atom, ∀ t : ℤ, intTruth M t (.untl A B) →
      (intTruth M t (Formula.and (Formula.neg q) σ) ↔ intTruth M t nqσ') :=
    fun M t hU => replace_correct_bool _ A B M t h_nqσ_bool hU
  have step4b_congr := snce_event_congr_with_U _ nqσ' Q_Z_nq A B h_nqσ_congr
  have h_nqσ_uf : isUFree nqσ' = true := replace_U_free_of_bool _ A B h_nqσ_bool
  have step4b := (case1_psi_properties nqσ' Q_Z_nq A B h_nqσ_uf hQ_uf hA hB hA' hB').1
  have step4b_full : intEquiv
    (.snce (Formula.and (Formula.and (Formula.neg q) σ) (.untl A B)) Q_Z_nq)
    (case1_psi nqσ' Q_Z_nq A B) :=
    int_equiv_trans step4b_congr step4b
  -- Combine: S(alpha, Q_Z) ↔ case1_psi a Q_Z A B ∨ case1_psi nqσ' Q_Z A B = d21_sep
  intro M t; constructor
  · intro h
    have h12 := (steps12 M t).mp h
    rcases (int_truth_or M t _ _).mp h12 with h1 | h2
    · exact (int_truth_or M t _ _).mpr (Or.inl ((step4a_full M t).mp h1))
    · have h2' := (step3 M t).mp h2
      exact (int_truth_or M t _ _).mpr (Or.inr ((step4b_full M t).mp h2'))
  · intro h
    rcases (int_truth_or M t _ _).mp h with h1 | h2
    · exact (steps12 M t).mpr ((int_truth_or M t _ _).mpr (Or.inl ((step4a_full M t).mpr h1)))
    · have h2' := (step4b_full M t).mpr h2
      exact (steps12 M t).mpr ((int_truth_or M t _ _).mpr (Or.inr ((step3 M t).mpr h2')))

/-! ## Core Helper: S(COMBINED ∧ U, guard) Separable -/

/-- S(COMBINED ∧ U(A,B), guard) is separable when COMBINED satisfies
    untlUnderBoolOnly and guard is U-free with S-free A, B.
    Works by replacing U with True in the event and applying Case 1. -/
theorem snce_combined_U_separable
    (combined guard : Formula Atom) (A B : Formula Atom)
    (hA : isUFree A = true) (hB : isUFree B = true)
    (hA' : isSFree A = true) (hB' : isSFree B = true)
    (hg_uf : isUFree guard = true)
    (h_bool : untlUnderBoolOnly combined A B) :
    isSeparable (.snce (Formula.and combined (.untl A B)) guard) := by
  let combined' := replaceUntlWithTop combined A B
  have h_uf : isUFree combined' = true := replace_U_free_of_bool combined A B h_bool
  have h_congr := snce_event_congr_with_U combined combined' guard A B
    (fun M t hU => replace_correct_bool combined A B M t h_bool hU)
  apply is_separable_of_equiv h_congr
  obtain ⟨psi, hequiv, hsep⟩ := elim_case_1_gen combined' guard A B h_uf hg_uf hA hB hA' hB'
  exact ⟨psi, hsep, hequiv⟩

/-! ## Cases 5-8 Separability -/

set_option maxHeartbeats 1600000 in
/-- Generalized Case 5: S(a ^ U(A,B), q v U(A,B)) is separable.
    Drops S-free requirements on a and q (only A, B need S-freeness).
    The proof only uses S-freeness of A and B. -/
theorem case5_separable_Z_gen (a q A B : Formula Atom)
    (ha : isUFree a = true) (hq : isUFree q = true)
    (hA : isUFree A = true) (hB : isUFree B = true)
    (hA' : isSFree A = true) (hB' : isSFree B = true) :
    isSeparable (.snce (Formula.and a (.untl A B)) (Formula.or q (.untl A B))) := by
  -- Same proof as case5_separable_Z but without ha'/hq'
  apply is_separable_of_equiv (case3_equiv_Z_general (Formula.and a (.untl A B)) q A B)
  simp only [case3_rhs]
  apply or_separable
  · apply or_separable
    · obtain ⟨psi, hequiv_psi, hsep_psi⟩ := elim_case_1_gen a q A B ha hq hA hB hA' hB'
      exact ⟨psi, hsep_psi, hequiv_psi⟩
    · apply and_separable
      · apply is_separable_of_equiv (snce_event_congr (case3_alpha_aU_factor a q A B))
        apply is_separable_of_equiv (int_equiv_trans
          (snce_event_congr (and_or_distrib a
            (Formula.and (Formula.neg q) (.snce (Formula.and a (.untl A B)) q))
            (.untl A B)))
          (since_distrib_or_left _ _ (Q_Z A B (Formula.neg q))))
        apply or_separable
        · exact snce_combined_U_separable a (Q_Z A B (Formula.neg q)) A B
            hA hB hA' hB' (Q_Z_neg_q_U_free A B q hA hB hq)
            (u_free_untl_under_bool a A B ha)
        · let σ := case1_psi a q A B
          have hσ_equiv : intEquiv (.snce (Formula.and a (.untl A B)) q) σ :=
            (case1_psi_properties a q A B ha hq hA hB hA' hB').1
          have hY_congr : intEquiv
            (Formula.and (Formula.neg q) (.snce (Formula.and a (.untl A B)) q))
            (Formula.and (Formula.neg q) σ) := by
            intro M t; constructor
            · intro h; have ⟨hnq, hS⟩ := (int_truth_and M t _ _).mp h
              exact (int_truth_and M t _ _).mpr ⟨hnq, (hσ_equiv M t).mp hS⟩
            · intro h; have ⟨hnq, hσ'⟩ := (int_truth_and M t _ _).mp h
              exact (int_truth_and M t _ _).mpr ⟨hnq, (hσ_equiv M t).mpr hσ'⟩
          apply is_separable_of_equiv (snce_event_congr (and_left_congr hY_congr))
          have h_nqσ_bool : untlUnderBoolOnly (Formula.and (Formula.neg q) σ) A B := by
            show untlUnderBoolOnly (.imp (.imp (Formula.neg q) (.imp σ .bot)) .bot) A B
            refine ⟨⟨?_, case1_psi_bool_only a q A B ha hq hA hB, trivial⟩, trivial⟩
            exact ⟨u_free_untl_under_bool q A B hq, trivial⟩
          exact snce_combined_U_separable (Formula.and (Formula.neg q) σ)
            (Q_Z A B (Formula.neg q)) A B hA hB hA' hB'
            (Q_Z_neg_q_U_free A B q hA hB hq) h_nqσ_bool
      · apply or_separable
        · exact u_free_s_free_is_separable A hA hA'
        · exact and_separable
            (u_free_s_free_is_separable B hB hB')
            ⟨.untl A B, by simp [isSyntacticallySeparated, hA', hB'], int_equiv_refl _⟩
  · have h_d21 := d21_sep_equiv a q A B ha hq hA hB hA' hB'
    have h_event_congr : intEquiv
      (Formula.and (Formula.and A (Formula.or q (.untl A B)))
        (.snce (case3_alpha (Formula.and a (.untl A B)) q A B) (Q_Z A B (Formula.neg q))))
      (Formula.and (Formula.and A (Formula.or q (.untl A B))) (d21_sep a q A B)) := by
      intro M t; constructor
      · intro h; have ⟨hAqU, hS⟩ := (int_truth_and M t _ _).mp h
        exact (int_truth_and M t _ _).mpr ⟨hAqU, (h_d21 M t).mp hS⟩
      · intro h; have ⟨hAqU, hd⟩ := (int_truth_and M t _ _).mp h
        exact (int_truth_and M t _ _).mpr ⟨hAqU, (h_d21 M t).mpr hd⟩
    apply is_separable_of_equiv (snce_event_congr h_event_congr)
    apply is_separable_of_equiv (since_event_split _ (.untl A B) q)
    apply or_separable
    · have h_event_bool : untlUnderBoolOnly
          (Formula.and (Formula.and A (Formula.or q (.untl A B))) (d21_sep a q A B)) A B := by
        show untlUnderBoolOnly (.imp (.imp (Formula.and A (Formula.or q (.untl A B)))
          (.imp (d21_sep a q A B) .bot)) .bot) A B
        refine ⟨⟨?_, d21_sep_bool_only a q A B ha hq hA hB, trivial⟩, trivial⟩
        show untlUnderBoolOnly (.imp (.imp A (.imp (Formula.or q (.untl A B)) .bot)) .bot) A B
        refine ⟨⟨u_free_untl_under_bool A A B hA, ?_, trivial⟩, trivial⟩
        show untlUnderBoolOnly (.imp (.imp q .bot) (.untl A B)) A B
        exact ⟨⟨u_free_untl_under_bool q A B hq, trivial⟩, Or.inl ⟨rfl, rfl⟩⟩
      exact snce_combined_U_separable
        (Formula.and (Formula.and A (Formula.or q (.untl A B))) (d21_sep a q A B))
        q A B hA hB hA' hB' hq h_event_bool
    · have h_event_bool : untlUnderBoolOnly
          (Formula.and (Formula.and A (Formula.or q (.untl A B))) (d21_sep a q A B)) A B := by
        show untlUnderBoolOnly (.imp (.imp (Formula.and A (Formula.or q (.untl A B)))
          (.imp (d21_sep a q A B) .bot)) .bot) A B
        refine ⟨⟨?_, d21_sep_bool_only a q A B ha hq hA hB, trivial⟩, trivial⟩
        show untlUnderBoolOnly (.imp (.imp A (.imp (Formula.or q (.untl A B)) .bot)) .bot) A B
        refine ⟨⟨u_free_untl_under_bool A A B hA, ?_, trivial⟩, trivial⟩
        show untlUnderBoolOnly (.imp (.imp q .bot) (.untl A B)) A B
        exact ⟨⟨u_free_untl_under_bool q A B hq, trivial⟩, Or.inl ⟨rfl, rfl⟩⟩
      exact snce_combined_notU_separable
        (Formula.and (Formula.and A (Formula.or q (.untl A B))) (d21_sep a q A B))
        q A B hA hB hA' hB' hq h_event_bool

theorem case5_separable_Z (a q A B : Formula Atom)
    (ha : isUFree a = true) (hq : isUFree q = true)
    (hA : isUFree A = true) (hB : isUFree B = true)
    (_ha' : isSFree a = true) (_hq' : isSFree q = true)
    (hA' : isSFree A = true) (hB' : isSFree B = true) :
    isSeparable (.snce (Formula.and a (.untl A B)) (Formula.or q (.untl A B))) :=
  case5_separable_Z_gen a q A B ha hq hA hB hA' hB'

/-! ## Case 6 Infrastructure

Case 6: S(a∧¬U(A,B), q∨U(A,B)) where a,q,A,B are U-free and S-free.

Strategy: Decompose ¬U ↔ G(¬A) ∨ U' using neg_until_equiv where U' = U(¬A∧¬B, ¬A).
Split into two branches:
  Branch A: S(a∧G(¬A), q∨U) -- event is U-free, handled by case5_separable_Z_gen
  Branch B: S(a∧U', q∨U)   -- uses case3_equiv + U∧U'=⊥ contradiction to reduce

Key lemma: U(A,B) and U(¬A∧¬B, ¬A) cannot both hold at the same time.
When U(A,B) holds at an event point, the U'-containing parts of any separated
equivalent of S(a∧U', q) vanish, leaving only U-free components. -/

/-- U(A,B) and U(¬A∧¬B, ¬A) are contradictory: they cannot both hold at the same time.
    Proof: if U(A,B)(t) gives witness s₁ > t with A(s₁)∧B on (t,s₁), and
    U(¬A∧¬B, ¬A)(t) gives witness s₂ > t with (¬A∧¬B)(s₂)∧(¬A) on (t,s₂), then
    s₁ < s₂ → ¬A(s₁) contradicts A(s₁); s₁ = s₂ → same; s₁ > s₂ → B(s₂) contradicts ¬B(s₂). -/
theorem untl_neguntl_contradictory (A B : Formula Atom) (M : IntStructure Atom) (t : ℤ)
    (hU : intTruth M t (.untl A B))
    (hU' : intTruth M t (.untl (Formula.and (Formula.neg A) (Formula.neg B)) (Formula.neg A))) :
    False := by
  obtain ⟨s₁, hts₁, hA₁, hB₁⟩ := hU
  obtain ⟨s₂, hts₂, hAB₂, hA₂⟩ := hU'
  -- hAB₂ : intTruth M s₂ (and (neg A) (neg B))
  -- Extract ¬A(s₂) and ¬B(s₂)
  have hnotA₂ : ¬ intTruth M s₂ A := fun h => hAB₂ (fun hna _ => hna h)
  have hnotB₂ : ¬ intTruth M s₂ B := fun h => hAB₂ (fun _ hnb => hnb h)
  rcases lt_trichotomy s₁ s₂ with h | h | h
  · -- s₁ < s₂: s₁ ∈ (t, s₂), guard gives ¬A(s₁), but A(s₁)
    exact hA₂ s₁ hts₁ h hA₁
  · -- s₁ = s₂: A(s₁) = A(s₂), contradicts ¬A(s₂)
    exact hnotA₂ (h ▸ hA₁)
  · -- s₁ > s₂: s₂ ∈ (t, s₁), guard gives B(s₂), but ¬B(s₂)
    exact hnotB₂ (hB₁ s₂ hts₂ h)

/-- Negation equivalence specialized: ¬U → G(¬A) ∨ U', as an intEquiv on the event. -/
theorem neg_untl_event_equiv (a A B : Formula Atom) :
    intEquiv (Formula.and a (Formula.neg (.untl A B)))
      (Formula.or (Formula.and a (.allFuture (Formula.neg A)))
        (Formula.and a (.untl (Formula.and (Formula.neg A) (Formula.neg B)) (Formula.neg A)))) := by
  intro M t; constructor
  · intro h
    have ⟨ha, hnotU⟩ := (int_truth_and M t _ _).mp h
    rcases (int_truth_or M t _ _).mp ((neg_until_equiv A B M t).mp hnotU) with hG | hU'
    · exact (int_truth_or M t _ _).mpr (Or.inl ((int_truth_and M t _ _).mpr ⟨ha, hG⟩))
    · exact (int_truth_or M t _ _).mpr (Or.inr ((int_truth_and M t _ _).mpr ⟨ha, hU'⟩))
  · intro h
    rcases (int_truth_or M t _ _).mp h with h1 | h2
    · have ⟨ha, hG⟩ := (int_truth_and M t _ _).mp h1
      exact (int_truth_and M t _ _).mpr ⟨ha,
        (neg_until_equiv A B M t).mpr ((int_truth_or M t _ _).mpr (Or.inl hG))⟩
    · have ⟨ha, hU'⟩ := (int_truth_and M t _ _).mp h2
      exact (int_truth_and M t _ _).mpr ⟨ha,
        (neg_until_equiv A B M t).mpr ((int_truth_or M t _ _).mpr (Or.inr hU'))⟩

set_option maxHeartbeats 3200000 in
/-- S(ev, q∨U) is separable when ev is U-free.
    This is the core of Branch A and is like case5_separable_Z_gen but with
    the event already U-free (no U in the event), making it simpler. -/
theorem snce_Ufree_event_qU_guard_separable (ev q A B : Formula Atom)
    (hev_uf : isUFree ev = true) (hq : isUFree q = true)
    (hA : isUFree A = true) (hB : isUFree B = true)
    (hA' : isSFree A = true) (hB' : isSFree B = true) :
    isSeparable (.snce ev (Formula.or q (.untl A B))) := by
  apply is_separable_of_equiv (case3_equiv_Z_general ev q A B)
  simp only [case3_rhs]
  have hQ_uf : isUFree (Q_Z A B (Formula.neg q)) = true :=
    Q_Z_neg_q_U_free A B q hA hB hq
  -- D1: S(ev, q) -- U-free event and guard → syntactically separated
  -- D2: S(alpha, Q_Z) ∧ (A∨B∧U)
  -- D3: S(A ∧ (q∨U) ∧ S(alpha, Q_Z), q)
  -- alpha = ev ∨ ((¬q ∧ S(ev,q)) ∧ (q∨U))
  -- Since ev is U-free: alpha has U only in (q∨U) → untlUnderBoolOnly
  have h_nqSev_uf : isUFree (Formula.and (Formula.neg q) (.snce ev q)) = true := by
    simp [Formula.and, Formula.neg, isUFree, hq, hev_uf]
  -- alpha = ev ∨ (nqSev ∧ (q∨U)) where nqSev = ¬q∧S(ev,q) is U-free
  -- S(alpha, Q_Z): distribute via since_distrib_or_left
  -- then event-split the second disjunct on U
  -- Key helper: S(alpha, Q_Z) separable
  have h_Salpha_sep : isSeparable (.snce (case3_alpha ev q A B) (Q_Z A B (Formula.neg q))) := by
    apply is_separable_of_equiv (since_distrib_or_left _ _ (Q_Z A B (Formula.neg q)))
    apply or_separable
    · exact ⟨.snce ev (Q_Z A B (Formula.neg q)),
        by simp [isSyntacticallySeparated, hev_uf, hQ_uf], int_equiv_refl _⟩
    · apply is_separable_of_equiv (since_event_split _ (.untl A B) (Q_Z A B (Formula.neg q)))
      apply or_separable
      · -- U branch
        apply is_separable_of_equiv (snce_event_congr_with_U _ _ _ A B
          (fun M t hU => ⟨fun h => ((int_truth_and M t _ _).mp h).1,
            fun h => (int_truth_and M t _ _).mpr ⟨h, (int_truth_or M t _ _).mpr (Or.inr hU)⟩⟩))
        exact snce_combined_U_separable (Formula.and (Formula.neg q) (.snce ev q))
          (Q_Z A B (Formula.neg q)) A B hA hB hA' hB' hQ_uf
          (u_free_untl_under_bool _ A B h_nqSev_uf)
      · -- ¬U branch: ¬q∧q = ⊥
        apply is_separable_of_equiv (by
          intro M t; constructor
          · rintro ⟨s, _, h_event, _⟩
            have ⟨h_left, h_notU⟩ := (int_truth_and M s _ _).mp h_event
            have ⟨h_nqS, h_qU⟩ := (int_truth_and M s _ _).mp h_left
            have h_nq := ((int_truth_and M s _ _).mp h_nqS).1
            rcases (int_truth_or M s _ _).mp h_qU with hq' | hU
            · exact h_nq hq'
            · exact h_notU hU
          · intro h; exact h.elim : intEquiv _ .bot)
        exact ⟨.bot, by simp [isSyntacticallySeparated], int_equiv_refl _⟩
  apply or_separable
  · apply or_separable
    · -- D1
      exact ⟨.snce ev q, by simp [isSyntacticallySeparated, hev_uf, hq], int_equiv_refl _⟩
    · -- D2
      apply and_separable
      · exact h_Salpha_sep
      · apply or_separable
        · exact u_free_s_free_is_separable A hA hA'
        · exact and_separable (u_free_s_free_is_separable B hB hB')
            ⟨.untl A B, by simp [isSyntacticallySeparated, hA', hB'], int_equiv_refl _⟩
  · -- D3: S(A ∧ (q∨U) ∧ S(alpha, Q_Z), q)
    -- Use d21_sep-style infrastructure: alpha has untlUnderBoolOnly
    -- The alpha for U-free ev: same structure as Case 5 but simpler
    -- alpha satisfies untlUnderBoolOnly because ev is U-free
    have h_alpha_bool : untlUnderBoolOnly (case3_alpha ev q A B) A B := by
      show untlUnderBoolOnly (Formula.or ev (Formula.and (Formula.and (Formula.neg q)
        (.snce ev q)) (Formula.or q (.untl A B)))) A B
      have h_or : ∀ p q, untlUnderBoolOnly p A B → untlUnderBoolOnly q A B →
          untlUnderBoolOnly (Formula.or p q) A B := by
        intro p q hp hq; show untlUnderBoolOnly (.imp (.imp p .bot) q) A B
        exact ⟨⟨hp, trivial⟩, hq⟩
      have h_and : ∀ p q, untlUnderBoolOnly p A B → untlUnderBoolOnly q A B →
          untlUnderBoolOnly (Formula.and p q) A B := by
        intro p q hp hq; show untlUnderBoolOnly (.imp (.imp p (.imp q .bot)) .bot) A B
        exact ⟨⟨hp, hq, trivial⟩, trivial⟩
      apply h_or
      · exact u_free_untl_under_bool ev A B hev_uf
      · apply h_and
        · apply h_and
          · exact ⟨u_free_untl_under_bool q A B hq, trivial⟩
          · exact ⟨hev_uf, hq⟩
        · exact ⟨⟨u_free_untl_under_bool q A B hq, trivial⟩, Or.inl ⟨rfl, rfl⟩⟩
    -- Get explicit separated equiv of S(alpha, Q_Z) satisfying untlUnderBoolOnly
    -- For this, build a d21-sep analog. The alpha for U-free ev factors as:
    -- alpha = ev ∨ ((¬q ∧ S(ev, q)) ∧ (q∨U))
    -- = (ev ∧ (q∨U)) ∨ ((¬q ∧ S(ev,q)) ∧ (q∨U))   (since ev doesn't involve U; actually false)
    -- No, we can't factor out (q∨U) because ev doesn't imply anything about (q∨U).
    -- Instead, distribute: S(alpha, Q_Z) ↔ S(ev, Q_Z) ∨ S(nqSev∧(q∨U), Q_Z)
    -- S(ev, Q_Z) is U-free → its separated equiv is U-free → untlUnderBoolOnly trivially
    -- S(nqSev∧(q∨U), Q_Z) after event-split:
    --   U branch → S(nqSev∧U, Q_Z) → snce_combined_U_separable → case1_psi(nqSev, Q_Z, A, B)
    --   ¬U branch → empty
    -- case1_psi(nqSev, Q_Z, A, B) satisfies case1_psi_bool_only → untlUnderBoolOnly
    -- So the or of these satisfies untlUnderBoolOnly.
    -- Define explicit d21_sep for this case:
    let d21_6A := Formula.or (.snce ev (Q_Z A B (Formula.neg q)))
      (case1_psi (Formula.and (Formula.neg q) (.snce ev q)) (Q_Z A B (Formula.neg q)) A B)
    -- Show d21_6A satisfies untlUnderBoolOnly
    have h_d21_bool : untlUnderBoolOnly d21_6A A B := by
      have h_or : ∀ p q, untlUnderBoolOnly p A B → untlUnderBoolOnly q A B →
          untlUnderBoolOnly (Formula.or p q) A B := by
        intro p q hp hq; exact ⟨⟨hp, trivial⟩, hq⟩
      apply h_or
      · -- S(ev, Q_Z): U-free args → untlUnderBoolOnly for snce
        exact ⟨hev_uf, hQ_uf⟩
      · exact case1_psi_bool_only _ _ A B h_nqSev_uf hQ_uf hA hB
    -- Show d21_6A is intEquiv to S(alpha, Q_Z)
    have h_d21_equiv : intEquiv (.snce (case3_alpha ev q A B) (Q_Z A B (Formula.neg q))) d21_6A := by
      -- S(alpha, Q_Z) ↔ S(ev, Q_Z) ∨ S((¬q∧S(ev,q))∧(q∨U), Q_Z) via distribute
      -- S((¬q∧S(ev,q))∧(q∨U), Q_Z) ↔ S((¬q∧S(ev,q))∧U, Q_Z) ∨ ⊥ via event-split
      -- S((¬q∧S(ev,q))∧U, Q_Z) ↔ case1_psi via snce_event_congr_with_U + case1_psi_properties
      have h_step1 := since_distrib_or_left ev
        (Formula.and (Formula.and (Formula.neg q) (.snce ev q)) (Formula.or q (.untl A B)))
        (Q_Z A B (Formula.neg q))
      have h_step2 := since_event_split
        (Formula.and (Formula.and (Formula.neg q) (.snce ev q)) (Formula.or q (.untl A B)))
        (.untl A B) (Q_Z A B (Formula.neg q))
      have h_congr_U := snce_event_congr_with_U
        (Formula.and (Formula.and (Formula.neg q) (.snce ev q)) (Formula.or q (.untl A B)))
        (Formula.and (Formula.neg q) (.snce ev q))
        (Q_Z A B (Formula.neg q)) A B
        (fun M t hU => ⟨fun h => ((int_truth_and M t _ _).mp h).1,
          fun h => (int_truth_and M t _ _).mpr ⟨h, (int_truth_or M t _ _).mpr (Or.inr hU)⟩⟩)
      have h_psi := (case1_psi_properties (Formula.and (Formula.neg q) (.snce ev q))
        (Q_Z A B (Formula.neg q)) A B h_nqSev_uf hQ_uf hA hB hA' hB').1
      intro M t; constructor
      · intro h
        have h12 := (h_step1 M t).mp h
        rcases (int_truth_or M t _ _).mp h12 with h1 | h2
        · exact (int_truth_or M t _ _).mpr (Or.inl h1)
        · have h_split := (h_step2 M t).mp h2
          rcases (int_truth_or M t _ _).mp h_split with hU_br | hnotU_br
          · exact (int_truth_or M t _ _).mpr (Or.inr ((h_psi M t).mp ((h_congr_U M t).mp hU_br)))
          · -- ¬U branch: contradiction ¬q∧q
            exfalso
            obtain ⟨s, _, h_event, _⟩ := hnotU_br
            have ⟨h_left, h_notU⟩ := (int_truth_and M s _ _).mp h_event
            have ⟨h_nqS, h_qU⟩ := (int_truth_and M s _ _).mp h_left
            rcases (int_truth_or M s _ _).mp h_qU with hq' | hU
            · exact ((int_truth_and M s _ _).mp h_nqS).1 hq'
            · exact h_notU hU
      · intro h
        rcases (int_truth_or M t _ _).mp h with h1 | h2
        · exact (h_step1 M t).mpr ((int_truth_or M t _ _).mpr (Or.inl h1))
        · have h_combined := (h_congr_U M t).mpr ((h_psi M t).mpr h2)
          have h_unsplit := (h_step2 M t).mpr ((int_truth_or M t _ _).mpr (Or.inl h_combined))
          exact (h_step1 M t).mpr ((int_truth_or M t _ _).mpr (Or.inr h_unsplit))
    -- Now handle D3 using d21_6A
    have h_event_congr : intEquiv
      (Formula.and (Formula.and A (Formula.or q (.untl A B)))
        (.snce (case3_alpha ev q A B) (Q_Z A B (Formula.neg q))))
      (Formula.and (Formula.and A (Formula.or q (.untl A B))) d21_6A) := by
      intro M t; constructor
      · intro h; have ⟨hAqU, hS⟩ := (int_truth_and M t _ _).mp h
        exact (int_truth_and M t _ _).mpr ⟨hAqU, (h_d21_equiv M t).mp hS⟩
      · intro h; have ⟨hAqU, hd⟩ := (int_truth_and M t _ _).mp h
        exact (int_truth_and M t _ _).mpr ⟨hAqU, (h_d21_equiv M t).mpr hd⟩
    apply is_separable_of_equiv (snce_event_congr h_event_congr)
    apply is_separable_of_equiv (since_event_split _ (.untl A B) q)
    apply or_separable
    · -- U branch
      have h_event_bool : untlUnderBoolOnly
          (Formula.and (Formula.and A (Formula.or q (.untl A B))) d21_6A) A B := by
        show untlUnderBoolOnly (.imp (.imp (Formula.and A (Formula.or q (.untl A B)))
          (.imp d21_6A .bot)) .bot) A B
        refine ⟨⟨?_, h_d21_bool, trivial⟩, trivial⟩
        show untlUnderBoolOnly (.imp (.imp A (.imp (Formula.or q (.untl A B)) .bot)) .bot) A B
        refine ⟨⟨u_free_untl_under_bool A A B hA, ?_, trivial⟩, trivial⟩
        exact ⟨⟨u_free_untl_under_bool q A B hq, trivial⟩, Or.inl ⟨rfl, rfl⟩⟩
      exact snce_combined_U_separable
        (Formula.and (Formula.and A (Formula.or q (.untl A B))) d21_6A)
        q A B hA hB hA' hB' hq h_event_bool
    · -- ¬U branch
      have h_event_bool : untlUnderBoolOnly
          (Formula.and (Formula.and A (Formula.or q (.untl A B))) d21_6A) A B := by
        show untlUnderBoolOnly (.imp (.imp (Formula.and A (Formula.or q (.untl A B)))
          (.imp d21_6A .bot)) .bot) A B
        refine ⟨⟨?_, h_d21_bool, trivial⟩, trivial⟩
        show untlUnderBoolOnly (.imp (.imp A (.imp (Formula.or q (.untl A B)) .bot)) .bot) A B
        refine ⟨⟨u_free_untl_under_bool A A B hA, ?_, trivial⟩, trivial⟩
        exact ⟨⟨u_free_untl_under_bool q A B hq, trivial⟩, Or.inl ⟨rfl, rfl⟩⟩
      exact snce_combined_notU_separable
        (Formula.and (Formula.and A (Formula.or q (.untl A B))) d21_6A)
        q A B hA hB hA' hB' hq h_event_bool

/-! ### Case 6 via GHR94 Direct Formula (10.2.3 item 6)

GHR94 approach: S(a∧¬U, q∨U). Consider the past time s indicated by S. At s,
a(s) and ¬U(A,B)(s) hold, with q∨U on (s,t). The formula is equivalent to:

  [S(a, q∧¬A) ∧ ¬A ∧ ¬(B∧U)]
  ∨ S(¬B∧¬A∧(q∨U)∧S(a,q∧¬A), q∨U)

D1 is separated: S(a,q∧¬A) is U-free, ¬A is U-free, ¬(B∧U) is boolean of atoms/U.
D2 uses eliminations (3) and (5): factor (q∨U) in event, apply since_distrib. -/

set_option maxHeartbeats 3200000 in
/-- GHR94 10.2.3 item 6: S(a∧¬U, q∨U) ↔ [S(a,q∧¬A)∧¬A∧¬(B∧U)] ∨ S(¬B∧¬A∧(q∨U)∧S(a,q∧¬A), q∨U).
    The decomposition considers when the first ¬B after the witness s occurs. -/
theorem case6_equiv_Z (a q A B : Formula Atom) :
    intEquiv (.snce (Formula.and a (Formula.neg (.untl A B)))
                     (Formula.or q (.untl A B)))
              (Formula.or
                (Formula.and (Formula.and (.snce a (Formula.and q (Formula.neg A)))
                  (Formula.neg A))
                  (Formula.neg (Formula.and B (.untl A B))))
                (.snce (Formula.and (Formula.and (Formula.and (Formula.neg B) (Formula.neg A))
                  (Formula.or q (.untl A B)))
                  (.snce a (Formula.and q (Formula.neg A))))
                  (Formula.or q (.untl A B)))) := by
  intro M t; constructor
  · -- Forward: S(a∧¬U, q∨U)(t) → D1 ∨ D2
    intro ⟨s, hst, hevent, hguard⟩
    have ⟨ha_s, hnotU_s⟩ := (int_truth_and M s _ _).mp hevent
    by_cases h_allB : ∀ r, s < r → r < t → intTruth M r B
    · -- Case: B holds on all of (s,t)
      have h_notA_interval : ∀ r, s < r → r < t → ¬ intTruth M r A := by
        intro r hsr hrt hAr
        apply hnotU_s
        exact ⟨r, hsr, hAr, fun z hsz hzr => h_allB z hsz (lt_trans hzr hrt)⟩
      have h_qnA_interval : ∀ r, s < r → r < t → intTruth M r (Formula.and q (Formula.neg A)) := by
        intro r hsr hrt
        apply (int_truth_and M r _ _).mpr
        constructor
        · rcases (int_truth_or M r _ _).mp (hguard r hsr hrt) with hq | hU_r
          · exact hq
          · exfalso; apply hnotU_s
            obtain ⟨w, hrw, hAw, hBrw⟩ := hU_r
            exact ⟨w, lt_trans hsr hrw, hAw, fun z hsz hzw => by
              rcases lt_or_ge z r with hzr | hrz
              · exact h_allB z hsz (lt_trans hzr hrt)
              · rcases lt_or_eq_of_le hrz with hrz_lt | hrz_eq
                · exact hBrw z hrz_lt hzw
                · exact h_allB z hsz (by omega)⟩
        · exact h_notA_interval r hsr hrt
      apply (int_truth_or M t _ _).mpr; left
      apply (int_truth_and M t _ _).mpr; constructor
      · apply (int_truth_and M t _ _).mpr; constructor
        · exact ⟨s, hst, ha_s, h_qnA_interval⟩
        · intro hAt; apply hnotU_s
          exact ⟨t, hst, hAt, h_allB⟩
      · intro hBU
        have ⟨hBt, hUt⟩ := (int_truth_and M t _ _).mp hBU
        obtain ⟨w, htw, hAw, hBtw⟩ := hUt
        apply hnotU_s
        exact ⟨w, lt_trans hst htw, hAw, fun z hsz hzw => by
          rcases lt_or_ge z t with hzt | htz
          · exact h_allB z hsz hzt
          · rcases eq_or_lt_of_le htz with rfl | htz'
            · exact hBt
            · exact hBtw z htz' hzw⟩
    · -- Case: ∃ r₀ ∈ (s,t) with ¬B(r₀)
      push_neg at h_allB
      obtain ⟨r₀, hsr₀, hr₀t, hnotBr₀⟩ := h_allB
      have h_min : ∃ r₁, s < r₁ ∧ r₁ < t ∧ ¬ intTruth M r₁ B ∧
          (∀ z, s < z → z < r₁ → intTruth M z B) := by
        by_contra h_no_min
        push_neg at h_no_min
        have : ∀ n : ℕ, ∀ r, s < r → r < t → r - s ≤ ↑n → ¬ intTruth M r B →
            ∃ r₁, s < r₁ ∧ r₁ < t ∧ ¬ intTruth M r₁ B ∧
            (∀ z, s < z → z < r₁ → intTruth M z B) := by
          intro n
          induction n with
          | zero => intro r hsr _ hrs _; omega
          | succ k ih =>
            intro r hsr hrt hrs hnotBr
            obtain ⟨z, hsz, hzr, hnotBz⟩ := h_no_min r hsr hrt hnotBr
            exact ih z hsz (lt_trans hzr hrt) (by omega) hnotBz
        obtain ⟨r₁, hsr₁, hr₁t, hnotBr₁, hB_min⟩ :=
          this (r₀ - s).toNat r₀ hsr₀ hr₀t (by omega) hnotBr₀
        obtain ⟨z, hsz, hzr₁, hnotBz⟩ := h_no_min r₁ hsr₁ hr₁t hnotBr₁
        exact hnotBz (hB_min z hsz hzr₁)
      obtain ⟨r₁, hsr₁, hr₁t, hnotBr₁, hB_min⟩ := h_min
      have hnotAr₁ : ¬ intTruth M r₁ A := by
        intro hAr₁; apply hnotU_s
        exact ⟨r₁, hsr₁, hAr₁, hB_min⟩
      have h_qnA_sr₁ : ∀ z, s < z → z < r₁ → intTruth M z (Formula.and q (Formula.neg A)) := by
        intro z hsz hzr₁
        apply (int_truth_and M z _ _).mpr; constructor
        · rcases (int_truth_or M z _ _).mp (hguard z hsz (lt_trans hzr₁ hr₁t)) with hq | hUz
          · exact hq
          · exfalso; apply hnotU_s
            obtain ⟨w, hzw, hAw, hBzw⟩ := hUz
            exact ⟨w, lt_trans hsz hzw, hAw, fun v hsv hvw => by
              rcases lt_or_ge v z with hvz | hzv
              · rcases lt_or_ge v r₁ with hvr₁ | hr₁v
                · exact hB_min v hsv hvr₁
                · exact hB_min v hsv (by omega)
              · rcases lt_or_eq_of_le hzv with hzv_lt | hzv_eq
                · exact hBzw v hzv_lt hvw
                · exact hB_min v hsv (by omega)⟩
        · intro hAz; apply hnotU_s
          exact ⟨z, hsz, hAz, fun v hsv hvz => hB_min v hsv (lt_trans hvz hzr₁)⟩
      have hSa_r₁ : intTruth M r₁ (.snce a (Formula.and q (Formula.neg A))) :=
        ⟨s, hsr₁, ha_s, h_qnA_sr₁⟩
      have hqU_r₁ := hguard r₁ hsr₁ hr₁t
      apply (int_truth_or M t _ _).mpr; right
      refine ⟨r₁, hr₁t, ?_, fun z hz₁ hzt => hguard z (lt_trans hsr₁ hz₁) hzt⟩
      apply (int_truth_and M r₁ _ _).mpr; constructor
      · apply (int_truth_and M r₁ _ _).mpr; constructor
        · apply (int_truth_and M r₁ _ _).mpr; exact ⟨hnotBr₁, hnotAr₁⟩
        · exact hqU_r₁
      · exact hSa_r₁
  · -- Backward: D1 ∨ D2 → S(a∧¬U, q∨U)
    intro h
    rcases (int_truth_or M t _ _).mp h with hD1 | hD2
    · -- D1: S(a, q∧¬A)(t) ∧ ¬A(t) ∧ ¬(B∧U)(t)
      have ⟨hSaqnA, hrest⟩ := (int_truth_and M t _ _).mp hD1
      have ⟨hSa, hnotAt⟩ := (int_truth_and M t _ _).mp hSaqnA
      obtain ⟨s, hst, ha_s, hqnA_guard⟩ := hSa
      have hnotU_s : ¬ intTruth M s (.untl A B) := by
        intro ⟨w, hsw, hAw, hBsw⟩
        have hwt : t < w := by
          rcases lt_or_ge w t with hwt | htw
          · exact absurd hAw (((int_truth_and M w _ _).mp (hqnA_guard w hsw hwt)).2)
          · exact lt_of_le_of_ne htw (fun h => hnotAt (h ▸ hAw))
        have hBt : intTruth M t B := hBsw t hst hwt
        have hUt : intTruth M t (.untl A B) :=
          ⟨w, hwt, hAw, fun z htz hzw => hBsw z (lt_trans hst htz) hzw⟩
        exact hrest ((int_truth_and M t _ _).mpr ⟨hBt, hUt⟩)
      refine ⟨s, hst, (int_truth_and M s _ _).mpr ⟨ha_s, hnotU_s⟩, fun r hsr hrt => ?_⟩
      exact (int_truth_or M r _ _).mpr (Or.inl (((int_truth_and M r _ _).mp (hqnA_guard r hsr hrt)).1))
    · -- D2: S(¬B∧¬A∧(q∨U)∧S(a,q∧¬A), q∨U)(t)
      obtain ⟨r, hrt, hevent_r, hguard_r⟩ := hD2
      have ⟨h_left, hSa_r⟩ := (int_truth_and M r _ _).mp hevent_r
      have ⟨h_nBnA, hqU_r⟩ := (int_truth_and M r _ _).mp h_left
      have ⟨hnotBr, hnotAr⟩ := (int_truth_and M r _ _).mp h_nBnA
      obtain ⟨s, hsr, ha_s, hqnA_sr⟩ := hSa_r
      have hnotU_s : ¬ intTruth M s (.untl A B) := by
        intro ⟨w, hsw, hAw, hBsw⟩
        have hwr : r < w := by
          rcases lt_or_ge w r with hwr | hrw
          · exact absurd hAw (((int_truth_and M w _ _).mp (hqnA_sr w hsw hwr)).2)
          · exact lt_of_le_of_ne hrw (fun h => hnotAr (h ▸ hAw))
        exact hnotBr (hBsw r hsr hwr)
      refine ⟨s, lt_trans hsr hrt, (int_truth_and M s _ _).mpr ⟨ha_s, hnotU_s⟩, fun z hsz hzt => ?_⟩
      rcases lt_or_ge z r with hzr | hrz
      · exact (int_truth_or M z _ _).mpr (Or.inl (((int_truth_and M z _ _).mp (hqnA_sr z hsz hzr)).1))
      · rcases eq_or_lt_of_le hrz with rfl | hrz'
        · exact hqU_r
        · exact hguard_r z hrz' hzt

/-- Case 6 separability for Z: S(a ^ ~U(A,B), q v U(A,B)) is separable.
    Uses GHR94 10.2.3 item 6 direct formula, then separates each disjunct
    using eliminations (3) and (5) per GHR94. -/
theorem case6_separable_Z (a q A B : Formula Atom)
    (ha : isUFree a = true) (hq : isUFree q = true)
    (hA : isUFree A = true) (hB : isUFree B = true)
    (_ha' : isSFree a = true) (_hq' : isSFree q = true)
    (hA' : isSFree A = true) (hB' : isSFree B = true) :
    isSeparable (.snce (Formula.and a (Formula.neg (.untl A B)))
      (Formula.or q (.untl A B))) := by
  -- Apply case6_equiv_Z: S(a∧¬U, q∨U) ↔ D1 ∨ D2
  apply is_separable_of_equiv (case6_equiv_Z a q A B)
  apply or_separable
  · -- D1: S(a, q∧¬A) ∧ ¬A ∧ ¬(B∧U)
    apply and_separable
    · apply and_separable
      · -- S(a, q∧¬A): a, q, A all U-free → syntactically separated
        have hg : isUFree (Formula.and q (Formula.neg A)) = true := by
          simp [Formula.and, Formula.neg, isUFree, hq, hA]
        exact ⟨.snce a (Formula.and q (Formula.neg A)),
          by simp [isSyntacticallySeparated, ha, hg], int_equiv_refl _⟩
      · -- ¬A: U-free and S-free
        exact u_free_s_free_is_separable (Formula.neg A)
          (by simp [Formula.neg, isUFree, hA])
          (by simp [Formula.neg, isSFree, hA'])
    · -- ¬(B∧U): neg of (B∧U). B is U-free/S-free, U is S-free future.
      apply neg_separable
      exact and_separable (u_free_s_free_is_separable B hB hB')
        ⟨.untl A B, by simp [isSyntacticallySeparated, hA', hB'], int_equiv_refl _⟩
  · -- D2: S(¬B∧¬A∧(q∨U)∧S(a,q∧¬A), q∨U)
    -- Factor: event = STUFF ∧ (q∨U) where STUFF = (¬B∧¬A)∧S(a,q∧¬A) is U-free.
    -- Rearrange the conjunction to put (q∨U) last.
    have h_rearrange : intEquiv
      (Formula.and (Formula.and (Formula.and (Formula.neg B) (Formula.neg A))
        (Formula.or q (.untl A B)))
        (.snce a (Formula.and q (Formula.neg A))))
      (Formula.and (Formula.and (Formula.and (Formula.neg B) (Formula.neg A))
        (.snce a (Formula.and q (Formula.neg A))))
        (Formula.or q (.untl A B))) := by
      intro M t; constructor
      · intro h
        have ⟨h1, h2⟩ := (int_truth_and M t _ _).mp h
        have ⟨h3, h4⟩ := (int_truth_and M t _ _).mp h1
        exact (int_truth_and M t _ _).mpr ⟨(int_truth_and M t _ _).mpr ⟨h3, h2⟩, h4⟩
      · intro h
        have ⟨h1, h2⟩ := (int_truth_and M t _ _).mp h
        have ⟨h3, h4⟩ := (int_truth_and M t _ _).mp h1
        exact (int_truth_and M t _ _).mpr ⟨(int_truth_and M t _ _).mpr ⟨h3, h2⟩, h4⟩
    apply is_separable_of_equiv (snce_event_congr h_rearrange)
    -- Now: S(STUFF ∧ (q∨U), q∨U) where STUFF = (¬B∧¬A)∧S(a,q∧¬A) is U-free
    -- Distribute STUFF∧(q∨U) = (STUFF∧q) ∨ (STUFF∧U) via and_or_distrib
    have h_distrib : intEquiv
      (Formula.and (Formula.and (Formula.and (Formula.neg B) (Formula.neg A))
        (.snce a (Formula.and q (Formula.neg A))))
        (Formula.or q (.untl A B)))
      (Formula.or
        (Formula.and (Formula.and (Formula.and (Formula.neg B) (Formula.neg A))
          (.snce a (Formula.and q (Formula.neg A)))) q)
        (Formula.and (Formula.and (Formula.and (Formula.neg B) (Formula.neg A))
          (.snce a (Formula.and q (Formula.neg A)))) (.untl A B))) := by
      intro M t; constructor
      · intro h
        have ⟨hc, hab⟩ := (int_truth_and M t _ _).mp h
        rcases (int_truth_or M t _ _).mp hab with ha | hb
        · exact (int_truth_or M t _ _).mpr (Or.inl ((int_truth_and M t _ _).mpr ⟨hc, ha⟩))
        · exact (int_truth_or M t _ _).mpr (Or.inr ((int_truth_and M t _ _).mpr ⟨hc, hb⟩))
      · intro h
        rcases (int_truth_or M t _ _).mp h with h1 | h2
        · have ⟨hc, ha⟩ := (int_truth_and M t _ _).mp h1
          exact (int_truth_and M t _ _).mpr ⟨hc, (int_truth_or M t _ _).mpr (Or.inl ha)⟩
        · have ⟨hc, hb⟩ := (int_truth_and M t _ _).mp h2
          exact (int_truth_and M t _ _).mpr ⟨hc, (int_truth_or M t _ _).mpr (Or.inr hb)⟩
    apply is_separable_of_equiv (snce_event_congr h_distrib)
    apply is_separable_of_equiv (since_distrib_or_left _ _ (Formula.or q (.untl A B)))
    have hSTUFF_uf : isUFree (Formula.and (Formula.and (Formula.neg B) (Formula.neg A))
        (.snce a (Formula.and q (Formula.neg A)))) = true := by
      simp [Formula.and, Formula.neg, isUFree, ha, hq, hA, hB]
    apply or_separable
    · -- S(STUFF∧q, q∨U): STUFF∧q is U-free → snce_Ufree_event_qU_guard_separable
      have hev_uf : isUFree (Formula.and (Formula.and (Formula.and (Formula.neg B)
          (Formula.neg A)) (.snce a (Formula.and q (Formula.neg A)))) q) = true := by
        simp [Formula.and, Formula.neg, isUFree, ha, hq, hA, hB]
      exact snce_Ufree_event_qU_guard_separable _ q A B hev_uf hq hA hB hA' hB'
    · -- S(STUFF∧U, q∨U): STUFF is U-free → case5_separable_Z_gen
      exact case5_separable_Z_gen _ q A B hSTUFF_uf hq hA hB hA' hB'

/-- Case 6 generalized: drops S-free requirements on a, q (they were unused
    in the original proof). Only needs S-free A, B. -/
theorem case6_separable_Z_gen (a q A B : Formula Atom)
    (ha : isUFree a = true) (hq : isUFree q = true)
    (hA : isUFree A = true) (hB : isUFree B = true)
    (hA' : isSFree A = true) (hB' : isSFree B = true) :
    isSeparable (.snce (Formula.and a (Formula.neg (.untl A B)))
      (Formula.or q (.untl A B))) := by
  apply is_separable_of_equiv (case6_equiv_Z a q A B)
  apply or_separable
  · apply and_separable
    · apply and_separable
      · have hg : isUFree (Formula.and q (Formula.neg A)) = true := by
          simp [Formula.and, Formula.neg, isUFree, hq, hA]
        exact ⟨.snce a (Formula.and q (Formula.neg A)),
          by simp [isSyntacticallySeparated, ha, hg], int_equiv_refl _⟩
      · exact u_free_s_free_is_separable (Formula.neg A)
          (by simp [Formula.neg, isUFree, hA])
          (by simp [Formula.neg, isSFree, hA'])
    · apply neg_separable
      exact and_separable (u_free_s_free_is_separable B hB hB')
        ⟨.untl A B, by simp [isSyntacticallySeparated, hA', hB'], int_equiv_refl _⟩
  · have h_rearrange : intEquiv
      (Formula.and (Formula.and (Formula.and (Formula.neg B) (Formula.neg A))
        (Formula.or q (.untl A B)))
        (.snce a (Formula.and q (Formula.neg A))))
      (Formula.and (Formula.and (Formula.and (Formula.neg B) (Formula.neg A))
        (.snce a (Formula.and q (Formula.neg A))))
        (Formula.or q (.untl A B))) := by
      intro M t; constructor
      · intro h
        have ⟨h1, h2⟩ := (int_truth_and M t _ _).mp h
        have ⟨h3, h4⟩ := (int_truth_and M t _ _).mp h1
        exact (int_truth_and M t _ _).mpr ⟨(int_truth_and M t _ _).mpr ⟨h3, h2⟩, h4⟩
      · intro h
        have ⟨h1, h2⟩ := (int_truth_and M t _ _).mp h
        have ⟨h3, h4⟩ := (int_truth_and M t _ _).mp h1
        exact (int_truth_and M t _ _).mpr ⟨(int_truth_and M t _ _).mpr ⟨h3, h2⟩, h4⟩
    apply is_separable_of_equiv (snce_event_congr h_rearrange)
    have h_distrib : intEquiv
      (Formula.and (Formula.and (Formula.and (Formula.neg B) (Formula.neg A))
        (.snce a (Formula.and q (Formula.neg A))))
        (Formula.or q (.untl A B)))
      (Formula.or
        (Formula.and (Formula.and (Formula.and (Formula.neg B) (Formula.neg A))
          (.snce a (Formula.and q (Formula.neg A)))) q)
        (Formula.and (Formula.and (Formula.and (Formula.neg B) (Formula.neg A))
          (.snce a (Formula.and q (Formula.neg A)))) (.untl A B))) := by
      intro M t; constructor
      · intro h
        have ⟨hc, hab⟩ := (int_truth_and M t _ _).mp h
        rcases (int_truth_or M t _ _).mp hab with ha | hb
        · exact (int_truth_or M t _ _).mpr (Or.inl ((int_truth_and M t _ _).mpr ⟨hc, ha⟩))
        · exact (int_truth_or M t _ _).mpr (Or.inr ((int_truth_and M t _ _).mpr ⟨hc, hb⟩))
      · intro h
        rcases (int_truth_or M t _ _).mp h with h1 | h2
        · have ⟨hc, ha⟩ := (int_truth_and M t _ _).mp h1
          exact (int_truth_and M t _ _).mpr ⟨hc, (int_truth_or M t _ _).mpr (Or.inl ha)⟩
        · have ⟨hc, hb⟩ := (int_truth_and M t _ _).mp h2
          exact (int_truth_and M t _ _).mpr ⟨hc, (int_truth_or M t _ _).mpr (Or.inr hb)⟩
    apply is_separable_of_equiv (snce_event_congr h_distrib)
    apply is_separable_of_equiv (since_distrib_or_left _ _ (Formula.or q (.untl A B)))
    have hSTUFF_uf : isUFree (Formula.and (Formula.and (Formula.neg B) (Formula.neg A))
        (.snce a (Formula.and q (Formula.neg A)))) = true := by
      simp [Formula.and, Formula.neg, isUFree, ha, hq, hA, hB]
    apply or_separable
    · have hev_uf : isUFree (Formula.and (Formula.and (Formula.and (Formula.neg B)
          (Formula.neg A)) (.snce a (Formula.and q (Formula.neg A)))) q) = true := by
        simp [Formula.and, Formula.neg, isUFree, ha, hq, hA, hB]
      exact snce_Ufree_event_qU_guard_separable _ q A B hev_uf hq hA hB hA' hB'
    · exact case5_separable_Z_gen _ q A B hSTUFF_uf hq hA hB hA' hB'

/-! ## Case 7 via GHR94 Direct Formula (10.2.3 item 7)

GHR94 approach: S(a∧U, q∨¬U). By considering when A is true we deduce:

  S(a∧U, q∨¬U) ↔ [S(A∧(q∨¬U)∧S(a,B∧q), q∨¬U)]     -- D1
               ∨ [S(a,B∧q) ∧ A]                       -- D2
               ∨ [S(a,B∧q) ∧ B ∧ U(A,B)]              -- D3

D2: separated (U-free past ∧ U-free/S-free atom).
D3: separated (U-free past ∧ S-free future ∧ S-free future).
D1: further eliminated by distributing (q∨¬U) in event, then
    S(U-free, q∨¬U) (Case 4 pattern) and S(U-free∧¬U, q∨¬U) (Case 8 pattern).

The first disjunct can be further eliminated by eliminations (8) and (4). -/

set_option maxHeartbeats 3200000 in
/-- GHR94 10.2.3 item 7: S(a∧U, q∨¬U) ↔ D1 ∨ D2 ∨ D3.
    The decomposition considers when the A from U(A,B) first occurs. -/
theorem case7_equiv_Z (a q A B : Formula Atom) :
    intEquiv (.snce (Formula.and a (.untl A B))
                     (Formula.or q (Formula.neg (.untl A B))))
              (Formula.or (Formula.or
                (.snce (Formula.and (Formula.and A
                  (Formula.or q (Formula.neg (.untl A B))))
                  (.snce a (Formula.and B q)))
                  (Formula.or q (Formula.neg (.untl A B))))
                (Formula.and (.snce a (Formula.and B q)) A))
                (Formula.and (Formula.and (.snce a (Formula.and B q)) B) (.untl A B))) := by
  intro M t; constructor
  · -- Forward: S(a∧U, q∨¬U)(t) → D1 ∨ D2 ∨ D3
    intro ⟨s, hst, hevent, hguard⟩
    have ⟨ha_s, hU_s⟩ := (int_truth_and M s _ _).mp hevent
    -- U(A,B)(s): ∃ w > s, A(w) ∧ B on (s,w)
    obtain ⟨w, hsw, hAw, hBsw⟩ := hU_s
    -- Consider w vs t: when does A first occur relative to t?
    rcases lt_trichotomy w t with hwt | hwt | hwt
    · -- w < t: A(w) at w ∈ (s,t). B∧q on (s,w)?
      have h_Bq_sw : ∀ r, s < r → r < w → intTruth M r (Formula.and B q) := by
        intro r hsr hrw
        have hBr := hBsw r hsr hrw
        have hUr : intTruth M r (.untl A B) :=
          ⟨w, hrw, hAw, fun z hrz hzw => hBsw z (lt_trans hsr hrz) hzw⟩
        rcases (int_truth_or M r _ _).mp (hguard r hsr (lt_trans hrw hwt)) with hqr | hnotUr
        · exact (int_truth_and M r _ _).mpr ⟨hBr, hqr⟩
        · exact absurd hUr hnotUr
      have hSaBq_w : intTruth M w (.snce a (Formula.and B q)) :=
        ⟨s, hsw, ha_s, h_Bq_sw⟩
      apply (int_truth_or M t _ _).mpr; left; apply (int_truth_or M t _ _).mpr; left
      have hqnotU_w := hguard w hsw hwt
      refine ⟨w, hwt, ?_, fun r hwr hrt => hguard r (lt_trans hsw hwr) hrt⟩
      apply (int_truth_and M w _ _).mpr; constructor
      · exact (int_truth_and M w _ _).mpr ⟨hAw, hqnotU_w⟩
      · exact hSaBq_w
    · -- w = t: A(t), B on (s,t). S(a,B∧q)(t): a(s), B∧q on (s,t).
      subst hwt
      have h_Bq_sw : ∀ r, s < r → r < w → intTruth M r (Formula.and B q) := by
        intro r hsr hrw
        have hBr := hBsw r hsr hrw
        have hUr : intTruth M r (.untl A B) :=
          ⟨w, hrw, hAw, fun z hrz hzw => hBsw z (lt_trans hsr hrz) hzw⟩
        rcases (int_truth_or M r _ _).mp (hguard r hsr hrw) with hqr | hnotUr
        · exact (int_truth_and M r _ _).mpr ⟨hBr, hqr⟩
        · exact absurd hUr hnotUr
      -- D2: S(a,B∧q) ∧ A at w (t was substituted away by subst hwt)
      apply (int_truth_or M w _ _).mpr; left; apply (int_truth_or M w _ _).mpr; right
      exact (int_truth_and M w _ _).mpr ⟨⟨s, hsw, ha_s, h_Bq_sw⟩, hAw⟩
    · -- w > t: B on (s,w) ⊃ (s,t). B on (s,t). U(A,B)(t) via w > t, A(w), B(t,w).
      -- S(a,B∧q)(t): a(s), B∧q on (s,t).
      have h_Bq_st : ∀ r, s < r → r < t → intTruth M r (Formula.and B q) := by
        intro r hsr hrt
        have hBr := hBsw r hsr (lt_trans hrt hwt)
        have hUr : intTruth M r (.untl A B) :=
          ⟨w, lt_trans hrt hwt, hAw, fun z hrz hzw => hBsw z (lt_trans hsr hrz) hzw⟩
        rcases (int_truth_or M r _ _).mp (hguard r hsr hrt) with hqr | hnotUr
        · exact (int_truth_and M r _ _).mpr ⟨hBr, hqr⟩
        · exact absurd hUr hnotUr
      -- D3: S(a,B∧q) ∧ B ∧ U at t
      have hBt : intTruth M t B := hBsw t hst hwt
      have hUt : intTruth M t (.untl A B) :=
        ⟨w, hwt, hAw, fun z htz hzw => hBsw z (lt_trans hst htz) hzw⟩
      apply (int_truth_or M t _ _).mpr; right
      apply (int_truth_and M t _ _).mpr; constructor
      · exact (int_truth_and M t _ _).mpr ⟨⟨s, hst, ha_s, h_Bq_st⟩, hBt⟩
      · exact hUt
  · -- Backward: D1 ∨ D2 ∨ D3 → S(a∧U, q∨¬U)
    intro h
    rcases (int_truth_or M t _ _).mp h with h12 | hD3
    · rcases (int_truth_or M t _ _).mp h12 with hD1 | hD2
      · -- D1: S(A∧(q∨¬U)∧S(a,B∧q), q∨¬U)(t)
        obtain ⟨r, hrt, hevent_r, hguard_r⟩ := hD1
        have ⟨hAqnotU, hSaBq_r⟩ := (int_truth_and M r _ _).mp hevent_r
        have ⟨hAr, _⟩ := (int_truth_and M r _ _).mp hAqnotU
        -- S(a,B∧q)(r): ∃ s < r, a(s), B∧q on (s,r)
        obtain ⟨s, hsr, ha_s, hBq_sr⟩ := hSaBq_r
        -- U(A,B)(s): A(r) with r > s, B on (s,r) from B∧q.
        have hU_s : intTruth M s (.untl A B) :=
          ⟨r, hsr, hAr, fun z hsz hzr => ((int_truth_and M z _ _).mp (hBq_sr z hsz hzr)).1⟩
        -- Guard q∨¬U on (s,t):
        -- On (s,r): B∧q gives q, hence q∨¬U.
        -- On (r,t): hguard_r gives q∨¬U.
        refine ⟨s, lt_trans hsr hrt, (int_truth_and M s _ _).mpr ⟨ha_s, hU_s⟩, fun z hsz hzt => ?_⟩
        rcases lt_or_ge z r with hzr | hrz
        · exact (int_truth_or M z _ _).mpr (Or.inl (((int_truth_and M z _ _).mp (hBq_sr z hsz hzr)).2))
        · rcases eq_or_lt_of_le hrz with rfl | hrz'
          · exact ((int_truth_and M r _ _).mp hAqnotU).2 -- (q∨¬U)(r) from event
          · exact hguard_r z hrz' hzt
      · -- D2: S(a,B∧q) ∧ A at t
        have ⟨hSaBq, hAt⟩ := (int_truth_and M t _ _).mp hD2
        obtain ⟨s, hst, ha_s, hBq_st⟩ := hSaBq
        -- U(A,B)(s): A(t) with B on (s,t) from B∧q.
        have hU_s : intTruth M s (.untl A B) :=
          ⟨t, hst, hAt, fun z hsz hzt => ((int_truth_and M z _ _).mp (hBq_st z hsz hzt)).1⟩
        refine ⟨s, hst, (int_truth_and M s _ _).mpr ⟨ha_s, hU_s⟩, fun z hsz hzt => ?_⟩
        exact (int_truth_or M z _ _).mpr (Or.inl (((int_truth_and M z _ _).mp (hBq_st z hsz hzt)).2))
    · -- D3: S(a,B∧q) ∧ B ∧ U at t
      have ⟨hSaBq_B, hUt⟩ := (int_truth_and M t _ _).mp hD3
      have ⟨hSaBq, hBt⟩ := (int_truth_and M t _ _).mp hSaBq_B
      obtain ⟨s, hst, ha_s, hBq_st⟩ := hSaBq
      obtain ⟨w, htw, hAw, hBtw⟩ := hUt
      have hU_s : intTruth M s (.untl A B) :=
        ⟨w, lt_trans hst htw, hAw, fun z hsz hzw => by
          rcases lt_or_ge z t with hzt | htz
          · exact ((int_truth_and M z _ _).mp (hBq_st z hsz hzt)).1
          · rcases eq_or_lt_of_le htz with rfl | htz'
            · exact hBt
            · exact hBtw z htz' hzw⟩
      refine ⟨s, hst, (int_truth_and M s _ _).mpr ⟨ha_s, hU_s⟩, fun z hsz hzt => ?_⟩
      exact (int_truth_or M z _ _).mpr (Or.inl (((int_truth_and M z _ _).mp (hBq_st z hsz hzt)).2))

/-! ## Case 8 Semantic Equivalence (GHR94 10.3.11.8 on Z)

On Z, K⁻ = ⊥ and Γ⁺ = ⊥, so the 10.3.11.8 formula simplifies to:
  S(a∧¬U, q∨¬U) ↔ S(a∧¬U, ⊤) ∧ ¬S(¬q∧U, ¬a∨U)

This avoids the multi-U-type problem because:
  - S(a∧¬U, ⊤) is Case 2 (guard ⊤ is U-free)
  - S(¬q∧U, ¬a∨U) is Case 5 (event has U, guard has U)
-/

set_option maxHeartbeats 1600000 in
/-- GHR94 10.3.11.8 on Z: S(a∧¬U, q∨¬U) ↔ S(a∧¬U, ⊤) ∧ ¬S(¬q∧U, ¬a∨U). -/
theorem case8_equiv_Z (a q A B : Formula Atom) :
    intEquiv (.snce (Formula.and a (Formula.neg (.untl A B)))
                     (Formula.or q (Formula.neg (.untl A B))))
              (Formula.and
                (.snce (Formula.and a (Formula.neg (.untl A B))) (Formula.neg .bot))
                (Formula.neg (.snce (Formula.and (Formula.neg q) (.untl A B))
                                    (Formula.or (Formula.neg a) (.untl A B))))) := by
  intro M t; constructor
  · -- Forward: S(a∧¬U, q∨¬U) → S(a∧¬U, ⊤) ∧ ¬S(¬q∧U, ¬a∨U)
    intro ⟨s, hst, hevent, hguard⟩
    have ⟨ha_s, hnotU_s⟩ := (int_truth_and M s _ _).mp hevent
    apply (int_truth_and M t _ _).mpr
    refine ⟨?_, ?_⟩
    · -- S(a∧¬U, ⊤): weaken guard
      exact ⟨s, hst, hevent, fun _ _ _ => id⟩
    · -- ¬S(¬q∧U, ¬a∨U)
      intro ⟨v, hvt, hevent_v, hguard_v⟩
      have ⟨hnq_v, hU_v⟩ := (int_truth_and M v _ _).mp hevent_v
      -- Trichotomy on s vs v
      rcases lt_trichotomy s v with hsv | hsv | hsv
      · -- s < v: v ∈ (s,t), guard gives q(v)∨¬U(v). ¬q(v) → ¬U(v). But U(v). Contradiction.
        have := hguard v hsv hvt
        rcases (int_truth_or M v _ _).mp this with hq | hnotU
        · exact hnq_v hq
        · exact hnotU hU_v
      · -- s = v: ¬U(s) vs U(v). s=v → ¬U(v). But U(v). Contradiction.
        exact (hsv ▸ hnotU_s) hU_v
      · -- v < s: s ∈ (v,t), guard_v gives ¬a(s)∨U(s). But a(s) ∧ ¬U(s). Contradiction.
        have := hguard_v s hsv hst
        rcases (int_truth_or M s _ _).mp this with hna | hU
        · exact hna ha_s
        · exact hnotU_s hU
  · -- Backward: S(a∧¬U, ⊤) ∧ ¬S(¬q∧U, ¬a∨U) → S(a∧¬U, q∨¬U)
    intro hand
    have ⟨hS_top, hnotS_neg⟩ := (int_truth_and M t _ _).mp hand
    -- Find the GREATEST s₀ < t with a(s₀)∧¬U(s₀)
    obtain ⟨s₀, hs₀t, hevent₀, _⟩ := hS_top
    let pred := fun s => intTruth M s (Formula.and a (Formula.neg (.untl A B)))
    haveI : DecidablePred pred := Classical.decPred _
    have hex : ∃ n, n < t ∧ pred n := ⟨s₀, hs₀t, hevent₀⟩
    obtain ⟨s, hst, hevent_s, hmax⟩ := Int.exists_greatest_below hex
    have ⟨ha_s, hnotU_s⟩ := (int_truth_and M s _ _).mp hevent_s
    refine ⟨s, hst, (int_truth_and M s _ _).mpr ⟨ha_s, hnotU_s⟩, fun r hsr hrt => ?_⟩
    -- Need: q(r) ∨ ¬U(r) for r ∈ (s,t)
    rw [int_truth_or]
    -- By maximality: ¬(a(r) ∧ ¬U(r)) for r ∈ (s,t)
    have hmax_r : ¬ intTruth M r (Formula.and a (Formula.neg (.untl A B))) :=
      hmax r hsr hrt
    by_cases hU_r : intTruth M r (.untl A B)
    · -- U(r) holds. Need q(r) ∨ ¬U(r). We have U(r).
      by_cases hq_r : intTruth M r q
      · exact Or.inl hq_r
      · -- ¬q(r) ∧ U(r) → derive contradiction via ¬S(¬q∧U, ¬a∨U)
        exfalso; apply hnotS_neg
        refine ⟨r, hrt, (int_truth_and M r _ _).mpr ⟨hq_r, hU_r⟩, fun r' hrr' hr't => ?_⟩
        rw [int_truth_or]
        have hmax_r' : ¬ intTruth M r' (Formula.and a (Formula.neg (.untl A B))) :=
          hmax r' (lt_trans hsr hrr') hr't
        by_cases hU_r' : intTruth M r' (.untl A B)
        · exact Or.inr hU_r'
        · by_cases ha_r' : intTruth M r' a
          · exfalso; exact hmax_r' ((int_truth_and M r' _ _).mpr ⟨ha_r', hU_r'⟩)
          · exact Or.inl ha_r'
    · -- ¬U(r) holds. q(r) ∨ ¬U(r) via ¬U(r).
      exact Or.inr hU_r

/-- Case 8 generalized: drops S-free requirements on a, q. Only needs S-free A, B.
    Uses case5_separable_Z_gen and elim_case_2_gen. -/
theorem case8_separable_Z_gen (a q A B : Formula Atom)
    (ha : isUFree a = true) (hq : isUFree q = true)
    (hA : isUFree A = true) (hB : isUFree B = true)
    (hA' : isSFree A = true) (hB' : isSFree B = true) :
    isSeparable (.snce (Formula.and a (Formula.neg (.untl A B)))
      (Formula.or q (Formula.neg (.untl A B)))) := by
  apply is_separable_of_equiv (case8_equiv_Z a q A B)
  apply and_separable
  · -- S(a∧¬U, ⊤): Case 2 with guard = ⊤ = neg bot (U-free)
    have hg : isUFree (Formula.neg (Formula.bot : Formula Atom)) = true := by simp [Formula.neg, isUFree]
    obtain ⟨psi, hequiv, hsep⟩ := elim_case_2_gen a (Formula.neg (Formula.bot : Formula Atom)) A B ha hg hA hB hA' hB'
    exact ⟨psi, hsep, hequiv⟩
  · -- ¬S(¬q∧U, ¬a∨U): neg_separable of Case 5 (generalized)
    apply neg_separable
    have hnq_uf : isUFree (Formula.neg q) = true := by simp [Formula.neg, isUFree, hq]
    have hna_uf : isUFree (Formula.neg a) = true := by simp [Formula.neg, isUFree, ha]
    exact case5_separable_Z_gen (Formula.neg q) (Formula.neg a) A B hnq_uf hna_uf hA hB hA' hB'

/-- S(ev, q∨¬U) is separable when ev is U-free.
    Dual of snce_Ufree_event_qU_guard_separable.
    Uses Case 4 pattern: S(a, q∨¬U) ↔ ¬H(¬a) ∧ ¬psi1 via elim_case_1_gen. -/
theorem snce_Ufree_event_qNotU_guard_separable (ev q A B : Formula Atom)
    (hev_uf : isUFree ev = true) (hq : isUFree q = true)
    (hA : isUFree A = true) (hB : isUFree B = true)
    (hA' : isSFree A = true) (hB' : isSFree B = true) :
    isSeparable (.snce ev (Formula.or q (Formula.neg (.untl A B)))) := by
  -- Case 4 pattern: S(a, q∨¬U) ↔ ¬H(¬a) ∧ ¬S((¬a∧¬q)∧U, ¬a)
  have hna_uf : isUFree (Formula.neg ev) = true := by simp [Formula.neg, isUFree, hev_uf]
  have hnq_uf : isUFree (Formula.neg q) = true := by simp [Formula.neg, isUFree, hq]
  have hanq_uf : isUFree (Formula.and (Formula.neg ev) (Formula.neg q)) = true := by
    simp [Formula.and, Formula.neg, isUFree, hev_uf, hq]
  obtain ⟨psi1, hequiv1, hsep1⟩ := elim_case_1_gen
    (Formula.and (Formula.neg ev) (Formula.neg q)) (Formula.neg ev) A B
    hanq_uf hna_uf hA hB hA' hB'
  -- S(ev, q∨¬U) ↔ ¬H(¬ev) ∧ ¬psi1
  have hsep_H : isSyntacticallySeparated (.allPast (Formula.neg ev)) = true := by
    simp [isSyntacticallySeparated, Formula.neg, isUFree, hev_uf]
  refine is_separable_of_equiv ?_ (and_separable
    (neg_separable ⟨.allPast (Formula.neg ev), hsep_H, int_equiv_refl _⟩)
    (neg_separable ⟨psi1, hsep1, hequiv1⟩))
  intro M t; constructor
  · intro hS
    apply (int_truth_and M t _ _).mpr; constructor
    · -- ¬H(¬ev): ∃ s < t with ev(s)
      rw [int_truth_neg, int_truth_allPast]
      push_neg
      obtain ⟨s, hst, hev_s, _⟩ := hS
      exact ⟨s, hst, fun h => h hev_s⟩
    · -- ¬psi1: ¬S((¬ev∧¬q)∧U, ¬ev)
      intro hpsi1
      obtain ⟨s1, hs1t, hevent1, hguard1⟩ := hpsi1
      have ⟨hanq1, hU1⟩ := (int_truth_and M s1 _ _).mp hevent1
      have hna1 := ((int_truth_and M s1 _ _).mp hanq1).1
      have hnq1 := ((int_truth_and M s1 _ _).mp hanq1).2
      obtain ⟨s, hst, hev_s, hguard_S⟩ := hS
      -- s vs s1: if s ≤ s1 then ev(s) with s ≤ s1 and guard1 says ¬ev at s (if s < s1)
      rcases lt_trichotomy s s1 with hss1 | hss1 | hss1
      · -- s < s1: s1 ∈ (s,t). Guard of S gives q(s1)∨¬U(s1). But ¬q(s1) and U(s1). Contradiction.
        rcases (int_truth_or M s1 _ _).mp (hguard_S s1 hss1 hs1t) with hq1 | hnotU1
        · exact hnq1 hq1
        · exact hnotU1 hU1
      · -- s = s1: ¬ev(s) from hna1. But ev(s). Contradiction.
        exact hna1 (hss1 ▸ hev_s)
      · -- s1 < s: guard1 gives ¬ev(s). But ev(s). Contradiction.
        exact (hguard1 s hss1 hst) hev_s
  · intro hand
    have ⟨hnotH, hnotPsi1⟩ := (int_truth_and M t _ _).mp hand
    have hnotS1 : ¬ intTruth M t (.snce (Formula.and (Formula.and (Formula.neg ev) (Formula.neg q))
        (.untl A B)) (Formula.neg ev)) :=
      fun hS1 => hnotPsi1 hS1
    by_contra hnotS
    rcases (int_truth_or M t _ _).mp ((neg_since_equiv ev
        (Formula.or q (Formula.neg (.untl A B))) M t).mp hnotS) with hH | hS_neg
    · exact hnotH hH
    · obtain ⟨s, hst, hevent, hguard⟩ := hS_neg
      have ⟨hna_s, hnotG⟩ := (int_truth_and M s _ _).mp hevent
      have hnotQ_s : ¬ intTruth M s q :=
        fun h => ((int_truth_neg M s _).mp hnotG) ((int_truth_or M s _ _).mpr (Or.inl h))
      have hU_s : intTruth M s (.untl A B) := by
        by_contra hnotU
        exact ((int_truth_neg M s _).mp hnotG)
          ((int_truth_or M s _ _).mpr (Or.inr ((int_truth_neg M s _).mpr hnotU)))
      exact hnotS1 ⟨s, hst, (int_truth_and M s _ _).mpr
        ⟨(int_truth_and M s _ _).mpr ⟨hna_s, hnotQ_s⟩, hU_s⟩, hguard⟩

set_option maxHeartbeats 3200000 in
/-- Case 7 separability for Z: S(a ^ U(A,B), q v ~U(A,B)) is separable.
    Uses GHR94 10.2.3 item 7 direct formula. -/
theorem case7_separable_Z (a q A B : Formula Atom)
    (ha : isUFree a = true) (hq : isUFree q = true)
    (hA : isUFree A = true) (hB : isUFree B = true)
    (_ha' : isSFree a = true) (_hq' : isSFree q = true)
    (hA' : isSFree A = true) (hB' : isSFree B = true) :
    isSeparable (.snce (Formula.and a (.untl A B))
      (Formula.or q (Formula.neg (.untl A B)))) := by
  apply is_separable_of_equiv (case7_equiv_Z a q A B)
  have hBq_uf : isUFree (Formula.and B q) = true := by
    simp only [Formula.and, Formula.neg, isUFree, hB, hq, Bool.true_and, Bool.and_self]
  apply or_separable
  · apply or_separable
    · -- D1: S(A∧(q∨¬U)∧S(a,B∧q), q∨¬U)
      -- Factor (q∨¬U) in event: distribute
      have h_rearrange : intEquiv
        (Formula.and (Formula.and A (Formula.or q (Formula.neg (.untl A B))))
          (.snce a (Formula.and B q)))
        (Formula.and (Formula.and A (.snce a (Formula.and B q)))
          (Formula.or q (Formula.neg (.untl A B)))) := by
        intro M t; constructor
        · intro h
          have ⟨h1, h2⟩ := (int_truth_and M t _ _).mp h
          have ⟨h3, h4⟩ := (int_truth_and M t _ _).mp h1
          exact (int_truth_and M t _ _).mpr ⟨(int_truth_and M t _ _).mpr ⟨h3, h2⟩, h4⟩
        · intro h
          have ⟨h1, h2⟩ := (int_truth_and M t _ _).mp h
          have ⟨h3, h4⟩ := (int_truth_and M t _ _).mp h1
          exact (int_truth_and M t _ _).mpr ⟨(int_truth_and M t _ _).mpr ⟨h3, h2⟩, h4⟩
      apply is_separable_of_equiv (snce_event_congr h_rearrange)
      -- S(STUFF∧(q∨¬U), q∨¬U) where STUFF = A∧S(a,B∧q) is U-free
      have h_distrib : intEquiv
        (Formula.and (Formula.and A (.snce a (Formula.and B q)))
          (Formula.or q (Formula.neg (.untl A B))))
        (Formula.or
          (Formula.and (Formula.and A (.snce a (Formula.and B q))) q)
          (Formula.and (Formula.and A (.snce a (Formula.and B q)))
            (Formula.neg (.untl A B)))) := by
        intro M t; constructor
        · intro h
          have ⟨hc, hab⟩ := (int_truth_and M t _ _).mp h
          rcases (int_truth_or M t _ _).mp hab with ha | hb
          · exact (int_truth_or M t _ _).mpr (Or.inl ((int_truth_and M t _ _).mpr ⟨hc, ha⟩))
          · exact (int_truth_or M t _ _).mpr (Or.inr ((int_truth_and M t _ _).mpr ⟨hc, hb⟩))
        · intro h
          rcases (int_truth_or M t _ _).mp h with h1 | h2
          · have ⟨hc, ha⟩ := (int_truth_and M t _ _).mp h1
            exact (int_truth_and M t _ _).mpr ⟨hc, (int_truth_or M t _ _).mpr (Or.inl ha)⟩
          · have ⟨hc, hb⟩ := (int_truth_and M t _ _).mp h2
            exact (int_truth_and M t _ _).mpr ⟨hc, (int_truth_or M t _ _).mpr (Or.inr hb)⟩
      apply is_separable_of_equiv (snce_event_congr h_distrib)
      apply is_separable_of_equiv (since_distrib_or_left _ _
        (Formula.or q (Formula.neg (.untl A B))))
      have hSTUFF_uf : isUFree (Formula.and A (.snce a (Formula.and B q))) = true := by
        simp only [Formula.and, Formula.neg, isUFree, hA, ha, hB, hq, Bool.and_self]
      apply or_separable
      · -- S(STUFF∧q, q∨¬U): STUFF∧q is U-free → Case 4 pattern
        have hev_uf : isUFree (Formula.and (Formula.and A
            (.snce a (Formula.and B q))) q) = true := by
          simp only [Formula.and, Formula.neg, isUFree, hA, ha, hB, hq, Bool.and_self]
        exact snce_Ufree_event_qNotU_guard_separable _ q A B hev_uf hq hA hB hA' hB'
      · -- S(STUFF∧¬U, q∨¬U): Case 8 generalized
        exact case8_separable_Z_gen
          (Formula.and A (.snce a (Formula.and B q)))
          q A B hSTUFF_uf hq hA hB hA' hB'
    · -- D2: S(a,B∧q) ∧ A -- U-free past and U-free/S-free atom
      apply and_separable
      · exact ⟨.snce a (Formula.and B q),
          by simp [isSyntacticallySeparated, ha, hBq_uf], int_equiv_refl _⟩
      · exact u_free_s_free_is_separable A hA hA'
  · -- D3: S(a,B∧q) ∧ B ∧ U -- past (U-free) and future (S-free)
    apply and_separable
    · exact and_separable
        ⟨.snce a (Formula.and B q),
          by simp [isSyntacticallySeparated, ha, hBq_uf], int_equiv_refl _⟩
        (u_free_s_free_is_separable B hB hB')
    · exact ⟨.untl A B, by simp [isSyntacticallySeparated, hA', hB'], int_equiv_refl _⟩

/-- Case 7 generalized: drops S-free requirements on a, q (they were unused
    in the original proof). Only needs S-free A, B. -/
theorem case7_separable_Z_gen (a q A B : Formula Atom)
    (ha : isUFree a = true) (hq : isUFree q = true)
    (hA : isUFree A = true) (hB : isUFree B = true)
    (hA' : isSFree A = true) (hB' : isSFree B = true) :
    isSeparable (.snce (Formula.and a (.untl A B))
      (Formula.or q (Formula.neg (.untl A B)))) := by
  apply is_separable_of_equiv (case7_equiv_Z a q A B)
  have hBq_uf : isUFree (Formula.and B q) = true := by
    simp only [Formula.and, Formula.neg, isUFree, hB, hq, Bool.true_and, Bool.and_self]
  apply or_separable
  · apply or_separable
    · have h_rearrange : intEquiv
        (Formula.and (Formula.and A (Formula.or q (Formula.neg (.untl A B))))
          (.snce a (Formula.and B q)))
        (Formula.and (Formula.and A (.snce a (Formula.and B q)))
          (Formula.or q (Formula.neg (.untl A B)))) := by
        intro M t; constructor
        · intro h
          have ⟨h1, h2⟩ := (int_truth_and M t _ _).mp h
          have ⟨h3, h4⟩ := (int_truth_and M t _ _).mp h1
          exact (int_truth_and M t _ _).mpr ⟨(int_truth_and M t _ _).mpr ⟨h3, h2⟩, h4⟩
        · intro h
          have ⟨h1, h2⟩ := (int_truth_and M t _ _).mp h
          have ⟨h3, h4⟩ := (int_truth_and M t _ _).mp h1
          exact (int_truth_and M t _ _).mpr ⟨(int_truth_and M t _ _).mpr ⟨h3, h2⟩, h4⟩
      apply is_separable_of_equiv (snce_event_congr h_rearrange)
      have h_distrib : intEquiv
        (Formula.and (Formula.and A (.snce a (Formula.and B q)))
          (Formula.or q (Formula.neg (.untl A B))))
        (Formula.or
          (Formula.and (Formula.and A (.snce a (Formula.and B q))) q)
          (Formula.and (Formula.and A (.snce a (Formula.and B q)))
            (Formula.neg (.untl A B)))) := by
        intro M t; constructor
        · intro h
          have ⟨hc, hab⟩ := (int_truth_and M t _ _).mp h
          rcases (int_truth_or M t _ _).mp hab with ha | hb
          · exact (int_truth_or M t _ _).mpr (Or.inl ((int_truth_and M t _ _).mpr ⟨hc, ha⟩))
          · exact (int_truth_or M t _ _).mpr (Or.inr ((int_truth_and M t _ _).mpr ⟨hc, hb⟩))
        · intro h
          rcases (int_truth_or M t _ _).mp h with h1 | h2
          · have ⟨hc, ha⟩ := (int_truth_and M t _ _).mp h1
            exact (int_truth_and M t _ _).mpr ⟨hc, (int_truth_or M t _ _).mpr (Or.inl ha)⟩
          · have ⟨hc, hb⟩ := (int_truth_and M t _ _).mp h2
            exact (int_truth_and M t _ _).mpr ⟨hc, (int_truth_or M t _ _).mpr (Or.inr hb)⟩
      apply is_separable_of_equiv (snce_event_congr h_distrib)
      apply is_separable_of_equiv (since_distrib_or_left _ _
        (Formula.or q (Formula.neg (.untl A B))))
      have hSTUFF_uf : isUFree (Formula.and A (.snce a (Formula.and B q))) = true := by
        simp only [Formula.and, Formula.neg, isUFree, hA, ha, hB, hq, Bool.and_self]
      apply or_separable
      · have hev_uf : isUFree (Formula.and (Formula.and A
            (.snce a (Formula.and B q))) q) = true := by
          simp only [Formula.and, Formula.neg, isUFree, hA, ha, hB, hq, Bool.and_self]
        exact snce_Ufree_event_qNotU_guard_separable _ q A B hev_uf hq hA hB hA' hB'
      · exact case8_separable_Z_gen
          (Formula.and A (.snce a (Formula.and B q)))
          q A B hSTUFF_uf hq hA hB hA' hB'
    · apply and_separable
      · exact ⟨.snce a (Formula.and B q),
          by simp [isSyntacticallySeparated, ha, hBq_uf], int_equiv_refl _⟩
      · exact u_free_s_free_is_separable A hA hA'
  · apply and_separable
    · exact and_separable
        ⟨.snce a (Formula.and B q),
          by simp [isSyntacticallySeparated, ha, hBq_uf], int_equiv_refl _⟩
        (u_free_s_free_is_separable B hB hB')
    · exact ⟨.untl A B, by simp [isSyntacticallySeparated, hA', hB'], int_equiv_refl _⟩

/-- Case 8 separability for Z: S(a ^ ~U(A,B), q v ~U(A,B)) is separable. -/
theorem case8_separable_Z (a q A B : Formula Atom)
    (ha : isUFree a = true) (hq : isUFree q = true)
    (hA : isUFree A = true) (hB : isUFree B = true)
    (ha' : isSFree a = true) (hq' : isSFree q = true)
    (hA' : isSFree A = true) (hB' : isSFree B = true) :
    isSeparable (.snce (Formula.and a (Formula.neg (.untl A B)))
      (Formula.or q (Formula.neg (.untl A B)))) := by
  -- Apply case8_equiv_Z: S(a∧¬U, q∨¬U) ↔ S(a∧¬U, ⊤) ∧ ¬S(¬q∧U, ¬a∨U)
  apply is_separable_of_equiv (case8_equiv_Z a q A B)
  apply and_separable
  · -- S(a∧¬U, ⊤): Case 2 with guard = ⊤ = neg bot (U-free)
    have hg : isUFree (Formula.neg (Formula.bot : Formula Atom)) = true := by simp [Formula.neg, isUFree]
    obtain ⟨psi, hequiv, hsep⟩ := elim_case_2_gen a (Formula.neg (Formula.bot : Formula Atom)) A B ha hg hA hB hA' hB'
    exact ⟨psi, hsep, hequiv⟩
  · -- ¬S(¬q∧U, ¬a∨U): neg_separable of Case 5
    apply neg_separable
    have hnq_uf : isUFree (Formula.neg q) = true := by simp [Formula.neg, isUFree, hq]
    have hna_uf : isUFree (Formula.neg a) = true := by simp [Formula.neg, isUFree, ha]
    have hnq_sf : isSFree (Formula.neg q) = true := by simp [Formula.neg, isSFree, hq']
    have hna_sf : isSFree (Formula.neg a) = true := by simp [Formula.neg, isSFree, ha']
    exact case5_separable_Z (Formula.neg q) (Formula.neg a) A B hnq_uf hna_uf hA hB hnq_sf hna_sf hA' hB'


end Cslib.Logic.Bimodal.Metalogic.Separation
