/-
Copyright (c) 2026 Akhilesh Balaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji
-/

module

public import Cslib.Computability.Languages.RegularLanguage

@[expose] public section

/-! # All three subparts of the Myhill-Nerode Theorem for DFAs

(1) `L` regular iff. `∼_L` has a finite number of equivalence classes `N`.
(2) `N` is the number of states in the minimal DFA accepting `L`.
(3) The minimal DFA is unique up to unique isomorphism. That is, for any
    minimal DFA acceptor, there exists exactly one isomorphism from it to the
    following one:

  > Let each equivalence class `⟦ x ⟧` correspond to a state, and let state
  transitions be `a : ⟦ x ⟧ → ⟦ x a ⟧` for each `a ∈ Σ`.
  Let the starting state be `⟦ ϵ ⟧`, and the accepting states be `⟦ x ⟧` where
  `x ∈ L`.

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][Hopcroft2006]
* [T. Malkin, *COMS W3261: Computer Science Theory, Handout 3: The Myhill-Nerode Theorem
   and Implications*][Malkin2024]
* [Wikipedia contributors, Myhill–Nerode theorem][WikipediaMyhillNerode2026]
-/

namespace Language
open Cslib
open scoped RightCongruence
open Language
open Automata Automata.DA Automata.DA.FinAcc Acceptor

variable {α : Type*} {l : Language α}

/-- The Nerode congruence of a language `l` is a right congruence on strings where two
strings are related iff. all their right extensions are either both in the language
or both not in it. -/
instance NerodeCongruence (l : Language α) : RightCongruence α where
  r x y := ∀ z, x ++ z ∈ l ↔ y ++ z ∈ l
  iseqv.refl := fun _ _ => Iff.rfl
  iseqv.symm := fun h z => (h z).symm
  iseqv.trans := fun h_1 h_2 z => (h_1 z).trans (h_2 z)
  right_cov := ⟨fun a {x y} (h : ∀ z, x ++ z ∈ l ↔ y ++ z ∈ l) z =>
    List.append_assoc x a z ▸ List.append_assoc y a z ▸ h (a ++ z)⟩

/-- The Nerode congruence of a language `l` gives rise to a DFA where each state corresponds to an
equivalence class of the language under the Nerode congruence. Note that this is simply the DFA
given rise to by the underlying right congruence with only the accept states specified here as
`{⟦ x ⟧ | x ∈ l}`. -/
def NerodeCongruence.toFinAcc (l : Language α) :
    DA.FinAcc (Quotient (l.NerodeCongruence).eq) α :=
  { (l.NerodeCongruence).toDA with accept := (⟦·⟧) '' l }

/-- The DFA constructed from the Nerode congruence on `l` accepts `l`. -/
@[simp, scoped grind =]
theorem nerodeCongruence_to_finacc_acc (l : Language α) :
    language (NerodeCongruence.toFinAcc l) = l := by
  ext x
  simp only [NerodeCongruence.toFinAcc, language, Acceptor.Accepts, congr_mtr_eq, Set.mem_image]
  constructor
  · rintro ⟨y, hy, heq⟩
    simpa using (Quotient.eq.mp heq []).mp (by simpa using hy)
  · exact fun hx => ⟨x, hx, rfl⟩

/-- The statement that (two strings are related by the Nerode congruence `c_l` iff. all their right
extensions are either both in the language or both not in it) is equivalent to stating that (all
their right extensions are either both accepted or rejected by the DFA given rise to by `c_l`. -/
theorem nerodeCongruence_accepts_apply
    (M : DA.FinAcc State α) (x y : List α) :
    ((language M).NerodeCongruence).r x y ↔
      ∀ z,
        M.mtr (M.mtr M.start x) z ∈ M.accept ↔
        M.mtr (M.mtr M.start y) z ∈ M.accept := by
  simp only [FLTS.mtr, ← List.foldl_append]
  rfl

/-- If `l` is regular, then `α*/c_l` is finite. -/
theorem IsRegular.finite_range_nerode_quotient (h : l.IsRegular) :
    Finite (Quotient (l.NerodeCongruence).eq) := by
  rcases IsRegular.iff_dfa.mp h with ⟨State, hFin, M, hM⟩
  rw [← hM]
  apply Finite.of_surjective
    (fun s : State =>
      ⟦ Classical.epsilon (fun x => M.mtr M.start x = s) ⟧)
  intro q
  induction q using Quotient.inductionOn with
  | h x =>
    exact ⟨M.mtr M.start x, Quotient.sound (by
      change ((language M).NerodeCongruence).r _ x
      rw [nerodeCongruence_accepts_apply]
      intro z
      have heps : M.mtr M.start (Classical.epsilon
          (fun y => M.mtr M.start y = M.mtr M.start x)) = M.mtr M.start x :=
        @Classical.epsilon_spec _ (fun y => M.mtr M.start y = M.mtr M.start x) ⟨x, rfl⟩
      rw [heps])⟩

-- Myhill-Nerode (1)

/-- `l` is regular if and only if `α*/c_l` is finite. -/
@[simp, scoped grind =]
theorem IsRegular_iff_finite_eqv_cls_wrt_nerode {l : Language α} :
    l.IsRegular ↔ Finite (Quotient (l.NerodeCongruence).eq) := by
  constructor
  · intro h
    exact IsRegular.finite_range_nerode_quotient h
  · intro h
    letI : Fintype (Quotient (l.NerodeCongruence).eq) := Fintype.ofFinite _
    set e := Fintype.equivFin (Quotient (l.NerodeCongruence).eq)
    set M := NerodeCongruence.toFinAcc l
    refine IsRegular.iff_dfa.mpr ⟨Fin _, inferInstance,
      { tr := fun s x => e (M.tr (e.symm s) x)
        start := e M.start
        accept := e '' M.accept }, ?_⟩
    have hfoldl : ∀ s x, List.foldl (fun s x => e (M.tr (e.symm s) x)) (e s) x =
        e (List.foldl M.tr s x) := by
      intro s x
      induction x generalizing s with
      | nil => simp
      | cons a as ih => simp only [List.foldl, e.symm_apply_apply, ih]
    ext x
    change List.foldl (fun s x => e (M.tr (e.symm s) x)) (e M.start) x ∈ e '' M.accept ↔ x ∈ l
    simp only [hfoldl, Set.mem_image_equiv, Equiv.symm_apply_apply,
      ← nerodeCongruence_to_finacc_acc l, language, Acceptor.Accepts, FLTS.mtr]
    exact Iff.of_eq rfl
--

/-- Given a set of strings all distinguishable by `l` (i.e., not related to each other by `c_l`),
the number of states in the DFA accepting `l` is at least the number of strings in the set. -/
@[simp]
theorem lower_bound_num_states_dfa_acc [Finite States] {l : Language α}
  {M : DA.FinAcc States α} {ws : Set (List α)} [Finite ws]
  (hws : ws.Pairwise (fun x y => ¬(l.NerodeCongruence).r x y))
  (hM : language M = l) :
    Nat.card States ≥ Nat.card ws := by
  classical
  letI : Fintype States := Fintype.ofFinite _
  letI : Fintype ws := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  by_contra h
  simp only [ge_iff_le, not_le] at h
  by_cases h_card : Fintype.card ws ≤ 1
  · exact (lt_of_lt_of_le h (le_trans h_card
      (Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr ⟨M.start⟩)))).false
  · obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, hne, heq⟩ :=
      Fintype.exists_ne_map_eq_of_card_lt (f := fun w : ws => M.mtr M.start w) (by omega)
    rw [← hM] at hws
    exact hws hx hy (fun h => hne (Subtype.ext h))
      ((nerodeCongruence_accepts_apply M x y).mpr (fun z => heq ▸ Iff.rfl))

-- Myhill-Nerode (2)

/-- All DFAs accepting `l` must have at least as many states as the number of equivalence classes
of `α*` under the Nerode congruence `c_l` induced by `l` (i.e., `|α*/c_l|`). -/
@[simp]
theorem minimum_dfa_states_eq_num_eqv_clss_nerode {M : DA.FinAcc States α}
  [Finite States] [Finite (Quotient ((language M).NerodeCongruence).eq)] :
    Nat.card States ≥ Nat.card (Quotient ((language M).NerodeCongruence).eq) := by
  classical
  let ws : Set (List α) := Set.range
    (Quotient.out : Quotient ((language M).NerodeCongruence).eq → List α)
  haveI : Finite ws := Set.finite_range _ |>.to_subtype
  have hws : ws.Pairwise (fun x y => ¬((language M).NerodeCongruence).r x y) := by
    rintro _ ⟨qx, rfl⟩ _ ⟨qy, rfl⟩ hne h
    exact hne (by simpa using Quotient.sound h)
  have card_hws_eq : Nat.card ws = Nat.card (Quotient ((language M).NerodeCongruence).eq) :=
    Nat.card_congr (Equiv.ofInjective _ Quotient.out_injective).symm
  exact card_hws_eq ▸ lower_bound_num_states_dfa_acc hws rfl
--

end Language

namespace Cslib
namespace Automata.DA

open Cslib
open scoped RightCongruence
open Language
open Automata Automata.DA Automata.DA.FinAcc Acceptor

/-- The minimal DFA accepting `l` has `|α*/c_l|` states. -/
def FinAcc.IsMinimalAutomaton [Finite States] (M : DA.FinAcc States α) (l : Language α) :=
  language M = l ∧ Nat.card States = Nat.card (Quotient (l.NerodeCongruence).eq)

/-- Given a DFA `M`, two strings are related iff. they reach the same state under when run through
`M`. The Nerode congruence is the state congruence wrt. the minimal DFA accepting `l`. -/
instance StateCongruence (M : DA.FinAcc States α) : RightCongruence α where
  r x y := ∀ z, M.mtr M.start (x ++ z) = M.mtr M.start (y ++ z)
  iseqv := ⟨by intro x z; rfl, by intro x y h z; symm; exact h z,
      by intro x y z h_1 h_2 w; exact (h_1 w).trans (h_2 w)⟩
  right_cov := ⟨by
        intro a x y h z
        simpa [List.append_assoc, FLTS.mtr_concat_eq] using h (a ++ z)⟩

/-- The Nerode congruence is the most coarse state congruence given a language. -/
@[simp]
theorem stateCongruence_refines_nerodeCongruence {M : DA.FinAcc States α} :
    ∀ x y, (StateCongruence M).r x y → ((language M).NerodeCongruence ).r x y := by
  intro x y h z
  constructor
  · intro hx
    have := h z
    simpa [language, Acceptor.Accepts, FLTS.mtr_concat_eq] using
      congrArg (fun s => s ∈ M.accept) this ▸ hx
  · intro hy
    have := h z
    simpa [language, Acceptor.Accepts, FLTS.mtr_concat_eq] using
      congrArg (fun s => s ∈ M.accept) this ▸ hy

-- Myhill-Nerode (3)

/-- The minimal DFA `M` accepting `l` is unique up to unique isomorphism. -/
@[simp]
theorem unique_minimal_dfa (M : DA.FinAcc States α) [Finite States]
    (l : Language α) (hReg : l.IsRegular) (hMin : M.IsMinimalAutomaton l) :
    ∃! φ : States ≃ Quotient (l.NerodeCongruence).eq,
      ∀ x, φ (M.mtr M.start x) = ⟦ x ⟧ := by
  obtain ⟨hML, hCard⟩ := hMin
  haveI : Finite (Quotient (l.NerodeCongruence).eq) :=
    Language.IsRegular_iff_finite_eqv_cls_wrt_nerode.mp hReg
  letI : Fintype States := Fintype.ofFinite _
  letI : Fintype (Quotient (l.NerodeCongruence).eq) := Fintype.ofFinite _
  subst hML
  let φ : States → Quotient ((language M).NerodeCongruence).eq :=
    fun s => ⟦ Classical.epsilon (fun x : List α => M.mtr M.start x = s) ⟧
  have hφ : ∀ x, φ (M.mtr M.start x) = ⟦ x ⟧ := fun x => by
    apply Quotient.sound
    apply stateCongruence_refines_nerodeCongruence
    intro z
    have := @Classical.epsilon_spec _ (fun y : List α => M.mtr M.start y = M.mtr M.start x) ⟨x, rfl⟩
    simp only [FLTS.mtr, List.foldl_append] at this ⊢; rw [this]
  have hφ_surj : Function.Surjective φ := fun q =>
    q.inductionOn (fun x => ⟨M.mtr M.start x, hφ x⟩)
  have hφ_inj : Function.Injective φ :=
    hφ_surj.injective_of_finite (Fintype.equivOfCardEq (by
      rwa [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]))
  let φ_equiv := Equiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩
  refine ⟨φ_equiv, hφ, fun ψ hψ => ?_⟩
  ext s
  obtain ⟨x, rfl⟩ : ∃ x, M.mtr M.start x = s := by
    induction h : φ s using Quotient.inductionOn with
    | h x => exact ⟨x, hφ_inj ((hφ x).trans h.symm)⟩
  simp [φ_equiv, Equiv.ofBijective, hφ, hψ]
--

end Automata.DA
end Cslib

