/-
Copyright (c) 2026 Akhilesh Balaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji
-/

module

public import Cslib.Computability.Automata.DA.Basic
public import Cslib.Computability.Automata.DA.Congr
public import Cslib.Computability.Languages.RegularLanguage
public import Cslib.Computability.Languages.Congruences.RightCongruence
public import Mathlib.Computability.Language
public import Mathlib.Data.Fintype.Card
public import Mathlib.CategoryTheory.Iso

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
-/

namespace Cslib

open Cslib
open scoped RightCongruence

open Language

namespace Automata.DA
open Acceptor

variable {α : Type} {l m : Language α}

/-- The Nerode congruence of a language `l` is a right congruence on strings where two
strings are related iff. all their right extensions are either both in the language
or both not in it. -/
def NerodeCongruence (l : Language α) : RightCongruence α where
  r x y := ∀ z, x ++ z ∈ l ↔ y ++ z ∈ l
  iseqv := ⟨fun _ _ => Iff.rfl, fun h z => (h z).symm, fun h_1 h_2 z => (h_1 z).trans (h_2 z)⟩
  right_cov := ⟨fun a {x y} (h : ∀ z, x ++ z ∈ l ↔ y ++ z ∈ l) z =>
    List.append_assoc x a z ▸ List.append_assoc y a z ▸ h (a ++ z)⟩

/-- The Nerode congruence of a language `l` gives rise to a DFA where each state corresponds to an
equivalence class of the language under the Nerode congruence. Note that this is simply the DFA
given rise to by the underlying right congruence with only the accept states specified here as
`{⟦ x ⟧ | x ∈ l}`. -/
def NerodeCongruence.toFinAcc (l : Language α) : 
    DA.FinAcc (Quotient (NerodeCongruence l).eq) α :=
  letI c := NerodeCongruence l
  { c.toDA with
    accept := {q | Quotient.lift (fun x => x ∈ l) (by
      intro x y hxy
      simpa using hxy []) q} }

/-- The DFA constructed from the Nerode congruence on `l` accepts `l`. -/
@[simp, scoped grind =]
theorem nerodecongruence_to_finacc_acc (l : Language α) :
    language (NerodeCongruence.toFinAcc l) = l := by
      ext x
      simp [NerodeCongruence.toFinAcc, language, Acceptor.Accepts]
      exact Iff.of_eq rfl

/-- The statement that two strings are related by the Nerode congruence `c` iff. all their right
extensions are either both in the language or both not in it is equivalent to saying that all their
right extensions are either both accepted or rejected by the DFA given rise to by `c`. -/
theorem nerodecongruence_accepts_apply
    (M : DA.FinAcc State α) (x y : List α) :
    (NerodeCongruence (language M)).r x y ↔
      ∀ z,
        M.mtr (M.mtr M.start x) z ∈ M.accept ↔
        M.mtr (M.mtr M.start y) z ∈ M.accept := by
  simp only [FLTS.mtr, ← List.foldl_append]
  rfl

/-- If `l` is regular, then `l/c` is finite. -/
theorem IsRegular.finite_range_nerode_quotient (h : l.IsRegular) :
    Finite (Quotient (NerodeCongruence l).eq) := by
  rcases IsRegular.iff_dfa.mp h with ⟨State, hFin, M, hM⟩
  rw [← hM]
  apply Finite.of_surjective
    (fun s : State => Quotient.mk (NerodeCongruence (language M)).eq
      (Classical.epsilon (fun x => M.mtr M.start x = s)))
  intro q
  induction q using Quotient.inductionOn with
  | h x =>
    exact ⟨M.mtr M.start x, Quotient.sound (by
      change (NerodeCongruence (language M)).r _ x
      rw [nerodecongruence_accepts_apply]
      intro z
      have heps : M.mtr M.start (Classical.epsilon
          (fun y => M.mtr M.start y = M.mtr M.start x)) = M.mtr M.start x :=
        @Classical.epsilon_spec _ (fun y => M.mtr M.start y = M.mtr M.start x) ⟨x, rfl⟩
      rw [heps])⟩

-- Myhill-Nerode (1)

/-- `l` is regular if and only if `l/c` is finite. -/
@[simp, scoped grind =]
theorem IsRegular_iff_finite_eqv_cls_wrt_nerode {l : Language α} :
    l.IsRegular ↔ Finite (Quotient (NerodeCongruence l).eq) := by
    constructor
    · intro h
      exact IsRegular.finite_range_nerode_quotient h
    · intro h
      refine IsRegular.iff_dfa.mpr ⟨Quotient (NerodeCongruence l).eq, h,
          NerodeCongruence.toFinAcc l, nerodecongruence_to_finacc_acc l⟩
--

/-- Given a set of strings all distinguishable by `l` (i.e., not related to each other by `c`),
the number of states in the DFA accepting `l` is at least the number of strings in the set. -/
@[simp]
theorem lower_bound_num_states_dfa_acc {l : Language α} {M : DA.FinAcc States α}
  {ws : Finset (List α)} (hws : ∀ x ∈ ws, ∀ y ∈ ws, x ≠ y → ¬(NerodeCongruence l).r x y)
  (hM : language M = l) [Fintype States] :
    Fintype.card States ≥ ws.card := by
    classical
    by_contra h
    simp only [ge_iff_le, not_le] at h
    by_cases h_card : ws.card ≤ 1
    · exact (lt_of_lt_of_le h (le_trans h_card
      (Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr ⟨M.start⟩)))).false
    · obtain ⟨x, hx, y, hy, hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to h
        (fun x _ => Finset.mem_univ (M.mtr M.start x))
      rw [← hM] at hws
      exact hws x hx y hy hne
        ((nerodecongruence_accepts_apply M x y).mpr (fun z => heq ▸ Iff.rfl))

-- Myhill-Nerode (2)

/-- All DFAs accepting `l` must have at least as many states as the number of equivalence classes
of `l` under `c` (i.e., `|l/c|`). -/
@[simp]
theorem minimum_dfa_states_eq_num_eqv_clss_nerode {M : DA.FinAcc States α}
  [Fintype States] [Fintype (Quotient (NerodeCongruence (language M)).eq)] :
    Fintype.card States ≥ Fintype.card (Quotient (NerodeCongruence (language M)).eq) := by
      classical
      let ws : Finset (List α) := Finset.univ.image
                (Quotient.out : Quotient (NerodeCongruence (language M)).eq → List α)
      have hws : ∀ x ∈ ws, ∀ y ∈ ws, x ≠ y → ¬(NerodeCongruence (language M)).r x y := by
        simp only [ws, Finset.mem_image, Finset.mem_univ, true_and]
        rintro _ ⟨qx, rfl⟩ _ ⟨qy, rfl⟩ hne h
        exact hne (by simpa using Quotient.sound h)
      have card_hws_eq_num_eqv_clss : ws.card = Fintype.card
                (Quotient (NerodeCongruence (language M)).eq) := by
        simp [ws, Finset.card_image_of_injective _ Quotient.out_injective]
      exact card_hws_eq_num_eqv_clss ▸ lower_bound_num_states_dfa_acc hws rfl
--

/-- The minimal DFA accepting `l` has `|l/c|` states. -/
def IsMinimalAutomaton (M : DA.FinAcc States α)
  [Fintype States] [Fintype (Quotient (NerodeCongruence (language M)).eq)] :=
    Fintype.card States = Fintype.card (Quotient (NerodeCongruence (language M)).eq)

/-- Given a DFA `M`, two strings are related iff. they reach the same state under when run through
`M`. The Nerode congruence is the state congruence wrt. the minimal DFA accepting `l`. -/
def StateCongruence (M : DA.FinAcc States α) : RightCongruence α where
  r x y := ∀ z, M.mtr M.start (x ++ z) = M.mtr M.start (y ++ z)
  iseqv := ⟨by intro x z; rfl, by intro x y h z; symm; exact h z,
      by intro x y z h_1 h_2 w; exact (h_1 w).trans (h_2 w)⟩
  right_cov := ⟨by
        intro a x y h z
        simpa [List.append_assoc, FLTS.mtr_concat_eq] using h (a ++ z)⟩

/-- The Nerode congruence is the most coarse state congruence given a language. -/
@[simp]
theorem statecongruence_refines_nerodecongruence {M : DA.FinAcc States α} :
    ∀ x y, (StateCongruence M).r x y → (NerodeCongruence (language M)).r x y := by
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

/-- Every equivalence class of `l` under a Nerode congruence is a union of one or more equivalence
classes from the state congruence of a DFA accepting `l`. -/
@[simp]
lemma nerodecongruence_eqv_cls_eq_union_statecongruence_eqv_clss
    {M : DA.FinAcc States α} (Q : Quotient (NerodeCongruence (language M)).eq) :
    {x : List α | Quotient.mk (NerodeCongruence (language M)).eq x = Q} =
      ⋃ (R : Quotient (StateCongruence M).eq)
        (_ : Quotient.mk (NerodeCongruence (language M)).eq (Quotient.out R) = Q),
        {x | Quotient.mk (StateCongruence M).eq x = R} := by
  let NC := NerodeCongruence (language M); let SC := StateCongruence M
  ext x; simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · intro hx
    exact ⟨Quotient.mk SC.eq x,
      (Quotient.sound (statecongruence_refines_nerodecongruence _ _
        (Quotient.eq.mp (Quotient.out_eq (Quotient.mk SC.eq x))))).trans hx,
      rfl⟩
  · intro ⟨R, hRQ, hxR⟩
    exact (Quotient.out_eq Q) ▸ Quotient.sound (NC.iseqv.trans
      (statecongruence_refines_nerodecongruence _ _
        (Quotient.eq.mp (hxR.trans (Quotient.out_eq R).symm)))
      (Quotient.eq.mp (hRQ.trans (Quotient.out_eq Q).symm)))

-- Myhill-Nerode (3)

/-- The minimal DFA `M` accepting `l` is unique up to unique isomorphism. -/
@[simp]
theorem unique_minimal_dfa (M : DA.FinAcc States α) [Fintype States]
    [Fintype (Quotient (NerodeCongruence (language M)).eq)] (hMin : IsMinimalAutomaton M) :
    ∃! φ : States ≃ Quotient (NerodeCongruence (language M)).eq,
      ∀ x, φ (M.mtr M.start x) = ⟦ x ⟧ := by
  haveI : Finite States := @Fintype.finite States ‹Fintype States›
  let φ : States → Quotient (NerodeCongruence (language M)).eq :=
    fun s => ⟦Classical.epsilon (fun x : List α => M.mtr M.start x = s)⟧
  have hφ : ∀ x, φ (M.mtr M.start x) = ⟦x⟧ := fun x => by
    apply Quotient.sound
    apply statecongruence_refines_nerodecongruence
    intro z
    have := @Classical.epsilon_spec _ (fun y : List α => M.mtr M.start y = M.mtr M.start x) ⟨x, rfl⟩
    simp only [FLTS.mtr, List.foldl_append] at this ⊢; rw [this]
  have hφ_surj : Function.Surjective φ := fun q =>
    q.inductionOn (fun x => ⟨M.mtr M.start x, hφ x⟩)
  have hφ_inj : Function.Injective φ :=
    hφ_surj.injective_of_finite (Fintype.equivOfCardEq hMin)
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
