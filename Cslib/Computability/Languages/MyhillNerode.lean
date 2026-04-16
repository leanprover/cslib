/-
Copyright (c) 2026 Akhilesh Balaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji
-/

module

public import Cslib.Computability.Languages.RegularLanguage

@[expose] public section

/-! # Myhill-Nerode Theorem

Let `l` be a language on an alphabet `α`. The Nerode congruence (referred to as `c_l`
in comments below) of a language `l` is a right congruence on strings where two strings are
related iff all their right extensions are either both in the language or both not in it.

The Myhill-Nerode theorem has three parts [WikipediaMyhillNerode2026]:

(1) `l` is regular iff `c_l` has a finite number `N` of equivalence classes.

(2) `N` is the number of states of the minimal DFA accepting `l`.

(3) The minimal DFA is unique up to unique isomorphism. That is, for any
    minimal DFA accepting `l`, there exists exactly an isomorphism from it to the
    canonical DFA whose states are the equivalence classses of `c_l`, whose
    state transitions are of the form `⟦ x ⟧ → ⟦ x ++ [a] ⟧` (where `a : α`
    and `x : List α`), whose initial state is `⟦ [] ⟧`, and whose accepting states
    are `{ ⟦ x ⟧ | x ∈ l }`.

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][Hopcroft2006]
* [T. Malkin, *COMS W3261: Computer Science Theory, Handout 3: The Myhill-Nerode Theorem
   and Implications*][Malkin2024]
* [Wikipedia contributors, Myhill–Nerode theorem][WikipediaMyhillNerode2026]
-/

variable {α State : Type*}

namespace Language

open Cslib Language Automata DA FinAcc Acceptor
open scoped RightCongruence

/-- The Nerode congruence (henceforth called `c_l`) of a language `l` is a right congruence on
strings where two strings are related iff all their right extensions are either both in the language
or both not in it. -/
instance NerodeCongruence (l : Language α) : RightCongruence α where
  r x y := ∀ z, x ++ z ∈ l ↔ y ++ z ∈ l
  iseqv.refl := fun _ _ => Iff.rfl
  iseqv.symm := fun h z => (h z).symm
  iseqv.trans := fun h_1 h_2 z => (h_1 z).trans (h_2 z)
  right_cov.elim := fun a {x y} (h : ∀ z, x ++ z ∈ l ↔ y ++ z ∈ l) z =>
    List.append_assoc x a z ▸ List.append_assoc y a z ▸ h (a ++ z)

/-- The quotient type of a Nerode congruence. -/
abbrev NerodeQuotient (l : Language α) := Quotient (l.NerodeCongruence).eq

/-- The Nerode congruence of a language `l` gives rise to a DFA where each state corresponds to an
equivalence class of the language under the Nerode congruence. Note that this is simply the DFA
given rise to by the underlying right congruence with only the accept states specified here as
`{⟦ x ⟧ | x ∈ l}`. -/
def NerodeCongruenceDA (l : Language α) : DA.FinAcc (l.NerodeQuotient) α :=
  { (l.NerodeCongruence).toDA with accept := (⟦·⟧) '' l }

variable {l : Language α}

/-- The DFA constructed from the Nerode congruence `c_l` on `l` accepts `l`. -/
@[simp, scoped grind =]
theorem nerodeCongruenceDA_language_eq (l : Language α) :
    language (l.NerodeCongruenceDA) = l := by
  ext x
  simp only [NerodeCongruenceDA, language, Acceptor.Accepts, congr_mtr_eq, Set.mem_image]
  constructor
  · rintro ⟨y, hy, heq⟩
    simpa using (Quotient.eq.mp heq []).mp (by simpa using hy)
  · exact fun hx => ⟨x, hx, rfl⟩

/-- The statement (two strings are related by the Nerode congruence `c_l` on `l` iff all their right
extensions are either both in the language or both not in it) is equivalent to stating that (all
their right extensions are either both accepted or rejected by the DFA given rise to by `c_l`.) -/
theorem da_nerodeCongruence_iff {State : Type*} (M : DA.FinAcc State α) (x y : List α) :
    ((language M).NerodeCongruence).r x y ↔
    ∀ z, M.mtr (M.mtr M.start x) z ∈ M.accept ↔ M.mtr (M.mtr M.start y) z ∈ M.accept := by
  simp only [FLTS.mtr, ← List.foldl_append]
  rfl

/-- If `l` is regular then the Nerode congruence on `l` has finitely many equivalence classes. -/
theorem IsRegular.finite_nerodeQuotient (h : l.IsRegular) :
    Finite (l.NerodeQuotient) := by
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
      rw [da_nerodeCongruence_iff]
      intro z
      have heps : M.mtr M.start (Classical.epsilon
          (fun y => M.mtr M.start y = M.mtr M.start x)) = M.mtr M.start x :=
        @Classical.epsilon_spec _ (fun y => M.mtr M.start y = M.mtr M.start x) ⟨x, rfl⟩
      rw [heps])⟩

-- Myhill-Nerode (1)

/-- `l` is regular iff the Nerode congruence on `l` has finitely many equivalence classes. -/
@[simp, scoped grind =]
theorem IsRegular.iff_finite_nerodeQuotient {l : Language α} :
    l.IsRegular ↔ Finite (l.NerodeQuotient) := by
  constructor
  · intro h
    exact IsRegular.finite_nerodeQuotient h
  · intro h
    letI : Fintype (l.NerodeQuotient) := Fintype.ofFinite _
    set e := Fintype.equivFin (l.NerodeQuotient)
    set M := l.NerodeCongruenceDA
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
      ← nerodeCongruenceDA_language_eq l, language, Acceptor.Accepts, FLTS.mtr]
    exact Iff.of_eq rfl

/-- Given a set of strings all distinguishable by `l` (i.e., not related to each other by the Nerode
congruence on `l`), the number of states in the DFA accepting `l` is at least the number of strings
in the set. -/
@[simp]
theorem dfa_num_state_ge {State : Type*} [Finite State] {l : Language α}
    {M : DA.FinAcc State α} {ws : Set (List α)} [Finite ws]
    (hws : ws.Pairwise (¬ (l.NerodeCongruence).r · ·)) (hM : language M = l) :
    Nat.card State ≥ Nat.card ws := by
  letI : Fintype State := Fintype.ofFinite _
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
      ((da_nerodeCongruence_iff M x y).mpr (fun z => heq ▸ Iff.rfl))

-- Myhill-Nerode (2)

/-- All DFAs accepting `l` must have at least as many states as the number of equivalence classes
of the Nerode congruence on `l`. -/
@[simp]
theorem dfa_num_state_min {State : Type} {M : DA.FinAcc State α} [Finite State] :
    Nat.card State ≥ Nat.card (language M).NerodeQuotient := by
  let ws : Set (List α) := Set.range
    (Quotient.out : Quotient ((language M).NerodeCongruence).eq → List α)
  haveI : Finite (language M).NerodeQuotient :=
      IsRegular.iff_finite_nerodeQuotient.mp (IsRegular.iff_dfa.mpr ⟨State, inferInstance, M, rfl⟩)
  haveI : Finite ws := Set.finite_range _ |>.to_subtype
  have hws : ws.Pairwise (fun x y => ¬((language M).NerodeCongruence).r x y) := by
    rintro _ ⟨qx, rfl⟩ _ ⟨qy, rfl⟩ hne h
    exact hne (by simpa using Quotient.sound h)
  exact (Nat.card_congr (Equiv.ofInjective _ Quotient.out_injective).symm)
    ▸ dfa_num_state_ge hws rfl
--

end Language

namespace Cslib.Automata.DA.FinAcc

open Cslib Language Automata DA FinAcc Acceptor
open scoped RightCongruence

/-- The minimal DFA accepting `l` has the same number of states as the number of equivalence classes
of the Nerode congruence on `l`. -/
def IsMinimalAutomaton (M : FinAcc State α) (l : Language α) :=
  language M = l ∧ Nat.card State = Nat.card (l.NerodeQuotient)

/-- Given a DFA `M`, two strings are related iff they reach the same state under when run through
`M`. The Nerode congruence is the state congruence with respect to the minimal DFA accepting `l`. -/
instance StateCongruence (M : FinAcc State α) : RightCongruence α where
  r x y := ∀ z, M.mtr M.start (x ++ z) = M.mtr M.start (y ++ z)
  iseqv.refl := by intro x z; rfl
  iseqv.symm  := by intro x y h z; symm; exact h z
  iseqv.trans := by intro x y z h_1 h_2 w; exact (h_1 w).trans (h_2 w)
  right_cov.elim := by
    intro a x y h z
    simpa [List.append_assoc, FLTS.mtr_concat_eq] using h (a ++ z)

variable {M : FinAcc State α}

/-- The Nerode congruence is the most coarse state congruence given a language. -/
@[simp]
theorem stateCongruence_le_nerodeCongruence :
    ∀ x y, (StateCongruence M).r x y → ((language M).NerodeCongruence).r x y := by
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

/-- The minimal DFA `M` accepting the language `l` is unique up to unique isomorphism. -/
@[simp]
theorem unique_minimal [Finite State]
    (l : Language α) (hReg : l.IsRegular) (hMin : M.IsMinimalAutomaton l) :
    ∃! φ : State ≃ l.NerodeQuotient, ∀ x, φ (M.mtr M.start x) = ⟦ x ⟧ := by
  obtain ⟨hML, hCard⟩ := hMin
  haveI : Finite (l.NerodeQuotient) :=
    Language.IsRegular.iff_finite_nerodeQuotient.mp hReg
  letI : Fintype State := Fintype.ofFinite _
  letI : Fintype (l.NerodeQuotient) := Fintype.ofFinite _
  subst hML
  let φ : State → Quotient ((language M).NerodeCongruence).eq :=
    fun s => ⟦ Classical.epsilon (fun x : List α => M.mtr M.start x = s) ⟧
  have hφ : ∀ x, φ (M.mtr M.start x) = ⟦ x ⟧ := fun x => by
    apply Quotient.sound
    apply stateCongruence_le_nerodeCongruence
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

end Cslib.Automata.DA.FinAcc
