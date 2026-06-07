/-
Copyright (c) 2026 Akhilesh Balaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji, Ching-Tsun Chou
-/

module

public import Cslib.Computability.Languages.RegularLanguage
public import Mathlib.Data.Finite.Card

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

@[expose] public section

variable {α : Type}

namespace Language

open Cslib Language Automata DA FinAcc Acceptor Function
open scoped RightCongruence

/-- The Nerode congruence (henceforth called `c_l`) of a language `l` is a right congruence on
strings where two strings are related iff all their right extensions are either both in the language
or both not in it. -/
@[implicit_reducible]
def NerodeCongruence (l : Language α) : RightCongruence α where
  r x y := ∀ z, x ++ z ∈ l ↔ y ++ z ∈ l
  iseqv.refl := by grind
  iseqv.symm := by grind
  iseqv.trans := by grind
  right_cov.elim := by grind [Covariant]

/-- The quotient type of a Nerode congruence. -/
abbrev NerodeQuotient (l : Language α) := Quotient l.NerodeCongruence.eq

/-- The Nerode congruence of a language `l` gives rise to a DFA where each state corresponds to an
equivalence class of the language under the Nerode congruence. Note that this is simply the DFA
given rise to by the underlying right congruence with only the accept states specified here as
`{⟦ x ⟧ | x ∈ l}`. -/
def NerodeCongruenceDA (l : Language α) : DA.FinAcc (l.NerodeQuotient) α :=
  FinAcc.mk l.NerodeCongruence.toDA ((⟦·⟧) '' l)

variable {l : Language α}

/-- The DFA constructed from the Nerode congruence `c_l` on `l` accepts `l`. -/
@[simp, scoped grind =]
theorem nerodeCongruenceDA_language_eq (l : Language α) :
    language (l.NerodeCongruenceDA) = l := by
  ext x
  simp only [NerodeCongruenceDA, language, Acceptor.Accepts, congr_mtr_eq, Set.mem_image]
  constructor
  · rintro ⟨y, hy, heq⟩
    have h1 := Quotient.eq.mp heq []
    simp only [List.append_nil] at h1
    simpa [← h1]
  · intro hx
    use x, hx

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
  obtain ⟨State, hFin, M, hM⟩ := IsRegular.iff_dfa.mp h
  rw [← hM]
  apply Finite.of_surjective (fun s ↦ ⟦ Classical.epsilon (fun x ↦ M.mtr M.start x = s) ⟧)
  intro q
  induction q using Quotient.inductionOn with
  | h x =>
    use M.mtr M.start x
    apply Quotient.sound
    simp [da_nerodeCongruence_iff,
      @Classical.epsilon_spec _ (fun y ↦ M.mtr M.start y = M.mtr M.start x) ⟨x, rfl⟩]

-- Myhill-Nerode (1)

/-- `l` is regular iff the Nerode congruence on `l` has finitely many equivalence classes. -/
@[scoped grind =]
theorem IsRegular.iff_finite_nerodeQuotient {l : Language α} :
    l.IsRegular ↔ Finite (l.NerodeQuotient) := by
  constructor
  · intro h
    exact IsRegular.finite_nerodeQuotient h
  · intro h
    apply IsRegular.iff_dfa.mpr
    use l.NerodeQuotient, h, l.NerodeCongruenceDA, nerodeCongruenceDA_language_eq l

/-- Given a set of strings all distinguishable by `l` (i.e., not related to each other by the Nerode
congruence on `l`), the number of states in the DFA accepting `l` is at least the number of strings
in the set. -/
theorem dfa_num_state_ge
    {l : Language α} {ws : Set (List α)} [Finite ws]
    (hws : ws.Pairwise (¬ (l.NerodeCongruence).r · ·))
    {State : Type*} [Finite State] {M : DA.FinAcc State α} (hm : language M = l) :
    Nat.card State ≥ Nat.card ws := by
  -- In this proof it is easier to work with `Fintype` rather than `Finite` because of the use of
  -- the theorem `Fintype.exists_ne_map_eq_of_card_lt` below.
  have : Fintype State := Fintype.ofFinite _
  have : Fintype ws := Fintype.ofFinite _
  simp only [Nat.card_eq_fintype_card]
  by_contra! h
  by_cases h_card : Fintype.card ws ≤ 1
  · grind [Fintype.card_pos_iff.mpr ⟨M.start⟩]
  · obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, _, _⟩ :=
      Fintype.exists_ne_map_eq_of_card_lt (f := fun w : ws ↦ M.mtr M.start w) h
    grind [hws hx hy, da_nerodeCongruence_iff M x y]

-- Myhill-Nerode (2)

/-- All DFAs accepting `l` must have at least as many states as the number of equivalence classes
of the Nerode congruence on `l`. -/
theorem dfa_num_state_min {State : Type} {M : DA.FinAcc State α} [Finite State] :
    Nat.card State ≥ Nat.card (language M).NerodeQuotient := by
  let ws : Set (List α) := Set.range (Quotient.out : NerodeQuotient (language M) → List α)
  have : Finite (language M).NerodeQuotient :=
      IsRegular.iff_finite_nerodeQuotient.mp (IsRegular.iff_dfa.mpr ⟨State, inferInstance, M, rfl⟩)
  have : Finite ws := Set.finite_range _ |>.to_subtype
  have hws : ws.Pairwise (fun x y ↦ ¬((language M).NerodeCongruence).r x y) := by
    rintro _ ⟨qx, rfl⟩ _ ⟨qy, rfl⟩ hne h
    apply hne
    simpa using Quotient.sound h
  have h1 := dfa_num_state_ge hws rfl
  rw [Nat.card_congr (Equiv.ofInjective _ Quotient.out_injective).symm] at h1
  assumption

end Language

namespace Cslib.Automata.DA.FinAcc

open Cslib Language Automata DA FinAcc Acceptor
open scoped RightCongruence

/-- The minimal DFA accepting `l` has the same number of states as the number of equivalence classes
of the Nerode congruence on `l`. -/
def IsMinimalAutomaton {State : Type*} (M : FinAcc State α) (l : Language α) :=
  language M = l ∧ Nat.card State = Nat.card l.NerodeQuotient

/-- Given a DFA `M`, two strings are related iff they reach the same state under when run through
`M`. The Nerode congruence is the state congruence with respect to the minimal DFA accepting `l`. -/
@[implicit_reducible]
def StateCongruence (M : FinAcc State α) : RightCongruence α where
  r x y := ∀ z, M.mtr M.start (x ++ z) = M.mtr M.start (y ++ z)
  iseqv.refl := by grind
  iseqv.symm  := by grind
  iseqv.trans := by grind
  right_cov.elim := by grind [Covariant]

variable {M : FinAcc State α}

/-- The Nerode congruence is the most coarse state congruence given a language. -/
theorem stateCongruence_le_nerodeCongruence {x y : List α}
    (h : (StateCongruence M).r x y) : ((language M).NerodeCongruence).r x y := by
  intro z
  grind [h z, language, Acceptor.Accepts, FLTS.mtr_concat_eq]

-- Myhill-Nerode (3)

/-- The minimal DFA `M` accepting the language `l` is unique up to unique isomorphism. -/
theorem unique_minimal [Finite State]
    (l : Language α) (hr : l.IsRegular) (hm : M.IsMinimalAutomaton l) :
    ∃! φ : State ≃ l.NerodeQuotient, ∀ x, φ (M.mtr M.start x) = ⟦ x ⟧ := by
  obtain ⟨rfl, hc⟩ := hm
  have := Language.IsRegular.iff_finite_nerodeQuotient.mp hr
  let φ : State → Quotient ((language M).NerodeCongruence).eq :=
    fun s ↦ ⟦ Classical.epsilon (fun x : List α ↦ M.mtr M.start x = s) ⟧
  have hφ (x : List α) : φ (M.mtr M.start x) = ⟦ x ⟧ := by
    apply Quotient.sound
    apply stateCongruence_le_nerodeCongruence
    intro z
    have := @Classical.epsilon_spec _ (fun y : List α ↦ M.mtr M.start y = M.mtr M.start x) ⟨x, rfl⟩
    grind [FLTS.mtr]
  have hφ_surj : Function.Surjective φ := fun q ↦ q.inductionOn (fun x ↦ ⟨M.mtr M.start x, hφ x⟩)
  have hφ_inj : Function.Injective φ := by
    have eqT := Classical.inhabited_of_nonempty <| Finite.card_eq.mp hc
    apply hφ_surj.injective_of_finite eqT.default
  use Equiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩, hφ
  intro ψ hψ
  ext s
  induction h : φ s using Quotient.inductionOn with
  | h x => grind [hφ_inj ((hφ x).trans h.symm)]

end Cslib.Automata.DA.FinAcc
