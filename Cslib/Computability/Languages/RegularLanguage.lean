/-
Copyright (c) 2025 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Automata.DA.Congr
public import Cslib.Computability.Automata.DA.Prod
public import Cslib.Computability.Automata.DA.ToNA
public import Cslib.Computability.Automata.EpsilonNA.OfRegularExpression
public import Cslib.Computability.Automata.EpsilonNA.ToNA
public import Cslib.Computability.Automata.NA.Preimage
public import Cslib.Computability.Automata.NA.Reverse
public import Cslib.Computability.Automata.NA.ToDA
public import Cslib.Computability.Automata.NA.ToEpsilonNA
public import Cslib.Computability.Automata.TwoWayNA.ComplToNA
public import Cslib.Computability.Automata.TwoWayNA.OfNA
public import Cslib.Computability.Languages.KleeneAlgorithm
public import Mathlib.Computability.DFA

/-!
# Regular languages
-/

@[expose] public section

namespace Cslib.Language

open Set List Prod Automata Acceptor
open scoped Computability FLTS DA NA DA.FinAcc NA.FinAcc

variable {Symbol Symbol' : Type*}

/-- A characterization of `Language.IsRegular` in terms of `DA`. This is the only theorem in Cslib
in which Mathlib's definition of `Language.IsRegular` is used. -/
theorem IsRegular.iff_dfa {l : Language Symbol} :
    l.IsRegular ↔ ∃ State : Type, ∃ _ : Finite State,
      ∃ dfa : DA.FinAcc State Symbol, language dfa = l := by
  constructor
  · rintro ⟨State, h_fin, ⟨tr, start, acc⟩, rfl⟩
    let dfa := DA.FinAcc.mk {tr, start} acc
    use State, Fintype.finite h_fin, dfa
    rfl
  · rintro ⟨State, h_fin, ⟨⟨flts, start⟩, acc⟩, rfl⟩
    let dfa := DFA.mk flts.tr start acc
    use State, Fintype.ofFinite State, dfa
    rfl

/-- A characterization of Language.IsRegular in terms of NA. -/
theorem IsRegular.iff_nfa {l : Language Symbol} :
    l.IsRegular ↔ ∃ State : Type, ∃ _ : Finite State,
      ∃ nfa : NA.FinAcc State Symbol, language nfa = l := by
  rw [IsRegular.iff_dfa]; constructor
  · rintro ⟨State, h_fin, ⟨da, acc⟩, rfl⟩
    use State, h_fin, ⟨da.toNA, acc⟩
    grind
  · rintro ⟨State, _, na, rfl⟩
    use Set State, inferInstance, na.toDAFinAcc
    grind

/-- A characterization of `Language.IsRegular` in terms of `εNA`. -/
theorem IsRegular.iff_epsilon_nfa {l : Language Symbol} :
    l.IsRegular ↔ ∃ State : Type, ∃ _ : Finite State,
      ∃ enfa : εNA.FinAcc State Symbol, language enfa = l := by
  rw [IsRegular.iff_nfa]
  constructor
  · rintro ⟨State, h_fin, nfa, rfl⟩
    exact ⟨State, h_fin, nfa.toEpsilonNAFinAcc, NA.FinAcc.toEpsilonNAFinAcc_language_eq⟩
  · rintro ⟨State, h_fin, enfa, rfl⟩
    exact ⟨State, h_fin, enfa.toNAFinAcc, εNA.FinAcc.toNAFinAcc_language_eq⟩

/-- The complementation of a regular language is regular. -/
theorem IsRegular.compl {l : Language Symbol} (h : l.IsRegular) : (lᶜ).IsRegular := by
  rw [IsRegular.iff_dfa] at h ⊢
  obtain ⟨State, _, ⟨da, acc⟩, rfl⟩ := h
  use State, inferInstance, ⟨da, accᶜ⟩
  #adaptation_note
  /-- A grind regression found moving to nightly-2026-03-31 (changes from lean#13166) -/
  ext
  simp only [language, Accepts]
  rfl

/-- A language is regular if and only if it is accepted by some two-way nondeterministic
automaton with finitely many states. -/
theorem IsRegular.iff_twoWayNA {l : Language Symbol} :
    l.IsRegular ↔ ∃ State : Type, ∃ _ : Finite State,
      ∃ a : TwoWayNA State Symbol, language a = l := by
  constructor
  · intro h
    rw [IsRegular.iff_nfa] at h
    obtain ⟨State, hfin, na, rfl⟩ := h
    exact ⟨State, hfin, NA.FinAcc.toTwoWayNA na, TwoWayNA.language_toTwoWayNA na⟩
  · rintro ⟨State, hfin, a, rfl⟩
    have := hfin
    have hc : (language a)ᶜ.IsRegular := by
      rw [IsRegular.iff_nfa]
      exact ⟨Set State × Set State, inferInstance, a.complToNA, a.language_complToNA⟩
    simpa using hc.compl

/-- The empty language is regular. -/
@[simp]
theorem IsRegular.zero : (0 : Language Symbol).IsRegular := by
  rw [IsRegular.iff_dfa]
  let flts := FLTS.mk (fun () (_ : Symbol) ↦ ())
  use Unit, inferInstance, ⟨DA.mk flts (), ∅⟩
  #adaptation_note
  /-- A grind regression found moving to nightly-2026-03-31 (changes from lean#13166) -/
  ext
  simp only [language, Accepts]
  rfl

/-- The language containing only the empty word is regular. -/
@[simp]
theorem IsRegular.one : (1 : Language Symbol).IsRegular := by
  rw [IsRegular.iff_dfa]
  let flts := FLTS.mk (fun (_ : Fin 2) (_ : Symbol) ↦ 1)
  use Fin 2, inferInstance, ⟨DA.mk flts 0, {0}⟩
  ext; constructor
  #adaptation_note
  /-- A grind regression found moving to nightly-2026-03-31 (changes from lean#13166) -/
  · intro h; by_contra h'
    have := dropLast_append_getLast h'
    grind [Accepts]
  · grind [Accepts, Language.mem_one]

/-- The language of all finite words is regular. -/
@[simp]
theorem IsRegular.top : (⊤ : Language Symbol).IsRegular := by
  have : (⊥ᶜ : Language Symbol).IsRegular := IsRegular.compl <| IsRegular.zero
  rwa [← compl_bot]

/-- The intersection of two regular languages is regular. -/
@[simp]
theorem IsRegular.inf {l1 l2 : Language Symbol}
    (h1 : l1.IsRegular) (h2 : l2.IsRegular) : (l1 ⊓ l2).IsRegular := by
  rw [IsRegular.iff_dfa] at h1 h2 ⊢
  obtain ⟨State1, h_fin1, ⟨da1, acc1⟩, rfl⟩ := h1
  obtain ⟨State2, h_fin1, ⟨da2, acc2⟩, rfl⟩ := h2
  use State1 × State2, inferInstance, ⟨da1.prod da2, fst ⁻¹' acc1 ∩ snd ⁻¹' acc2⟩
  #adaptation_note
  /-- A grind regression found moving to nightly-2026-03-31 (changes from lean#13166) -/
  ext; grind [Accepts, Language.mem_inf]

/-- The union of two regular languages is regular. -/
@[simp]
theorem IsRegular.add {l1 l2 : Language Symbol}
    (h1 : l1.IsRegular) (h2 : l2.IsRegular) : (l1 + l2).IsRegular := by
  rw [IsRegular.iff_dfa] at h1 h2 ⊢
  obtain ⟨State1, h_fin1, ⟨da1, acc1⟩, rfl⟩ := h1
  obtain ⟨State2, h_fin1, ⟨da2, acc2⟩, rfl⟩ := h2
  use State1 × State2, inferInstance, ⟨da1.prod da2, fst ⁻¹' acc1 ∪ snd ⁻¹' acc2⟩
  #adaptation_note
  /-- A grind regression found moving to nightly-2026-03-31 (changes from lean#13166) -/
  ext; grind [Accepts, Language.mem_add]

/-- The intersection of any finite number of regular languages is regular. -/
@[simp]
theorem IsRegular.iInf {I : Type*} [Finite I] {s : Set I} {l : I → Language Symbol}
    (h : ∀ i ∈ s, (l i).IsRegular) : (⨅ i ∈ s, l i).IsRegular := by
  generalize h_n : s.ncard = n
  induction n generalizing s
  case zero => simp_all [ncard_eq_zero (s := s)]
  case succ n h_ind =>
    obtain ⟨i, t, h_i, rfl, rfl⟩ := (ncard_eq_succ (s := s)).mp h_n
    rw [iInf_insert]
    grind [IsRegular.inf]

/-- The union of any finite number of regular languages is regular. -/
@[simp]
theorem IsRegular.iSup {I : Type*} [Finite I] {s : Set I} {l : I → Language Symbol}
    (h : ∀ i ∈ s, (l i).IsRegular) : (⨆ i ∈ s, l i).IsRegular := by
  generalize h_n : s.ncard = n
  induction n generalizing s
  case zero =>
    obtain ⟨rfl⟩ := (ncard_eq_zero (s := s)).mp h_n
    simp only [mem_empty_iff_false, not_false_eq_true, iSup_neg, iSup_bot]
    exact IsRegular.zero
  case succ n h_ind =>
    obtain ⟨i, t, h_i, rfl, rfl⟩ := (ncard_eq_succ (s := s)).mp h_n
    rw [iSup_insert]
    apply IsRegular.add <;> grind

/-- The concatenation of two regular languages is regular. -/
@[simp]
theorem IsRegular.mul {l1 l2 : Language Symbol}
    (h1 : l1.IsRegular) (h2 : l2.IsRegular) : (l1 * l2).IsRegular := by
  rw [IsRegular.iff_epsilon_nfa] at h1 h2 ⊢
  obtain ⟨State1, h_fin1, a1, rfl⟩ := h1
  obtain ⟨State2, h_fin2, a2, rfl⟩ := h2
  exact ⟨State1 ⊕ State2, inferInstance, a1.concat a2, εNA.FinAcc.language_concat a1 a2⟩

/-- The Kleene star of a regular language is regular. -/
@[simp]
theorem IsRegular.kstar {l : Language Symbol}
    (h : l.IsRegular) : (l∗).IsRegular := by
  rw [IsRegular.iff_epsilon_nfa] at h ⊢
  obtain ⟨State, h_fin, a, rfl⟩ := h
  exact ⟨Unit ⊕ State, inferInstance, a.star, εNA.FinAcc.language_star a⟩

open _root_.Language RightCongruence in
/-- If a right congruence is of finite index, then each of its equivalence classes is regular. -/
@[simp]
theorem IsRegular.congr_fin_index {Symbol : Type}
    [c : RightCongruence Symbol] [Finite (Quotient c.eq)]
    (a : Quotient c.eq) : (eqvCls a).IsRegular := by
  rw [IsRegular.iff_dfa]
  use Quotient c.eq, inferInstance, ⟨c.toDA, {a}⟩
  exact DA.FinAcc.congr_language_eq

open NA in
/-- The reversal of a regular language is regular. -/
theorem IsRegular.reverse {l : Language Symbol} (h : l.IsRegular) : l.reverse.IsRegular := by
  rw [IsRegular.iff_nfa] at h ⊢
  obtain ⟨State, h_fin, nfa, rfl⟩ := h
  use State, inferInstance, nfa.reverse, nfa.reverse_language_eq

/-- A language is regular iff its reversal is regular. -/
@[simp]
theorem IsRegular.reverse_iff {l : Language Symbol} : l.reverse.IsRegular ↔ l.IsRegular := by
  constructor
  · intro h
    simpa using IsRegular.reverse h
  · exact IsRegular.reverse

open NA _root_.Language in
/-- The preimage of a regular languge under a language homomorphism is regular. -/
theorem IsRegular.preimage (f : Hom Symbol' Symbol) {l : Language Symbol} (h : l.IsRegular) :
    (l.preimage f).IsRegular := by
  rw [IsRegular.iff_nfa] at h ⊢
  obtain ⟨State, h_fin, nfa, rfl⟩ := h
  use State, inferInstance, nfa.preimage f, nfa.preimage_language_eq f

/-- The language containing only the one character string `a` is regular. -/
@[simp]
theorem IsRegular.char (a : Symbol) : ({[a]} : Language Symbol).IsRegular :=
  IsRegular.iff_epsilon_nfa.mpr
    ⟨Bool, inferInstance, εNA.FinAcc.char a, εNA.FinAcc.language_char a⟩

/-- Languages matching regular expressions are regular. -/
theorem IsRegular.regex (r : RegularExpression Symbol) : r.matches'.IsRegular :=
  IsRegular.iff_epsilon_nfa.mpr ⟨r.State, inferInstance, r.toEpsilonNA, r.language_toEpsilonNA⟩

open RegularExpression in
/-- A characterization of `Language.IsRegular` in terms of `RegularExpression`. -/
theorem IsRegular.iff_regex [Finite Symbol] {l : Language Symbol} :
    l.IsRegular ↔ ∃ r : RegularExpression Symbol, l = matches' r := by
  constructor
  · intro h
    obtain ⟨State, _, nfa, rfl⟩ := IsRegular.iff_nfa.mp h
    exact NA.FinAcc.nfa_eq_regex nfa
  · rintro ⟨r, rfl⟩
    exact IsRegular.regex r

end Cslib.Language
