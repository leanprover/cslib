/-
Copyright (c) 2025 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Automata.DA.Congr
public import Cslib.Computability.Automata.DA.Prod
public import Cslib.Computability.Automata.DA.ToNA
public import Cslib.Computability.Automata.NA.Concat
public import Cslib.Computability.Automata.NA.Loop
public import Cslib.Computability.Automata.NA.ToDA
public import Mathlib.Computability.DFA
public import Mathlib.Computability.RegularExpressions
public import Mathlib.Data.Finite.Sum
public import Mathlib.Data.Set.Card

/-!
# Regular languages
-/

@[expose] public section

namespace Cslib.Language

open Set List Prod Automata Acceptor RightCongruence
open scoped Computability FLTS DA NA DA.FinAcc NA.FinAcc

variable {Symbol : Type*}

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

open NA.FinAcc Sum in
/-- The concatenation of two regular languages is regular. -/
@[simp]
theorem IsRegular.mul {l1 l2 : Language Symbol}
    (h1 : l1.IsRegular) (h2 : l2.IsRegular) : (l1 * l2).IsRegular := by
  obtain (he | hne) := isEmpty_or_nonempty Symbol
  · obtain (rfl | rfl) := Language.eq_zero_or_one_ofIsEmpty l1 <;>
    obtain (rfl | rfl) := Language.eq_zero_or_one_ofIsEmpty l2 <;> simp
  · have := Classical.inhabited_of_nonempty hne
    rw [IsRegular.iff_nfa] at h1 h2 ⊢
    obtain ⟨State1, h_fin1, nfa1, rfl⟩ := h1
    obtain ⟨State2, h_fin1, nfa2, rfl⟩ := h2
    use Option State1 ⊕ Option State2, inferInstance,
      ⟨finConcat nfa1 nfa2, inr '' (some '' nfa2.accept)⟩
    exact finConcat_language_eq

open NA.FinAcc Sum in
/-- The Kleene star of a regular language is regular. -/
@[simp]
theorem IsRegular.kstar {l : Language Symbol}
    (h : l.IsRegular) : (l∗).IsRegular := by
  obtain (he | hne) := isEmpty_or_nonempty Symbol
  · obtain (rfl | rfl) := Language.eq_zero_or_one_ofIsEmpty l <;> simp
  · have := Classical.inhabited_of_nonempty hne
    by_cases h_l : l = 0
    · simp [h_l]
    · rw [IsRegular.iff_nfa] at h ⊢
      obtain ⟨State, h_fin, nfa, rfl⟩ := h
      use Unit ⊕ Option State, inferInstance, ⟨finLoop nfa, {inl ()}⟩, loop_language_eq h_l

/-- If a right congruence is of finite index, then each of its equivalence classes is regular. -/
@[simp]
theorem IsRegular.congr_fin_index {Symbol : Type}
    [c : RightCongruence Symbol] [Finite (Quotient c.eq)]
    (a : Quotient c.eq) : (eqvCls a).IsRegular := by
  rw [IsRegular.iff_dfa]
  use Quotient c.eq, inferInstance, ⟨c.toDA, {a}⟩
  exact DA.FinAcc.congr_language_eq

/-- The language containing only the one character string `a` is regular. -/
@[simp]
theorem IsRegular.char (a : Symbol) : ({[a]} : Language Symbol).IsRegular := by
  rw [IsRegular.iff_dfa]
  classical
  let flts := FLTS.mk (fun (s : Fin 3) (x : Symbol) ↦ if (s = 0 ∧ x = a) then 1 else 2)
  use Fin 3, inferInstance, ⟨DA.mk flts 0, {1}⟩
  ext xs
  induction xs using List.reverseRec with
  | nil => grind [Accepts, Language.mem_singleton]
  | append_singleton xs x ih =>
    simp only [mem_language, Accepts, Language.mem_singleton, FLTS.mtr_concat_eq] at ih ⊢
    constructor
    · induction xs using List.reverseRec <;> grind
    · simp_all [flts, List.append_eq_cons_iff]

/-- Languages matching regular expressions are regular. -/
theorem IsRegular.regex {r : RegularExpression Symbol} :
    r.matches'.IsRegular := by
  induction r with
  | zero => simp
  | epsilon => simp
  | char a => simp [IsRegular.char a]
  | plus P Q hP hQ => grind [RegularExpression.matches', IsRegular.add]
  | comp P Q hP hQ => grind [RegularExpression.matches', IsRegular.mul]
  | star P hP => grind [RegularExpression.matches', IsRegular.kstar]

end Cslib.Language
