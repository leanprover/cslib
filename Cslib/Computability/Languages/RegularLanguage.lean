/-
Copyright (c) 2025 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Cslib.Computability.Automata.DAToNA
import Cslib.Computability.Automata.NAToDA
import Cslib.Computability.Automata.Prod
import Mathlib.Computability.DFA
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Common

/-!
# Regular languages
-/

open Set Function List Prod
open scoped Computability Cslib.FLTS Cslib.Automata.DA Cslib.Automata.NA Cslib.Automata.Acceptor
  Cslib.Automata.DA.FinAcc Cslib.Automata.NA.FinAcc

namespace Language

variable {Symbol : Type*}

open Cslib.Automata Acceptor in
/-- A characterization of Language.IsRegular using Cslib.DA -/
theorem IsRegular.iff_cslib_dfa {l : Language Symbol} :
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

open Cslib.Automata Acceptor in
/-- A characterization of Language.IsRegular using Cslib.NA -/
theorem IsRegular.iff_cslib_nfa {l : Language Symbol} :
    l.IsRegular ↔ ∃ State : Type, ∃ _ : Finite State,
      ∃ nfa : NA.FinAcc State Symbol, language nfa = l := by
  rw [IsRegular.iff_cslib_dfa]; constructor
  · rintro ⟨State, h_fin, ⟨da, acc⟩, rfl⟩
    use State, h_fin, ⟨da.toNA, acc⟩
    grind
  · rintro ⟨State, _, na, rfl⟩
    use Set State, inferInstance, na.toDAFinAcc
    grind

-- From this point onward we will use only automata from Cslib in the proofs.
open Cslib

@[simp]
theorem IsRegular.compl {l : Language Symbol} (h : l.IsRegular) : (lᶜ).IsRegular := by
  rw [IsRegular.iff_cslib_dfa] at h ⊢
  obtain ⟨State, _, ⟨da, acc⟩, rfl⟩ := h
  use State, inferInstance, ⟨da, accᶜ⟩
  grind

@[simp]
theorem IsRegular.zero : (0 : Language Symbol).IsRegular := by
  rw [IsRegular.iff_cslib_dfa]
  let flts := FLTS.mk (fun () (_ : Symbol) ↦ ())
  use Unit, inferInstance, ⟨Cslib.Automata.DA.mk flts (), ∅⟩
  grind

@[simp]
theorem IsRegular.one : (1 : Language Symbol).IsRegular := by
  rw [IsRegular.iff_cslib_dfa]
  let flts := FLTS.mk (fun (_ : Fin 2) (_ : Symbol) ↦ 1)
  use Fin 2, inferInstance, ⟨Cslib.Automata.DA.mk flts 0, {0}⟩
  ext; constructor
  · intro h; by_contra h'
    have := dropLast_append_getLast h'
    grind
  · grind [Language.mem_one]

@[simp]
theorem IsRegular.top : (⊤ : Language Symbol).IsRegular := by
  have : (⊥ᶜ : Language Symbol).IsRegular := IsRegular.compl <| IsRegular.zero
  rwa [← compl_bot]

@[simp]
theorem IsRegular.inf {l1 l2 : Language Symbol}
    (h1 : l1.IsRegular) (h2 : l2.IsRegular) : (l1 ⊓ l2).IsRegular := by
  rw [IsRegular.iff_cslib_dfa] at h1 h2 ⊢
  obtain ⟨State1, h_fin1, ⟨da1, acc1⟩, rfl⟩ := h1
  obtain ⟨State2, h_fin1, ⟨da2, acc2⟩, rfl⟩ := h2
  use State1 × State2, inferInstance, ⟨da1.prod da2, fst ⁻¹' acc1 ∩ snd ⁻¹' acc2⟩
  ext; grind

@[simp]
theorem IsRegular.add {l1 l2 : Language Symbol}
    (h1 : l1.IsRegular) (h2 : l2.IsRegular) : (l1 + l2).IsRegular := by
  rw [IsRegular.iff_cslib_dfa] at h1 h2 ⊢
  obtain ⟨State1, h_fin1, ⟨da1, acc1⟩, rfl⟩ := h1
  obtain ⟨State2, h_fin1, ⟨da2, acc2⟩, rfl⟩ := h2
  use State1 × State2, inferInstance, ⟨da1.prod da2, fst ⁻¹' acc1 ∪ snd ⁻¹' acc2⟩
  ext; grind [Language.mem_add]

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

end Language
