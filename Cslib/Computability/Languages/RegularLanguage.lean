/-
Copyright (c) 2025 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Cslib.Computability.Automata.DFAToNFA
import Cslib.Computability.Automata.NFAToDFA
import Mathlib.Computability.DFA
import Mathlib.Tactic

/-!
# Regular languages
-/

open Set Function
open scoped Computability

namespace Language

variable {Symbol : Type*} [Finite Symbol]

/-- A characterization of Language.IsRegular using Cslib.DFA -/
theorem IsRegular.iff_cslib_dfa {l : Language Symbol} :
    l.IsRegular ↔ ∃ State : Type, ∃ dfa : Cslib.DFA State Symbol, dfa.language = l := by
  constructor
  · rintro ⟨State, h_State, dfa, rfl⟩
    let dfa' : Cslib.DFA State Symbol := {
      start := dfa.start
      tr := dfa.step
      accept := dfa.accept
      finite_state := Fintype.finite h_State
      finite_symbol := by infer_instance }
    use State, dfa'
    rfl
  · rintro ⟨State, dfa, rfl⟩
    let dfa' : DFA Symbol State := {
      start := dfa.start
      step := dfa.tr
      accept := dfa.accept }
    have := dfa.finite_state
    use State, (Fintype.ofFinite State), dfa'
    rfl

/-- A characterization of Language.IsRegular using Cslib.NFA -/
theorem IsRegular.iff_cslib_nfa {l : Language Symbol} :
    l.IsRegular ↔ ∃ State : Type, ∃ nfa : Cslib.NFA State Symbol, nfa.language = l := by
  rw [IsRegular.iff_cslib_dfa] ; constructor
  · rintro ⟨State, dfa, rfl⟩
    use State, dfa.toNFA
    exact Cslib.DFA.toNFA_language_eq
  · rintro ⟨State, nfa, rfl⟩
    use (Set State), nfa.toDFA
    exact Cslib.NFA.toDFA_language_eq

-- From this point onward we will use only automata from Cslib in the proofs.
open Cslib

@[simp]
theorem IsRegular.compl {l : Language Symbol} (h : l.IsRegular) : (lᶜ).IsRegular := by
  rw [IsRegular.iff_cslib_dfa] at h ⊢
  obtain ⟨State, dfa, rfl⟩ := h
  use State, dfa.compl
  simp

@[simp]
theorem IsRegular.zero : (0 : Language Symbol).IsRegular := by
  rw [IsRegular.iff_cslib_dfa]
  use Unit, DFA.zero
  simp

@[simp]
theorem IsRegular.one : (1 : Language Symbol).IsRegular := by
  rw [IsRegular.iff_cslib_dfa]
  use Fin 2, DFA.one
  simp

@[simp]
theorem IsRegular.top : (⊤ : Language Symbol).IsRegular := by
  have : (⊥ᶜ : Language Symbol).IsRegular := IsRegular.compl <| IsRegular.zero (Symbol := Symbol)
  rwa [← compl_bot]

@[simp]
theorem IsRegular.inf {l1 l2 : Language Symbol}
    (h1 : l1.IsRegular) (h2 : l2.IsRegular) : (l1 ⊓ l2).IsRegular := by
  rw [IsRegular.iff_cslib_dfa] at h1 h2 ⊢
  obtain ⟨State1, dfa1, rfl⟩ := h1
  obtain ⟨State2, dfa2, rfl⟩ := h2
  use (State1 × State2), (dfa1.inf dfa2)
  simp

@[simp]
theorem IsRegular.add {l1 l2 : Language Symbol}
    (h1 : l1.IsRegular) (h2 : l2.IsRegular) : (l1 + l2).IsRegular := by
  rw [IsRegular.iff_cslib_dfa] at h1 h2 ⊢
  obtain ⟨State1, dfa1, rfl⟩ := h1
  obtain ⟨State2, dfa2, rfl⟩ := h2
  use (State1 × State2), (dfa1.add dfa2)
  simp

@[simp]
theorem IsRegular.iInf {I : Type*} [Finite I] {s : Set I} {l : I → Language Symbol}
    (h : ∀ i ∈ s, (l i).IsRegular) : (⨅ i ∈ s, l i).IsRegular := by
  generalize h_n : s.ncard = n
  induction n generalizing s
  case zero =>
    obtain ⟨rfl⟩ := (ncard_eq_zero (s := s)).mp h_n
    simp
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
