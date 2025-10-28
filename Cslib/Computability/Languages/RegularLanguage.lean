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

variable {Symbol : Type _} [Finite Symbol]

theorem regular_iff_cslib_dfa {l : Language Symbol} :
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

theorem regular_iff_cslib_nfa {l : Language Symbol} :
    l.IsRegular ↔ ∃ State : Type, ∃ nfa : Cslib.NFA State Symbol, nfa.language = l := by
  rw [regular_iff_cslib_dfa] ; constructor
  · rintro ⟨State, dfa, rfl⟩
    use State, dfa.toNFA
    exact Cslib.DFA.toNFA_language_eq
  · rintro ⟨State, nfa, rfl⟩
    use (Set State), nfa.toDFA
    exact Cslib.NFA.toDFA_language_eq

open Cslib

@[simp]
theorem regular_compl {l : Language Symbol} (h : l.IsRegular) : (lᶜ).IsRegular := by
  rw [regular_iff_cslib_dfa] at h ⊢
  obtain ⟨State, dfa, rfl⟩ := h
  use State, dfa.compl
  simp

@[simp]
theorem regular_zero : (0 : Language Symbol).IsRegular := by
  rw [regular_iff_cslib_dfa]
  use Unit, DFA.zero
  simp

@[simp]
theorem regular_one : (1 : Language Symbol).IsRegular := by
  rw [regular_iff_cslib_dfa]
  use Fin 2, DFA.one
  simp

@[simp]
theorem regular_top : (⊤ : Language Symbol).IsRegular := by
  have : (⊥ᶜ : Language Symbol).IsRegular := regular_compl <| regular_zero (Symbol := Symbol)
  rwa [← compl_bot]

@[simp]
theorem regular_inf {l1 l2 : Language Symbol}
    (h1 : l1.IsRegular) (h2 : l2.IsRegular) : (l1 ⊓ l2).IsRegular := by
  rw [regular_iff_cslib_dfa] at h1 h2 ⊢
  obtain ⟨State1, dfa1, rfl⟩ := h1
  obtain ⟨State2, dfa2, rfl⟩ := h2
  use (State1 × State2), (dfa1.inf dfa2)
  simp

@[simp]
theorem regular_add {l1 l2 : Language Symbol}
    (h1 : l1.IsRegular) (h2 : l2.IsRegular) : (l1 + l2).IsRegular := by
  rw [regular_iff_cslib_dfa] at h1 h2 ⊢
  obtain ⟨State1, dfa1, rfl⟩ := h1
  obtain ⟨State2, dfa2, rfl⟩ := h2
  use (State1 × State2), (dfa1.add dfa2)
  simp

@[simp]
theorem regular_iInf {I : Type _} [Finite I] {s : Set I} {l : I → Language Symbol}
    (h : ∀ i ∈ s, (l i).IsRegular) : (⨅ i ∈ s, l i).IsRegular := by
  generalize h_n : s.ncard = n
  induction n generalizing s
  case zero =>
    obtain ⟨rfl⟩ := (ncard_eq_zero (s := s)).mp h_n
    simp only [mem_empty_iff_false, not_false_eq_true, iInf_neg, iInf_top]
    exact regular_top
  case succ n h_ind =>
    obtain ⟨i, t, h_i, rfl, rfl⟩ := (ncard_eq_succ (s := s)).mp h_n
    rw [biInf_insert]
    apply regular_inf <;> grind

@[simp]
theorem regular_iSup {I : Type _} [Finite I] {s : Set I} {l : I → Language Symbol}
    (h : ∀ i ∈ s, (l i).IsRegular) : (⨆ i ∈ s, l i).IsRegular := by
  generalize h_n : s.ncard = n
  induction n generalizing s
  case zero =>
    obtain ⟨rfl⟩ := (ncard_eq_zero (s := s)).mp h_n
    simp only [mem_empty_iff_false, not_false_eq_true, iSup_neg, iSup_bot]
    exact regular_zero
  case succ n h_ind =>
    obtain ⟨i, t, h_i, rfl, rfl⟩ := (ncard_eq_succ (s := s)).mp h_n
    rw [biSup_insert]
    apply regular_add <;> grind

end Language
