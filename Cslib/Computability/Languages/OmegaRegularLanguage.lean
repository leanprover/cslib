/-
Copyright (c) 2025 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Cslib.Computability.Automata.DA.Buchi
import Cslib.Computability.Automata.NA.BuchiEquiv
import Cslib.Computability.Automata.NA.BuchiInter
import Cslib.Computability.Automata.NA.Sum
import Cslib.Computability.Languages.ExampleEventuallyZero
import Cslib.Computability.Languages.RegularLanguage
import Mathlib.Data.Finite.Sigma

/-!
# ω-Regular languages

This file defines ω-regular languages and proves some properties of them.
-/

open Set Function Filter Cslib.ωSequence Cslib.Automata ωAcceptor
open scoped Computability Cslib.Automata.NA.Run

universe u v

namespace Cslib.ωLanguage

variable {Symbol : Type u}

/-- An ω-language is ω-regular iff it is accepted by a
finite-state nondeterministic Buchi automaton. -/
def IsRegular (p : ωLanguage Symbol) :=
  ∃ (State : Type) (_ : Finite State) (na : NA.Buchi State Symbol), language na = p

/-- Helper lemma for `isRegular_iff` below. -/
private lemma isRegular_iff.helper.{v'} {Symbol : Type u} {p : ωLanguage Symbol}
    (h : ∃ (σ : Type v) (_ : Finite σ) (na : NA.Buchi σ Symbol), language na = p) :
    ∃ (σ' : Type v') (_ : Finite σ') (na : NA.Buchi σ' Symbol), language na = p := by
  have ⟨σ, _, na, h_na⟩ := h
  have ⟨σ', ⟨f⟩⟩ := Small.equiv_small.{v', v} (α := σ)
  use σ', Finite.of_equiv σ f, na.reindex f
  rwa [NA.Buchi.reindex_language_eq]

/-- The state space of the accepting finite-state nondeterministic Buchi automaton
can in fact be universe-polymorphic. -/
theorem isRegular_iff {p : ωLanguage Symbol} :
    p.IsRegular ↔ ∃ (σ : Type v) (_ : Finite σ) (na : NA.Buchi σ Symbol), language na = p :=
  ⟨isRegular_iff.helper, isRegular_iff.helper⟩

/-- The ω-language accepted by a finite-state deterministic Buchi automaton is ω-regular. -/
theorem IsRegular.of_da_buchi {State : Type} [Finite State] (da : DA.Buchi State Symbol) :
    (language da).IsRegular :=
  ⟨State, inferInstance, da.toNABuchi, DA.Buchi.toNABuchi_language_eq⟩

/-- There is an ω-regular language that is not accepted by any deterministic Buchi automaton,
where the automaton is not even required to be finite-state. -/
theorem IsRegular.not_da_buchi :
  ∃ (Symbol : Type) (p : ωLanguage Symbol), p.IsRegular ∧
    ¬ ∃ (State : Type) (da : DA.Buchi State Symbol), language da = p := by
  refine ⟨Fin 2, Example.eventually_zero, ?_, ?_⟩
  · use Fin 2, inferInstance, Example.eventually_zero_na,
      Example.eventually_zero_accepted_by_na_buchi
  · rintro ⟨State, ⟨da, acc⟩, _⟩
    have := Example.eventually_zero_not_omegaLim
    grind [DA.buchi_eq_finAcc_omegaLim]

/-- The ω-limit of a regular language is ω-regular. -/
@[simp]
theorem IsRegular.regular_omegaLim {l : Language Symbol}
    (h : l.IsRegular) : (l↗ω).IsRegular := by
  obtain ⟨State, _, ⟨da, acc⟩, rfl⟩ := Language.IsRegular.iff_cslib_dfa.mp h
  grind [IsRegular.of_da_buchi, =_ DA.buchi_eq_finAcc_omegaLim]

/-- The empty language is ω-regular. -/
@[simp]
theorem IsRegular.bot : (⊥ : ωLanguage Symbol).IsRegular := by
  let na : NA.Buchi Unit Symbol := {
    Tr _ _ _ := False
    start := ∅
    accept := ∅ }
  use Unit, inferInstance, na
  ext xs
  simp [na]

/-- The language of all ω-sequences is ω-regular. -/
@[simp]
theorem IsRegular.top : (⊤ : ωLanguage Symbol).IsRegular := by
  let na : NA.Buchi Unit Symbol := {
    Tr _ _ _ := True
    start := univ
    accept := univ }
  use Unit, inferInstance, na
  ext xs
  simp only [na, NA.Buchi.instωAcceptor, mem_language, mem_univ, frequently_true_iff_neBot,
    atTop_neBot, and_true, mem_top, iff_true]
  use const ()
  grind

/-- The union of two ω-regular languages is ω-regular. -/
@[simp]
theorem IsRegular.sup {p1 p2 : ωLanguage Symbol}
    (h1 : p1.IsRegular) (h2 : p2.IsRegular) : (p1 ⊔ p2).IsRegular := by
  obtain ⟨State1, h_fin1, ⟨na1, acc1⟩, rfl⟩ := h1
  obtain ⟨State2, h_fin1, ⟨na2, acc2⟩, rfl⟩ := h2
  let State : Fin 2 → Type
    | 0 => State1 | 1 => State2
  let na : (i : Fin 2) → NA (State i) Symbol
    | 0 => na1 | 1 => na2
  let acc : (i : Fin 2) → Set (State i)
    | 0 => acc1 | 1 => acc2
  have : ∀ i, Finite (State i) := by grind
  use (Σ i : Fin 2, State i), inferInstance, ⟨(NA.iSum na), (⋃ i, Sigma.mk i '' (acc i))⟩
  ext xs
  simp only [NA.Buchi.iSum_language_eq, mem_sup, mem_language]
  rw [mem_iUnion, Fin.exists_fin_two]
  grind

open NA.Buchi in
/-- The intersection of two ω-regular languages is ω-regular. -/
@[simp]
theorem IsRegular.inf {p1 p2 : ωLanguage Symbol}
    (h1 : p1.IsRegular) (h2 : p2.IsRegular) : (p1 ⊓ p2).IsRegular := by
  obtain ⟨State1, h_fin1, ⟨na1, acc1⟩, rfl⟩ := h1
  obtain ⟨State2, h_fin1, ⟨na2, acc2⟩, rfl⟩ := h2
  let State : Bool → Type
    | false => State1 | true => State2
  let na : (i : Bool) → NA (State i) Symbol
    | false => na1 | true => na2
  let acc : (i : Bool) → Set (State i)
    | false => acc1 | true => acc2
  have : ∀ i, Finite (State i) := by grind
  use (Π i : Bool, State i) × Bool, inferInstance, ⟨(interNA na acc), interAccept acc⟩
  ext xs
  simp only [inter_language_eq, mem_inf, mem_language]
  rw [mem_iInter, Bool.forall_bool]
  grind

/-- The union of any finite number of ω-regular languages is ω-regular. -/
@[simp]
theorem IsRegular.iSup {I : Type*} [Finite I] {s : Set I} {p : I → ωLanguage Symbol}
    (h : ∀ i ∈ s, (p i).IsRegular) : (⨆ i ∈ s, p i).IsRegular := by
  generalize h_n : s.ncard = n
  induction n generalizing s
  case zero =>
    have := ncard_eq_zero (s := s)
    grind [IsRegular.bot, iSup_bot]
  case succ n h_ind =>
    obtain ⟨i, t, h_i, rfl, rfl⟩ := (ncard_eq_succ).mp h_n
    rw [iSup_insert]
    grind [IsRegular.sup]

/-- The intersection of any finite number of ω-regular languages is ω-regular. -/
@[simp]
theorem IsRegular.iInf {I : Type*} [Finite I] {s : Set I} {p : I → ωLanguage Symbol}
    (h : ∀ i ∈ s, (p i).IsRegular) : (⨅ i ∈ s, p i).IsRegular := by
  generalize h_n : s.ncard = n
  induction n generalizing s
  case zero =>
    have := ncard_eq_zero (s := s)
    grind [IsRegular.top, iInf_top]
  case succ n h_ind =>
    obtain ⟨i, t, h_i, rfl, rfl⟩ := (ncard_eq_succ).mp h_n
    rw [iInf_insert]
    grind [IsRegular.inf]

/-- McNaughton's Theorem. -/
proof_wanted IsRegular.iff_da_muller {p : ωLanguage Symbol} :
    p.IsRegular ↔
    ∃ (State : Type) (_ : Finite State) (da : DA.Muller State Symbol), language da = p

end Cslib.ωLanguage
