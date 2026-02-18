/-
Copyright (c) 2025 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Automata.DA.Buchi
public import Cslib.Computability.Automata.NA.BuchiEquiv
public import Cslib.Computability.Automata.NA.BuchiInter
public import Cslib.Computability.Automata.NA.Pair
public import Cslib.Computability.Automata.NA.Sum
public import Cslib.Computability.Languages.ExampleEventuallyZero
public import Cslib.Foundations.Data.Set.Saturation
public import Mathlib.Data.Finite.Card
public import Mathlib.Data.Finite.Sigma
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-!
# ω-Regular languages

This file defines ω-regular languages and proves some properties of them.
-/

namespace Cslib.ωLanguage

open Set Sum Filter ωSequence Automata ωAcceptor
open scoped Computability LTS

variable {Symbol : Type*}

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
  obtain ⟨State, _, ⟨da, acc⟩, rfl⟩ := Language.IsRegular.iff_dfa.mp h
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
  simp +instances [na]

/-- The language of all ω-sequences is ω-regular. -/
@[simp]
theorem IsRegular.top : (⊤ : ωLanguage Symbol).IsRegular := by
  let na : NA.Buchi Unit Symbol := {
    Tr _ _ _ := True
    start := univ
    accept := univ }
  use Unit, inferInstance, na
  ext xs
  simp +instances only [na, NA.Buchi.instωAcceptor, mem_language, mem_univ,
    frequently_true_iff_neBot, atTop_neBot, and_true, mem_top, iff_true]
  use const ()
  grind [NA.Run]

-- TODO: fix proof to work with backward.isDefEq.respectTransparency
set_option backward.isDefEq.respectTransparency false in
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

-- TODO: fix proof to work with backward.isDefEq.respectTransparency
set_option backward.isDefEq.respectTransparency false in
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

/-- The concatenation of a regular language and an ω-regular language is ω-regular. -/
@[simp]
theorem IsRegular.hmul {l : Language Symbol} {p : ωLanguage Symbol}
    (h1 : l.IsRegular) (h2 : p.IsRegular) : (l * p).IsRegular := by
  obtain ⟨State1, h_fin1, ⟨na1, acc1⟩, rfl⟩ := Language.IsRegular.iff_nfa.mp h1
  obtain ⟨State2, h_fin1, ⟨na2, acc2⟩, rfl⟩ := h2
  use State1 ⊕ State2, inferInstance, ⟨NA.concat ⟨na1, acc1⟩ na2, inr '' acc2⟩
  exact NA.Buchi.concat_language_eq

/-- The ω-power of a regular language is an ω-regular language. -/
@[simp]
theorem IsRegular.omegaPow [Inhabited Symbol] {l : Language Symbol}
    (h : l.IsRegular) : (l^ω).IsRegular := by
  obtain ⟨State, h_fin, na, rfl⟩ := Language.IsRegular.iff_nfa.mp h
  use Unit ⊕ State, inferInstance, ⟨na.loop, {inl ()}⟩
  exact NA.Buchi.loop_language_eq

-- TODO: fix proof to work with backward.isDefEq.respectTransparency
set_option backward.isDefEq.respectTransparency false in
/-- An ω-language is regular iff it is the finite union of ω-languages of the form `L * M^ω`,
where all `L`s and `M`s are regular languages. -/
theorem IsRegular.eq_fin_iSup_hmul_omegaPow [Inhabited Symbol] (p : ωLanguage Symbol) :
    p.IsRegular ↔ ∃ n : ℕ, ∃ l m : Fin n → Language Symbol,
      (∀ i, (l i).IsRegular ∧ (m i).IsRegular) ∧ p = ⨆ i, (l i) * (m i)^ω := by
  constructor
  · rintro ⟨State, _, na, rfl⟩
    rw [NA.Buchi.language_eq_fin_iSup_hmul_omegaPow na]
    have eq_start := Finite.equivFin ↑na.start
    have eq_accept := Finite.equivFin ↑na.accept
    have eq_prod := eq_start.prodCongr eq_accept
    have eq := (eq_prod.trans finProdFinEquiv).symm
    refine ⟨Nat.card ↑na.start * Nat.card ↑na.accept,
      fun i ↦ na.pairLang (eq i).1 (eq i).2,
      fun i ↦ na.pairLang (eq i).2 (eq i).2,
      by grind [LTS.pairLang_regular], ?_⟩
    ext xs
    simp only [mem_iSup]
    refine ⟨?_, by grind⟩
    rintro ⟨s, h_s, t, h_t, h_mem⟩
    use eq.invFun (⟨s, h_s⟩, ⟨t, h_t⟩)
    simp [h_mem]
  · rintro ⟨n, l, m, _, rfl⟩
    rw [← iSup_univ]
    apply IsRegular.iSup
    grind [IsRegular.hmul, IsRegular.omegaPow]

/-- If an ω-language has a finite saturating cover made of ω-regular languages,
then it is an ω-regular language. -/
theorem IsRegular.fin_cover_saturates {I : Type*} [Finite I]
    {p : I → ωLanguage Symbol} {q : ωLanguage Symbol}
    (hs : Saturates p q) (hc : ⨆ i, p i = ⊤) (hr : ∀ i, (p i).IsRegular) : q.IsRegular := by
  rw [saturates_eq_biUnion hs hc]
  apply IsRegular.iSup
  grind

/-- If an ω-language has a finite saturating cover made of ω-regular languages,
then its complement is an ω-regular language. -/
theorem IsRegular.fin_cover_saturates_compl {I : Type*} [Finite I]
    {p : I → ωLanguage Symbol} {q : ωLanguage Symbol}
    (hs : Saturates p q) (hc : ⨆ i, p i = ⊤) (hr : ∀ i, (p i).IsRegular) : (qᶜ).IsRegular :=
  IsRegular.fin_cover_saturates (saturates_compl hs) hc hr

/-- McNaughton's Theorem. -/
proof_wanted IsRegular.iff_da_muller {p : ωLanguage Symbol} :
    p.IsRegular ↔
    ∃ (State : Type) (_ : Finite State) (da : DA.Muller State Symbol), language da = p

end Cslib.ωLanguage
