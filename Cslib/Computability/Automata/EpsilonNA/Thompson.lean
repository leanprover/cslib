/-
Copyright (c) 2026 Yusuf Demir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yusuf Demir
-/

module

public import Cslib.Computability.Automata.EpsilonNA.Basic
public import Cslib.Computability.Languages.Language
import Mathlib.Data.List.ReduceOption

/-! # Thompson's construction

Thompson's construction turns a regular expression into an `εNA` with a single initial and a single
accepting state [Thompson1968]. This file defines the automata it is assembled from, with their
languages.

## Main definitions

* `εNA.FinAcc.zero`, `εNA.FinAcc.epsilon`, `εNA.FinAcc.char x`: automata for the empty language,
  the empty word and the word `[x]`.
* `εNA.FinAcc.union a b`: a fresh initial state with `ε`-transitions to the initial states of `a`
  and `b`, and a fresh accepting state reached by `ε`-transitions from their accepting states.

## Main statements

* `εNA.FinAcc.language_zero`, `εNA.FinAcc.language_epsilon`, `εNA.FinAcc.language_char` and
  `εNA.FinAcc.language_union`.

## References

* [K. Thompson, *Regular expression search algorithm*][Thompson1968]
-/

@[expose] public section

namespace Cslib.Automata.εNA.FinAcc

open Acceptor

variable {Symbol S₁ S₂ : Type*}

/-- An automaton with a single state, initial but not accepting, and no transitions. -/
def zero : FinAcc Unit Symbol where
  Tr _ _ _ := False
  start := {()}
  accept := ∅

/-- An automaton with a single state, initial and accepting, and no transitions. -/
def epsilon : FinAcc Unit Symbol where
  Tr _ _ _ := False
  start := {()}
  accept := {()}

/-- An automaton with two states, `false` initial and `true` accepting, joined by an
`x`-transition. -/
def char (x : Symbol) : FinAcc Bool Symbol where
  Tr s μ s' := s = false ∧ μ = some x ∧ s' = true
  start := {false}
  accept := {true}

@[simp]
theorem language_zero : language (zero : FinAcc Unit Symbol) = 0 := by
  ext xs
  rw [mem_language_iff]
  simp [zero]

@[simp]
theorem language_epsilon : language (epsilon : FinAcc Unit Symbol) = 1 := by
  ext xs
  rw [mem_language_iff, Language.mem_one]
  constructor
  · rintro ⟨_, -, _, -, μs, rfl, h⟩
    cases h with
    | refl => rfl
    | stepL htr _ => exact (htr : False).elim
  · rintro rfl
    exact ⟨(), Set.mem_singleton _, (), Set.mem_singleton _, [], rfl, .refl⟩

@[simp]
theorem language_char (x : Symbol) : language (char x) = {[x]} := by
  ext xs
  rw [mem_language_iff, Language.mem_singleton]
  constructor
  · rintro ⟨s, hs, t, ht, μs, rfl, h⟩
    obtain rfl : s = false := hs
    obtain rfl : t = true := ht
    cases h with
    | stepL htr h' =>
      obtain ⟨-, rfl, rfl⟩ := htr
      cases h' with
      | refl => rfl
      | stepL htr' _ =>
        obtain ⟨hf, -⟩ := htr'
        cases hf
  · rintro rfl
    exact ⟨false, Set.mem_singleton _, true, Set.mem_singleton _, [some x], rfl,
      .single _ ⟨rfl, rfl, rfl⟩⟩

/-- The transitions of `union a b`, whose states are a fresh initial state `inl false`, a fresh
accepting state `inl true`, and the states of `a` and `b`. -/
inductive UnionTr (a : FinAcc S₁ Symbol) (b : FinAcc S₂ Symbol) :
    Bool ⊕ (S₁ ⊕ S₂) → Option Symbol → Bool ⊕ (S₁ ⊕ S₂) → Prop
  | left {s μ s'} : a.Tr s μ s' → UnionTr a b (.inr (.inl s)) μ (.inr (.inl s'))
  | right {s μ s'} : b.Tr s μ s' → UnionTr a b (.inr (.inr s)) μ (.inr (.inr s'))
  | startLeft {s} : s ∈ a.start → UnionTr a b (.inl false) none (.inr (.inl s))
  | startRight {s} : s ∈ b.start → UnionTr a b (.inl false) none (.inr (.inr s))
  | acceptLeft {s} : s ∈ a.accept → UnionTr a b (.inr (.inl s)) none (.inl true)
  | acceptRight {s} : s ∈ b.accept → UnionTr a b (.inr (.inr s)) none (.inl true)

/-- The union of `a` and `b`: a fresh initial state with `ε`-transitions to the initial states of
`a` and `b`, and a fresh accepting state reached by `ε`-transitions from their accepting
states. -/
def union (a : FinAcc S₁ Symbol) (b : FinAcc S₂ Symbol) : FinAcc (Bool ⊕ (S₁ ⊕ S₂)) Symbol where
  Tr := UnionTr a b
  start := {.inl false}
  accept := {.inl true}

variable {a : FinAcc S₁ Symbol} {b : FinAcc S₂ Symbol}

/-- The fresh accepting state of `union a b` has no outgoing transitions. -/
theorem union_mTr_inl_true {μs : List (Option Symbol)} {y : Bool ⊕ (S₁ ⊕ S₂)}
    (h : (union a b).MTr (.inl true) μs y) : μs = [] ∧ y = .inl true := by
  cases h with
  | refl => exact ⟨rfl, rfl⟩
  | stepL htr _ => cases htr

/-- A run of `union a b` from a state of `a` to the fresh accepting state is a run of `a` to an
accepting state, followed by an `ε`-transition. -/
theorem union_mTr_left {s : S₁} {μs : List (Option Symbol)}
    (h : (union a b).MTr (.inr (.inl s)) μs (.inl true)) :
    ∃ t ∈ a.accept, ∃ μs', a.MTr s μs' t ∧ μs = μs' ++ [none] := by
  induction μs generalizing s with
  | nil => cases h
  | cons μ μs ih =>
    obtain ⟨y, htr, h'⟩ := LTS.MTr.cons_iff.mp h
    cases htr with
    | left htr =>
      obtain ⟨t, ht, μs', hrun, rfl⟩ := ih h'
      exact ⟨t, ht, μ :: μs', .stepL htr hrun, rfl⟩
    | acceptLeft hs =>
      obtain ⟨rfl, -⟩ := union_mTr_inl_true h'
      exact ⟨s, hs, [], .refl, rfl⟩

/-- A run of `union a b` from a state of `b` to the fresh accepting state is a run of `b` to an
accepting state, followed by an `ε`-transition. -/
theorem union_mTr_right {s : S₂} {μs : List (Option Symbol)}
    (h : (union a b).MTr (.inr (.inr s)) μs (.inl true)) :
    ∃ t ∈ b.accept, ∃ μs', b.MTr s μs' t ∧ μs = μs' ++ [none] := by
  induction μs generalizing s with
  | nil => cases h
  | cons μ μs ih =>
    obtain ⟨y, htr, h'⟩ := LTS.MTr.cons_iff.mp h
    cases htr with
    | right htr =>
      obtain ⟨t, ht, μs', hrun, rfl⟩ := ih h'
      exact ⟨t, ht, μ :: μs', .stepL htr hrun, rfl⟩
    | acceptRight hs =>
      obtain ⟨rfl, -⟩ := union_mTr_inl_true h'
      exact ⟨s, hs, [], .refl, rfl⟩

@[simp]
theorem language_union (a : FinAcc S₁ Symbol) (b : FinAcc S₂ Symbol) :
    language (union a b) = language a + language b := by
  ext xs
  rw [Language.mem_add, mem_language_iff, mem_language_iff, mem_language_iff]
  constructor
  · rintro ⟨s, hs, t, ht, μs, rfl, h⟩
    obtain rfl : s = .inl false := hs
    obtain rfl : t = .inl true := ht
    cases μs with
    | nil => cases h
    | cons μ μs =>
      obtain ⟨y, htr, h'⟩ := LTS.MTr.cons_iff.mp h
      cases htr with
      | startLeft hs =>
        obtain ⟨t, ht, μs', hrun, rfl⟩ := union_mTr_left h'
        exact .inl ⟨_, hs, t, ht, μs', by simp [List.reduceOption_append], hrun⟩
      | startRight hs =>
        obtain ⟨t, ht, μs', hrun, rfl⟩ := union_mTr_right h'
        exact .inr ⟨_, hs, t, ht, μs', by simp [List.reduceOption_append], hrun⟩
  · rintro (⟨s, hs, t, ht, μs, rfl, h⟩ | ⟨s, hs, t, ht, μs, rfl, h⟩)
    · refine ⟨.inl false, Set.mem_singleton _, .inl true, Set.mem_singleton _,
        none :: (μs ++ [none]), by simp [List.reduceOption_append], ?_⟩
      have hcopy : (union a b).MTr (.inr (.inl s)) μs (.inr (.inl t)) :=
        h.map (fun s => (.inr (.inl s) : Bool ⊕ (S₁ ⊕ S₂))) fun _ _ _ => UnionTr.left
      exact .stepL (UnionTr.startLeft hs) (hcopy.comp _ (.single _ (UnionTr.acceptLeft ht)))
    · refine ⟨.inl false, Set.mem_singleton _, .inl true, Set.mem_singleton _,
        none :: (μs ++ [none]), by simp [List.reduceOption_append], ?_⟩
      have hcopy : (union a b).MTr (.inr (.inr s)) μs (.inr (.inr t)) :=
        h.map (fun s => (.inr (.inr s) : Bool ⊕ (S₁ ⊕ S₂))) fun _ _ _ => UnionTr.right
      exact .stepL (UnionTr.startRight hs) (hcopy.comp _ (.single _ (UnionTr.acceptRight ht)))

end Cslib.Automata.εNA.FinAcc
