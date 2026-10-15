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
* `εNA.FinAcc.concat a b`: `ε`-transitions from the accepting states of `a` to the initial states
  of `b`.
* `εNA.FinAcc.star a`: a fresh hub state, initial and accepting, with `ε`-transitions to the
  initial states of `a` and from its accepting states.

## Main statements

* `εNA.FinAcc.language_zero`, `εNA.FinAcc.language_epsilon`, `εNA.FinAcc.language_char`,
  `εNA.FinAcc.language_union`, `εNA.FinAcc.language_concat` and `εNA.FinAcc.language_star`.

## References

* [K. Thompson, *Regular expression search algorithm*][Thompson1968]
-/

@[expose] public section

namespace Cslib.Automata.εNA.FinAcc

open Acceptor
open scoped Computability

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
    obtain rfl := Set.mem_singleton_iff.mp hs
    obtain rfl := Set.mem_singleton_iff.mp ht
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
    obtain rfl := Set.mem_singleton_iff.mp hs
    obtain rfl := Set.mem_singleton_iff.mp ht
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

/-- The transitions of `concat a b`, whose states are those of `a` followed by those of `b`. -/
inductive ConcatTr (a : FinAcc S₁ Symbol) (b : FinAcc S₂ Symbol) :
    S₁ ⊕ S₂ → Option Symbol → S₁ ⊕ S₂ → Prop
  | left {s μ s'} : a.Tr s μ s' → ConcatTr a b (.inl s) μ (.inl s')
  | right {s μ s'} : b.Tr s μ s' → ConcatTr a b (.inr s) μ (.inr s')
  | bridge {s s'} : s ∈ a.accept → s' ∈ b.start → ConcatTr a b (.inl s) none (.inr s')

/-- The concatenation of `a` and `b`: `ε`-transitions lead from the accepting states of `a` to the
initial states of `b`. -/
def concat (a : FinAcc S₁ Symbol) (b : FinAcc S₂ Symbol) : FinAcc (S₁ ⊕ S₂) Symbol where
  Tr := ConcatTr a b
  start := .inl '' a.start
  accept := .inr '' b.accept

/-- A run of `concat a b` between two states of `b` is a run of `b`. -/
theorem concat_mTr_inr {s t : S₂} {μs : List (Option Symbol)}
    (h : (concat a b).MTr (.inr s) μs (.inr t)) : b.MTr s μs t := by
  induction μs generalizing s with
  | nil =>
    cases h
    exact .refl
  | cons μ μs ih =>
    obtain ⟨y, htr, h'⟩ := LTS.MTr.cons_iff.mp h
    cases htr with
    | right htr => exact .stepL htr (ih h')

/-- A run of `concat a b` from a state of `a` to a state of `b` is a run of `a` to an accepting
state, an `ε`-transition to an initial state of `b`, and a run of `b`. -/
theorem concat_mTr_inl {s : S₁} {t : S₂} {μs : List (Option Symbol)}
    (h : (concat a b).MTr (.inl s) μs (.inr t)) :
    ∃ s₁ ∈ a.accept, ∃ s₂ ∈ b.start, ∃ μs₁ μs₂, a.MTr s μs₁ s₁ ∧ b.MTr s₂ μs₂ t ∧
      μs = μs₁ ++ none :: μs₂ := by
  induction μs generalizing s with
  | nil => cases h
  | cons μ μs ih =>
    obtain ⟨y, htr, h'⟩ := LTS.MTr.cons_iff.mp h
    cases htr with
    | left htr =>
      obtain ⟨s₁, hs₁, s₂, hs₂, μs₁, μs₂, h₁, h₂, rfl⟩ := ih h'
      exact ⟨s₁, hs₁, s₂, hs₂, μ :: μs₁, μs₂, .stepL htr h₁, h₂, rfl⟩
    | bridge hs hs' =>
      exact ⟨s, hs, _, hs', [], μs, .refl, concat_mTr_inr h', rfl⟩

@[simp]
theorem language_concat (a : FinAcc S₁ Symbol) (b : FinAcc S₂ Symbol) :
    language (concat a b) = language a * language b := by
  ext xs
  rw [Language.mem_mul, mem_language_iff]
  constructor
  · rintro ⟨_, hs', _, ht', μs, rfl, h⟩
    obtain ⟨s, hs, rfl⟩ := (Set.mem_image _ _ _).mp hs'
    obtain ⟨t, ht, rfl⟩ := (Set.mem_image _ _ _).mp ht'
    obtain ⟨s₁, hs₁, s₂, hs₂, μs₁, μs₂, h₁, h₂, rfl⟩ := concat_mTr_inl h
    exact ⟨μs₁.reduceOption, mem_language_iff.mpr ⟨s, hs, s₁, hs₁, μs₁, rfl, h₁⟩,
      μs₂.reduceOption, mem_language_iff.mpr ⟨s₂, hs₂, t, ht, μs₂, rfl, h₂⟩,
      by simp [List.reduceOption_append]⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    obtain ⟨s, hs, s₁, hs₁, μs₁, rfl, h₁⟩ := mem_language_iff.mp hx
    obtain ⟨s₂, hs₂, t, ht, μs₂, rfl, h₂⟩ := mem_language_iff.mp hy
    refine ⟨.inl s, Set.mem_image_of_mem _ hs, .inr t, Set.mem_image_of_mem _ ht,
      μs₁ ++ none :: μs₂,
      by simp [List.reduceOption_append], ?_⟩
    have hcopy₁ : (concat a b).MTr (.inl s) μs₁ (.inl s₁) :=
      h₁.map (fun s => (.inl s : S₁ ⊕ S₂)) fun _ _ _ => ConcatTr.left
    have hcopy₂ : (concat a b).MTr (.inr s₂) μs₂ (.inr t) :=
      h₂.map (fun s => (.inr s : S₁ ⊕ S₂)) fun _ _ _ => ConcatTr.right
    exact hcopy₁.comp _ (.stepL (ConcatTr.bridge hs₁ hs₂) hcopy₂)

/-- The transitions of `star a`, whose states are a fresh hub `inl ()` and the states of `a`. -/
inductive StarTr (a : FinAcc S₁ Symbol) : Unit ⊕ S₁ → Option Symbol → Unit ⊕ S₁ → Prop
  | inner {s μ s'} : a.Tr s μ s' → StarTr a (.inr s) μ (.inr s')
  | enter {s} : s ∈ a.start → StarTr a (.inl ()) none (.inr s)
  | exit {s} : s ∈ a.accept → StarTr a (.inr s) none (.inl ())

/-- The Kleene star of `a`: a fresh hub state, initial and accepting, with `ε`-transitions to the
initial states of `a` and from its accepting states. -/
def star (a : FinAcc S₁ Symbol) : FinAcc (Unit ⊕ S₁) Symbol where
  Tr := StarTr a
  start := {.inl ()}
  accept := {.inl ()}

/-- A run of `star a` from a state of `a` to the hub is a run of `a` to an accepting state, an
`ε`-transition to the hub, and a run from the hub back to the hub. -/
theorem star_mTr_inr {s : S₁} {μs : List (Option Symbol)}
    (h : (star a).MTr (.inr s) μs (.inl ())) :
    ∃ t ∈ a.accept, ∃ μs₁ μs₂, a.MTr s μs₁ t ∧ (star a).MTr (.inl ()) μs₂ (.inl ()) ∧
      μs = μs₁ ++ none :: μs₂ := by
  induction μs generalizing s with
  | nil => cases h
  | cons μ μs ih =>
    obtain ⟨y, htr, h'⟩ := LTS.MTr.cons_iff.mp h
    cases htr with
    | inner htr =>
      obtain ⟨t, ht, μs₁, μs₂, h₁, h₂, rfl⟩ := ih h'
      exact ⟨t, ht, μ :: μs₁, μs₂, .stepL htr h₁, h₂, rfl⟩
    | exit hs =>
      exact ⟨s, hs, [], μs, .refl, h', rfl⟩

/-- A run of `star a` from the hub back to the hub reads a word of `(language a)∗`. -/
theorem reduceOption_mem_kstar_of_star_mTr {μs : List (Option Symbol)}
    (h : (star a).MTr (.inl ()) μs (.inl ())) : μs.reduceOption ∈ (language a)∗ := by
  generalize hn : μs.length = n
  induction n using Nat.strong_induction_on generalizing μs with
  | _ n ih =>
    cases μs with
    | nil => exact Language.nil_mem_kstar _
    | cons μ μs =>
      obtain ⟨y, htr, h'⟩ := LTS.MTr.cons_iff.mp h
      cases htr with
      | enter hs =>
        obtain ⟨t, ht, μs₁, μs₂, h₁, h₂, rfl⟩ := star_mTr_inr h'
        have hlen : μs₂.length < n := by
          rw [← hn]
          simp only [List.length_cons, List.length_append]
          omega
        obtain ⟨L, hL, hLmem⟩ := Language.mem_kstar.mp (ih _ hlen h₂ rfl)
        refine Language.mem_kstar.mpr ⟨μs₁.reduceOption :: L, by
          simp [List.reduceOption_append, hL], ?_⟩
        intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact mem_language_iff.mpr ⟨_, hs, t, ht, μs₁, rfl, h₁⟩
        · exact hLmem w hw

/-- Every word of `(language a)∗` is read by a run of `star a` from the hub back to the hub. -/
theorem exists_star_mTr_of_mem_kstar {xs : List Symbol} (hxs : xs ∈ (language a)∗) :
    ∃ μs : List (Option Symbol), μs.reduceOption = xs ∧ (star a).MTr (.inl ()) μs (.inl ()) := by
  obtain ⟨L, rfl, hL⟩ := Language.mem_kstar.mp hxs
  clear hxs
  induction L with
  | nil => exact ⟨[], rfl, .refl⟩
  | cons w L ih =>
    obtain ⟨μs₂, hμs₂, h₂⟩ := ih fun y hy => hL y (by simp [hy])
    obtain ⟨s, hs, t, ht, μs₁, rfl, h₁⟩ := mem_language_iff.mp (hL w (by simp))
    have hcopy : (star a).MTr (.inr s) μs₁ (.inr t) :=
      h₁.map (fun s => (.inr s : Unit ⊕ S₁)) fun _ _ _ => StarTr.inner
    refine ⟨none :: (μs₁ ++ none :: μs₂), by simp [List.reduceOption_append, hμs₂], ?_⟩
    exact .stepL (StarTr.enter hs) (hcopy.comp _ (.stepL (StarTr.exit ht) h₂))

@[simp]
theorem language_star (a : FinAcc S₁ Symbol) : language (star a) = (language a)∗ := by
  ext xs
  rw [mem_language_iff]
  constructor
  · rintro ⟨s, hs, t, ht, μs, rfl, h⟩
    obtain rfl := Set.mem_singleton_iff.mp hs
    obtain rfl := Set.mem_singleton_iff.mp ht
    exact reduceOption_mem_kstar_of_star_mTr h
  · intro hxs
    obtain ⟨μs, hμs, h⟩ := exists_star_mTr_of_mem_kstar hxs
    exact ⟨.inl (), Set.mem_singleton _, .inl (), Set.mem_singleton _, μs, hμs, h⟩

end Cslib.Automata.εNA.FinAcc
