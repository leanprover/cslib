/-
Copyright (c) 2026 Yusuf Demir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yusuf Demir
-/

module

public import Cslib.Computability.Automata.EpsilonNA.ToSingleStartAccept
public import Cslib.Computability.Languages.Language
public import Cslib.Foundations.Semantics.LTS.Simulation
public import Cslib.Foundations.Semantics.LTS.Union
public import Mathlib.Data.List.ReduceOption

/-! # Thompson's construction

Thompson's construction turns a regular expression into an `εNA` with a single initial state and
at most one accepting state [Thompson1968]. This file defines the automata it is assembled from,
with their languages.

## Main definitions

* `εNA.FinAcc.zero`, `εNA.FinAcc.epsilon`, `εNA.FinAcc.char x`: automata for the empty language,
  the empty word and the word `[x]`.
* `εNA.FinAcc.sum a b`: the states and transitions of `a` and `b` side by side, through
  `LTS.unionSum`.
* `εNA.FinAcc.union a b`: `sum a b` with a single initial and a single accepting state, through
  `toSingleStartAccept`.
* `εNA.FinAcc.concat a b`: `ε`-transitions from the accepting states of `a` to the initial states
  of `b`.
* `εNA.FinAcc.star a`: a fresh hub state, initial and accepting, with `ε`-transitions to the
  initial states of `a` and from its accepting states.

## Main statements

* `εNA.FinAcc.language_zero`, `εNA.FinAcc.language_epsilon`, `εNA.FinAcc.language_char`,
  `εNA.FinAcc.language_sum`, `εNA.FinAcc.language_union`, `εNA.FinAcc.language_concat` and
  `εNA.FinAcc.language_star`.

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

/-- The disjoint sum of `a` and `b`: their states and transitions side by side (`LTS.unionSum`),
with the initial and the accepting states of both. -/
def sum (a : FinAcc S₁ Symbol) (b : FinAcc S₂ Symbol) : FinAcc (S₁ ⊕ S₂) Symbol where
  toLTS := LTS.unionSum a.toLTS b.toLTS
  start := .inl '' a.start ∪ .inr '' b.start
  accept := .inl '' a.accept ∪ .inr '' b.accept

variable {a : FinAcc S₁ Symbol} {b : FinAcc S₂ Symbol}

@[simp]
theorem language_sum (a : FinAcc S₁ Symbol) (b : FinAcc S₂ Symbol) :
    language (sum a b) = language a + language b := by
  ext xs
  rw [Language.mem_add, mem_language_iff, mem_language_iff, mem_language_iff]
  constructor
  · rintro ⟨_, hs', _, ht', μs, rfl, h⟩
    rcases (Set.mem_union _ _ _).mp hs' with hs' | hs'
    · obtain ⟨s, hs, rfl⟩ := (Set.mem_image _ _ _).mp hs'
      obtain ⟨t, rfl, hrun⟩ := LTS.unionSum_mTr_inl h
      exact .inl ⟨s, hs, t, by simpa [sum] using ht', μs, rfl, hrun⟩
    · obtain ⟨s, hs, rfl⟩ := (Set.mem_image _ _ _).mp hs'
      obtain ⟨t, rfl, hrun⟩ := LTS.unionSum_mTr_inr h
      exact .inr ⟨s, hs, t, by simpa [sum] using ht', μs, rfl, hrun⟩
  · rintro (⟨s, hs, t, ht, μs, rfl, h⟩ | ⟨s, hs, t, ht, μs, rfl, h⟩)
    · have hcopy : (sum a b).MTr (.inl s) μs (.inl t) := LTS.unionSum_mTr_inl_iff.mpr h
      exact ⟨.inl s, Set.mem_union_left _ (Set.mem_image_of_mem _ hs), .inl t,
        Set.mem_union_left _ (Set.mem_image_of_mem _ ht), μs, rfl, hcopy⟩
    · have hcopy : (sum a b).MTr (.inr s) μs (.inr t) := LTS.unionSum_mTr_inr_iff.mpr h
      exact ⟨.inr s, Set.mem_union_right _ (Set.mem_image_of_mem _ hs), .inr t,
        Set.mem_union_right _ (Set.mem_image_of_mem _ ht), μs, rfl, hcopy⟩

/-- The union of `a` and `b`: their disjoint sum, with a single initial state and a single
accepting state added by `toSingleStartAccept`. -/
def union (a : FinAcc S₁ Symbol) (b : FinAcc S₂ Symbol) : FinAcc (Bool ⊕ (S₁ ⊕ S₂)) Symbol :=
  (sum a b).toSingleStartAccept

@[simp]
theorem language_union (a : FinAcc S₁ Symbol) (b : FinAcc S₂ Symbol) :
    language (union a b) = language a + language b := by
  rw [union, toSingleStartAccept_language_eq, language_sum]

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
    have hinl : LTS.IsSimulationMap a.toLTS (concat a b).toLTS Sum.inl :=
      fun _ _ _ => ConcatTr.left
    have hinr : LTS.IsSimulationMap b.toLTS (concat a b).toLTS Sum.inr :=
      fun _ _ _ => ConcatTr.right
    exact (hinl.sim_trace h₁).comp _ (.stepL (ConcatTr.bridge hs₁ hs₂) (hinr.sim_trace h₂))

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
    have hinr : LTS.IsSimulationMap a.toLTS (star a).toLTS Sum.inr := fun _ _ _ => StarTr.inner
    refine ⟨none :: (μs₁ ++ none :: μs₂), by simp [List.reduceOption_append, hμs₂], ?_⟩
    exact .stepL (StarTr.enter hs) ((hinr.sim_trace h₁).comp _ (.stepL (StarTr.exit ht) h₂))

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
