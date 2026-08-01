/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Mathlib.Order.Monotone.Defs

import Mathlib.Tactic.Ring
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

/-!
# Complexity classes for deterministic multi-tape Turing machines

This file defines the resource-bounded complexity classes for deterministic multi-tape Turing
machines on top of `DecidableInTimeAndSpace`.

## Design

The primitives `DTIME` and `DSPACE` are defined using a single bound function `ℕ → ℕ` but allow
for `O`-fuzzyness. Using this fuzzyness is justified by the space and time compression / speedup
results which are not proven here. Once we have better machinery, we can prove them and potentially
move to exact bounds.

The classes are always relative to a `Symbol` alphabet.

## Important Declarations

* `DTIME` - the class of languages decidable in time `O(t(n))` for some function `t : ℕ → ℕ`.
* `DSPACE` - the class of languages decidable in space `O(s(n))` for some function `s : ℕ → ℕ`.

Some named complexity classes are defined in the `Classes` namespace:

* `P`, `E`, `EXP`
* `L`, `PSPACE`, `ESPACE`, `EXPSPACE`
-/

@[expose] public section

open Cslib

namespace Turing.MultiTapeTM

variable {Symbol : Type} [Inhabited Symbol]

/-- Monotonicity of `DecidableInTimeAndSpace` in the time bound. -/
lemma DecidableInTimeAndSpace.mono_time {L : Language Symbol} {s : ℕ → ℕ} :
    Monotone (DecidableInTimeAndSpace L · s) := by
  intro t₁ t₂ h hd
  obtain ⟨k, sym, state, emb, tm, hcomp⟩ := hd
  refine ⟨k, sym, state, emb, tm, fun input => ?_⟩
  obtain ⟨t', ht', s', hs', hcs⟩ := hcomp input
  exact ⟨t', ht'.trans (h _), s', hs', hcs⟩

/-- Monotonicity of `DecidableInTimeAndSpace` in the space bound. -/
lemma DecidableInTimeAndSpace.mono_space {L : Language Symbol} {t : ℕ → ℕ} :
    Monotone (DecidableInTimeAndSpace L t ·) := by
  intro s₁ s₂ h hd
  obtain ⟨k, sym, state, emb, tm, hcomp⟩ := hd
  refine ⟨k, sym, state, emb, tm, fun input => ?_⟩
  obtain ⟨t', ht', s', hs', hcs⟩ := hcomp input
  exact ⟨t', ht', s', hs'.trans (h _), hcs⟩

/-- The complexity class of languages decidable in time linear in `t` by a deterministic multi-tape
Turing machine, disregarding the space requirement. -/
def DTIME (t : ℕ → ℕ) :=
  {L : Language Symbol | ∃ c₁ c₂ : ℕ, ∃ s, DecidableInTimeAndSpace L (c₁ * t · + c₂) s}

/-- The complexity class of languages decidable in space linear in `s` by a deterministic multi-tape
Turing machine, for some time bound. -/
def DSPACE (s : ℕ → ℕ) :=
  {L : Language Symbol | ∃ c₁ c₂ : ℕ, ∃ t, DecidableInTimeAndSpace L t (c₁ * s · + c₂)}

/-- `DTIME` is monotone in the time bound. -/
lemma DTIME_mono {t₁ t₂ : ℕ → ℕ} (h : t₁ ≤ t₂) :
    DTIME (Symbol := Symbol) t₁ ⊆ DTIME t₂ := by
  rintro L ⟨c₁, c₂, s, hs⟩
  exact ⟨c₁, c₂, s, hs.mono_time fun n => by gcongr; exact h n⟩

/-- `DSPACE` is monotone in the space bound. -/
lemma DSPACE_mono {s₁ s₂ : ℕ → ℕ} (h : ∀ n, s₁ n ≤ s₂ n) :
    DSPACE s₁ ⊆ (DSPACE s₂ : Set (Language Symbol)) := by
  rintro L ⟨c₁, c₂, t, ht⟩
  exact ⟨c₁, c₂, t, ht.mono_space fun n => by gcongr; exact h n⟩

namespace Classes

/-- Deterministic polynomial time. -/
def P : Set (Language Symbol) := ⋃ k, DTIME (· ^ k)

/-- Deterministic exponential time (linear exponent). -/
def E : Set (Language Symbol) := ⋃ k, DTIME fun n => 2 ^ (k * n)

/-- Deterministic exponential time (polynomial exponent). -/
def EXP : Set (Language Symbol) := ⋃ k, DTIME fun n => 2 ^ (n ^ k)

/-- Deterministic logarithmic space. -/
def L : Set (Language Symbol) := DSPACE Nat.log2

/-- Deterministic polynomial space. -/
def PSPACE : Set (Language Symbol) := ⋃ k, DSPACE fun n => n ^ k

/-- Deterministic exponential space. -/
def ESPACE : Set (Language Symbol) := ⋃ k, DSPACE fun n => 2 ^ (k * n)

/-- Deterministic exponential space. -/
def EXPSPACE : Set (Language Symbol) := ⋃ k, DSPACE fun n => 2 ^ (n ^ k)

end Classes

end Turing.MultiTapeTM
