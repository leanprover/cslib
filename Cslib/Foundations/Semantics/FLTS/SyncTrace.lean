/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Semantics.FLTS.Basic
public import Mathlib.Data.Fintype.Card

/-! # Synchronising traces

This module defines synchronising traces for `FLTS`.
-/

@[expose] public section

namespace Cslib.FLTS

variable {State Label : Type*}

/-- A trace `μs` is synchronising if following it from any two states leads to the same state. -/
def IsSyncTrace (flts : FLTS State Label) (μs : List Label) : Prop :=
  ∀ s₁ s₂ : State, flts.mtr s₁ μs = flts.mtr s₂ μs

/-- `flts` is synchronising, i.e., it has at least one synchronising trace. -/
def HasSyncTrace (flts : FLTS State Label) : Prop :=
  ∃ μs : List Label, flts.IsSyncTrace μs

/-- Černý conjecture: for any synchronising `FLTS` with `n` states, there exists a synchronising
trace of length at most `(n-1)^2`. -/
proof_wanted cerny_bound [Finite State] (flts : FLTS State Label) (h : flts.HasSyncTrace) :
    ∃ μs, flts.IsSyncTrace μs ∧ μs.length ≤ (Nat.card State - 1) ^ 2

end Cslib.FLTS
