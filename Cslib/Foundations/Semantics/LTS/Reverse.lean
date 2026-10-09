/-
Copyright (c) 2026 Vignesh Karri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vignesh Karri
-/

module

public import Cslib.Foundations.Semantics.LTS.Execution

/-!
# Reverse operation for LTS

This file defines `Cslib.LTS.reverse`, which reverses every transition of an LTS.
`reverse_canReach`, `reverse_unlabelledTr`, `reverse_image`, `reverse_imageMultistep`,
`reverse_hasOutLabel` and `reverse_boundedUpTo` each state a property about `lts.reverse` in
terms of `lts`.

`reverse_mTr` states that the multistep transitions of `lts.reverse` are the reversed
multistep transitions of `lts`. `reverse_execution` is the same statement for
executions, and is derived from `Execution.reverse`.
-/

@[expose] public section

namespace Cslib.LTS

variable {State Label : Type*}

open Execution

section Reverse

/-- Constructs an LTS by reversing the transitions of an existing LTS. -/
def reverse (lts : LTS State Label) : LTS State Label where
  Tr s μ s' := lts.Tr s' μ s

/-- The transitions of `lts.reverse` are exactly the reversed transitions of `lts`. -/
@[simp]
theorem reverse_tr {lts : LTS State Label} :
    (lts.reverse).Tr s μ s' ↔ lts.Tr s' μ s := by rfl

/-- Reversing an LTS twice gives back the original LTS. -/
@[simp]
theorem reverse_reverse (lts : LTS State Label) : lts.reverse.reverse = lts := rfl

/-- Reversal of an LTS is an involution. -/
theorem reverse_involutive : Function.Involutive (reverse (Label := Label) (State := State)) :=
  reverse_reverse

theorem Execution.reverse {lts : LTS State Label} (h : lts.Execution s μs s' ss) :
    lts.reverse.Execution s' μs.reverse s ss.reverse := by
  induction h with
  | refl s => exact .refl s
  | stepL htr _ ih =>
    simpa using ih.comp (.of_tr htr)

/-- An execution of `lts.reverse` is an execution of `lts` with the labels, states
and endpoints reversed. -/
@[simp]
theorem reverse_execution {lts : LTS State Label} :
    lts.reverse.Execution s μs s' ss ↔ lts.Execution s' μs.reverse s ss.reverse :=
  ⟨fun h => h.reverse, fun h => by simpa using h.reverse⟩

/-- The multistep transitions of `lts.reverse` are exactly the reversed multistep transitions of
`lts`. -/
@[simp]
theorem reverse_mTr {lts : LTS State Label} :
    lts.reverse.MTr s' μs s ↔ lts.MTr s μs.reverse s' := by
  simp_rw [mTr_iff_execution, reverse_execution]
  conv_rhs => rw [List.reverse_involutive.surjective.exists]

/-- `lts.reverse` can reach `s'` from `s` iff `lts` can reach `s` from `s'`. -/
@[simp]
theorem reverse_canReach {lts : LTS State Label} :
    lts.reverse.CanReach s s' ↔ lts.CanReach s' s := by
  simp only [CanReach, reverse_mTr]
  conv_rhs => rw [List.reverse_involutive.surjective.exists]

/-- The unlabelled transitions of `lts.reverse` are those of `lts` with the endpoints swapped. -/
@[simp]
theorem reverse_unlabelledTr {lts : LTS State Label} :
    lts.reverse.UnlabelledTr s s' ↔ lts.UnlabelledTr s' s := Iff.rfl

/-- The `μ`-image of a state in `lts.reverse` is its `μ`-preimage in `lts`. -/
@[simp]
theorem reverse_image {lts : LTS State Label} :
    lts.reverse.image s μ = {s' | lts.Tr s' μ s} := rfl

/-- Membership form of `reverse_image`. -/
theorem mem_reverse_image {lts : LTS State Label} :
    s' ∈ lts.reverse.image s μ ↔ s ∈ lts.image s' μ := Iff.rfl

/-- The `μs`-image of a state in `lts.reverse` is its `μs.reverse`-preimage in `lts`. -/
@[simp]
theorem reverse_imageMultistep {lts : LTS State Label} :
    lts.reverse.imageMultistep s μs = {s' | lts.MTr s' μs.reverse s} :=
  Set.ext fun _ => reverse_mTr

/-- Membership version of `reverse_imageMultistep`. -/
theorem mem_reverse_imageMultistep {lts : LTS State Label} :
    s' ∈ lts.reverse.imageMultistep s μs ↔ s ∈ lts.imageMultistep s' μs.reverse := reverse_mTr

/-- A state has `μ` as an outgoing label in `lts.reverse` iff it has `μ` as an incoming
label in `lts`. -/
@[simp]
theorem reverse_hasOutLabel {lts : LTS State Label} :
    lts.reverse.HasOutLabel s μ ↔ ∃ s', lts.Tr s' μ s := Iff.rfl

/-- `lts.reverse` is bounded up to `n` iff `lts` is. -/
@[simp]
theorem reverse_boundedUpTo {lts : LTS State Label} {n : ℕ} :
    lts.reverse.BoundedUpTo n ↔ lts.BoundedUpTo n := by
  constructor <;> intro h s₁ μs s₂ hmtr <;> simpa using h s₂ μs.reverse s₁ (by simpa using hmtr)

end Reverse

end Cslib.LTS
