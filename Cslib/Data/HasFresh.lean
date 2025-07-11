/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Kenny Lau
-/

import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Ring.CharZero
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.SuccPred
import Mathlib.Order.SuccPred.WithBot

universe u

/-- A type `α` has a computable `fresh` function if it is always possible, for any finite set of `α`, to compute a fresh element not in the set. -/
class HasFresh (α : Type u) where
  /-- Given a finite set, returns an element not in the set. -/
  fresh : Finset α → α
  /-- Proof that `fresh` returns a fresh element for its input set. -/
  fresh_notMem (s : Finset α) : fresh s ∉ s

lemma WithBot.lt_succ {α : Type u} [Preorder α] [OrderBot α] [SuccOrder α] [NoMaxOrder α]
    (x : WithBot α) : x < x.succ :=
  succ_eq_succ x ▸ Order.lt_succ_of_le_of_not_isMax le_rfl (not_isMax x)

open Finset in
/-- Construct a fresh function from an embedding of ℕ. -/
def HasFresh.ofNatEmbed {α : Type u} [DecidableEq α] (e : ℕ ↪ α) : HasFresh α where
  fresh s := e (Nat.find (p := fun n ↦ e n ∉ s) ⟨(s.preimage e e.2.injOn).max.succ,
    fun h ↦ not_lt_of_ge (le_max <| (mem_preimage (hf := e.2.injOn)).2 h) (WithBot.lt_succ _)⟩)
  fresh_notMem s := Nat.find_spec (p := fun n ↦ e n ∉ s) _

/-- `ℕ` has a computable fresh function. -/
instance : HasFresh ℕ :=
  .ofNatEmbed (.refl _)

/-- `ℤ` has a computable fresh function. -/
instance : HasFresh ℤ :=
  .ofNatEmbed (Nat.castEmbedding)

/-- `ℚ` has a computable fresh function. -/
instance : HasFresh ℚ :=
  .ofNatEmbed (Nat.castEmbedding)

/-- `Finset ℕ` has a computable fresh function. -/
instance : HasFresh (Finset ℕ) :=
  .ofNatEmbed ⟨({·}), Finset.singleton_injective⟩
