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

/-- A type `α` has a computable `fresh` function if it is always possible, for any finite set
of `α`, to compute a fresh element not in the set. -/
class HasFresh (α : Type u) where
  /-- Given a finite set, returns an element not in the set. -/
  fresh : Finset α → α
  /-- Proof that `fresh` returns a fresh element for its input set. -/
  fresh_notMem (s : Finset α) : fresh s ∉ s

attribute [simp] HasFresh.fresh_notMem

/-- An existential version of the `HasFresh` typeclass. This is useful for the sake of brevity
in proofs. -/
theorem HasFresh.fresh_exists {α : Type u} [HasFresh α] (s : Finset α) : ∃ a, a ∉ s :=
  ⟨fresh s, fresh_notMem s⟩

export HasFresh (fresh fresh_notMem fresh_exists)

lemma HasFresh.not_of_finite (α : Type u) [Fintype α] : IsEmpty (HasFresh α) :=
  ⟨fun f ↦ (f.fresh_notMem .univ).elim (Finset.mem_univ _)⟩

/-- All infinite types have an associated (at least noncomputable) fresh function.
This, in conjunction with `HasFresh.not_of_finite`, characterizes `HasFresh`. -/
noncomputable def HasFresh.of_infinite (α : Type u) [Infinite α] : HasFresh α where
  fresh s := s.finite_toSet.infinite_compl.nonempty.choose
  fresh_notMem s := s.finite_toSet.infinite_compl.nonempty.choose_spec

open Finset in
/-- Construct a fresh element from an embedding of `ℕ` using `Nat.find`. -/
def HasFresh.ofNatEmbed {α : Type u} [DecidableEq α] (e : ℕ ↪ α) : HasFresh α where
  fresh s := e (Nat.find (p := fun n ↦ e n ∉ s) ⟨(s.preimage e e.2.injOn).max.succ,
    fun h ↦ not_lt_of_ge (le_max <| mem_preimage.2 h) (WithBot.lt_succ _)⟩)
  fresh_notMem s := Nat.find_spec (p := fun n ↦ e n ∉ s) _

/-- Construct a fresh element given a function `f` with `x < f x`. -/
def HasFresh.ofSucc {α : Type u} [Inhabited α] [SemilatticeSup α] (f : α → α) (hf : ∀ x, x < f x) :
    HasFresh α where
  fresh s := if hs : s.Nonempty then f (s.sup' hs id) else default
  fresh_notMem s h := if hs : s.Nonempty
    then not_le_of_gt (hf (s.sup' hs id)) <| by rw [dif_pos hs] at h; exact s.le_sup' id h
    else hs ⟨_, h⟩

/-- `ℕ` has a computable fresh function. -/
instance : HasFresh ℕ :=
  .ofSucc (· + 1) Nat.lt_add_one

/-- `ℤ` has a computable fresh function. -/
instance : HasFresh ℤ :=
  .ofSucc (· + 1) Int.lt_succ

/-- `ℚ` has a computable fresh function. -/
instance : HasFresh ℚ :=
  .ofSucc (· + 1) fun x ↦ lt_add_of_pos_right x one_pos

/-- If `α` has a computable fresh function, then so does `Finset α`. -/
instance {α : Type u} [DecidableEq α] [HasFresh α] : HasFresh (Finset α) :=
  .ofSucc (fun s ↦ insert (fresh s) s) fun s ↦ Finset.ssubset_insert <| fresh_notMem s

/-- If `α` is inhabited, then `Multiset α` has a computable fresh function. -/
instance {α : Type u} [DecidableEq α] [Inhabited α] : HasFresh (Multiset α) :=
  .ofSucc (fun s ↦ default ::ₘ s) fun _ ↦ Multiset.lt_cons_self _ _

/-- `ℕ → ℕ` has a computable fresh function. -/
instance : HasFresh (ℕ → ℕ) :=
  .ofSucc (fun f x ↦ f x + 1) fun _ ↦ Pi.lt_def.2 ⟨fun _ ↦ Nat.le_succ _, 0, Nat.lt_succ_self _⟩
