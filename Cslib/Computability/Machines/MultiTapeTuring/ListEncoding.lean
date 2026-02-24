/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Basic
public import Cslib.Computability.Machines.MultiTapeTuring.HeadStats
public import Cslib.Computability.Machines.MultiTapeTuring.WithTapes

import Mathlib.Tactic.DeriveFintype

namespace Turing

/--
An alphabet that contains exactly two symbols, 1 and 2.
TODO use an embedding or something else that is more flexible
-/
public inductive OneTwo where
  | one
  | two
deriving DecidableEq, Inhabited, Fintype


/-- An alphabet for list encoding -/
public inductive WithSep (α : Type) where
  | blank
  | ofChar (c : α)
  | comma
  -- TODO need to decide if we want to encode lists with parentheses or not.
  -- Is annoying when pushing and popping from lists, but can be useful to avoid
  -- running "off the tape"
  -- | lParen
  -- | rParen
deriving Fintype, DecidableEq, Inhabited

/-- A list of words is transformed by appending a comma after each word and concatenating.
Note that the comma is not only a separator but also appears as the final character
of the resulting string (if the list is non-empty). -/
public def listToString (ls : List (List α)) : List (WithSep α) :=
  (ls.map (fun w : List α => (w.map .ofChar) ++ [.comma])).flatten

/-- Encodes a list of words into a tape. -/
public def listToTape (ls : List (List α)) : BiTape (WithSep α) :=
  BiTape.mk₁ (listToString ls)

/-- The Turing machine `tm` transforms the list-encoded tapes `tapes` into the list-encoded
tapes `tapes'`. -/
public def MultiTapeTM.TransformsLists
    (tm : MultiTapeTM k (WithSep α))
    (tapes tapes' : Fin k → List (List α)) : Prop :=
  tm.TransformsTapes (listToTape ∘ tapes) (listToTape ∘ tapes')

/-- The Turing machine `tm` halts starting with list-encoded tapes `tapes`. -/
public def MultiTapeTM.HaltsOnLists
    (tm : MultiTapeTM k (WithSep α))
    (tapes : Fin k → List (List α)) : Prop :=
  ∃ tapes', tm.TransformsLists tapes tapes'

/-- Execute the Turing machine `tm` on the list-encoded tapes `tapes`. -/
public noncomputable def MultiTapeTM.eval_list
    (tm : MultiTapeTM k (WithSep α))
    (tapes : Fin k → List (List α)) :
    Part (Fin k → List (List α)) :=
  ⟨tm.HaltsOnLists tapes, fun h => h.choose⟩

public theorem MultiTapeTM.HaltsOnLists_of_eval_list
    {tm : MultiTapeTM k (WithSep α)}
    {tapes : Fin k → List (List α)}
    (h_dom : (tm.eval_list tapes).Dom) :
    tm.HaltsOnLists tapes := by
  simpa using h_dom

/-- Execute the Turing machine `tm` knowing that it always halts, thus yielding a total function
on the tapes. -/
public noncomputable def MultiTapeTM.eval_list_tot
  (tm : MultiTapeTM k (WithSep α))
  (h_alwaysHalts : ∀ tapes, tm.HaltsOnLists tapes)
  (tapes : Fin k → List (List α)) :
  Fin k → List (List α) :=
  (tm.eval_list tapes).get (h_alwaysHalts tapes)

@[simp, grind =]
public theorem MultiTapeTM.extend_eval_list
    {α : Type} [Fintype α]
    {k₁ k₂ : ℕ} {h_le : k₁ ≤ k₂}
    {tm : MultiTapeTM k₁ (WithSep α)}
    {tapes : Fin k₂ → List (List α)} :
  (tm.extend h_le).eval_list tapes =
    (tm.eval_list (tapes ⟨·, by omega⟩)).map (fun tapes' =>
      fun i : Fin k₂ => if h : i.val < k₁ then tapes' ⟨i, h⟩ else tapes i) := by
  sorry

@[simp, grind =]
public theorem MultiTapeTM.permute_tapes_eval_list
  {α : Type} [Fintype α] [Inhabited α]
  (tm : MultiTapeTM k (WithSep α)) (σ : Equiv.Perm (Fin k)) (tapes : Fin k → List (List α)) :
  (tm.permute_tapes σ).eval_list tapes =
    (tm.eval_list (tapes ∘ σ)).map (fun tapes' => tapes' ∘ σ.symm) := by
  sorry

@[simp, grind =]
public theorem MultiTapeTM.with_tapes_eval_list
  {α : Type} [Fintype α] [Inhabited α]
  {k₁ k₂ : ℕ}
  {tm : MultiTapeTM k₁ (WithSep α)} {f : Fin k₁ → Fin k₂} {h_inj : f.Injective}
  {tapes : Fin k₂ → List (List α)} :
  (tm.with_tapes f h_inj).eval_list tapes =
    (tm.eval_list (tapes ∘ f)).map
      (fun tapes' => fun t => apply_updates tapes tapes' f t) := by
   sorry

def MultiTapeTM.TransformsListsWithStats
    (tm : MultiTapeTM k (WithSep α))
    (tapes : Fin k → List (List α))
    (ts : (Fin k → List (List α)) × (Fin k → HeadStats)) : Prop :=
    tm.evalWithStats (listToTape ∘ tapes) = .some (listToTape ∘ ts.1, ts.2)

/--
Evaluate the Turing machine `tm` on the list-encoded tapes `tapes` and also return the head
statistics of the computation.
-/
public noncomputable def MultiTapeTM.evalWithStats_list
    (tm : MultiTapeTM k (WithSep α))
    (tapes : Fin k → List (List α)) :
    Part ((Fin k → List (List α)) × (Fin k → HeadStats)) :=
  ⟨∃ ts, tm.TransformsListsWithStats tapes ts, fun h => h.choose⟩

-- TODO for machines running on lists, we can actually have more precise head stats:
-- we know (and should enforce) that the head never moves to the right of the rightmost symbol
-- and always starts and ends on the leftmost symbol (and if the tape is empty, it never moves
-- to the right of the starting position).
-- So the minimal information we need is (per tape) the amount of symbols that were used beyond
-- the max of the ones in the initial and final configuration.
-- TODO it also makes sense to allow upper bounds on that.

/--
The Turing machine `tm` computes a total function on lists and this uniquely
determined function is `f`.
-/
public def MultiTapeTM.computes
    (tm : MultiTapeTM k (WithSep α))
    (f : (Fin k → List (List α)) → (Fin k → List (List α))) : Prop :=
  ∀ tapes, tm.eval_list tapes = .some (f tapes)

public theorem MultiTapeTM.eval_of_computes
    {tm : MultiTapeTM k (WithSep α)}
    {f : (Fin k → List (List α)) → (Fin k → List (List α))}
    (h_computes : tm.computes f)
    {tapes : Fin k → List (List α)} :
    tm.eval_list tapes = .some (f tapes) := by
  specialize h_computes tapes
  simpa [MultiTapeTM.computes] using h_computes


/-- Dyadic encoding of natural numbers. -/
public def dya (n : ℕ) : List OneTwo :=
  if n = 0 then []
  else if Even n then
    dya (n / 2 - 1) ++ [.two]
  else
    dya ((n - 1) / 2) ++ [.one]

/-- Dyadic decoding of natural numbers. -/
public def dya_inv : List OneTwo → ℕ := sorry

@[simp, grind =]
public lemma dya_inv_zero : dya_inv [] = 0 := by
  sorry

@[simp, grind =]
public lemma dya_inv_dya (n : ℕ) : dya_inv (dya n) = n := by sorry

@[simp, grind =]
public lemma dya_dya_inv (w : List OneTwo) : dya (dya_inv w) = w := by sorry

end Turing
