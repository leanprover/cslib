/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Basic

import Mathlib.Tactic.DeriveFintype

-- TODO create a "common file"
import Cslib.Computability.Machines.SingleTapeTuring.Basic

namespace Turing

variable [Inhabited α] [Fintype α]

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

public def listToTape (ls : List (List α)) : BiTape (WithSep α) :=
  BiTape.mk₁ (listToString ls)

public def MultiTapeTM.TransformsLists
    (tm : MultiTapeTM k (WithSep α))
    (tapes tapes' : Fin k → List (List α)) : Prop :=
  tm.TransformsTapes (listToTape ∘ tapes) (listToTape ∘ tapes')

public noncomputable def MultiTapeTM.eval_list
    (tm : MultiTapeTM k (WithSep α))
    (tapes : Fin k → List (List α)) :
    Part (Fin k → List (List α)) :=
  ⟨∃ tapes', tm.TransformsLists tapes tapes', fun h => h.choose⟩


end Turing
