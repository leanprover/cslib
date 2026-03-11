/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Cslib.AlgorithmsTheory.QueryModel
public import Cslib.Computability.Machines.SingleTapeTuring.Basic

@[expose] public section

/-!
# Query Type for Comparison Search in Lists

In this file we define a query type `ListSearch` for comparison based searching in Lists,
whose sole query `compare` compares the head of the list with a given argument. It
further defines a model `ListSearch.natCost` for this query.

--
## Definitions



-/

namespace Cslib

namespace Algorithms

open Prog Turing

variable [Inhabited Symbol] [Fintype Symbol] [DecidableEq Symbol]

inductive Dir where
  | Left
  | Right
  | Stop

inductive TMQuery (tm : SingleTapeTM Symbol) : Type → Type where
  | readTape (inpCfg : tm.Cfg) : TMQuery tm (Option Symbol)
  | readState (inpCfg : tm.Cfg) : TMQuery tm (Option tm.State)
  | write (inpCfg : tm.Cfg) (s : Option Symbol) : TMQuery tm tm.Cfg
  | update (inpCfg : tm.Cfg) (st : tm.State): TMQuery tm tm.Cfg
  | move (inpCfg : tm.Cfg) (dir : Dir) : TMQuery tm tm.Cfg

@[ext, grind]
structure TMCost where
  /-- `steps` counts the number of moves in the TM -/
  steps : ℕ
  /-- `writeCells` is a set of cells that were previously unwritten -/
  writeCells : ℕ


/-- Equivalence between SortOpsCost and a product type. -/
def TMCost.equivProd : TMCost ≃ (ℕ × ℕ) where
  toFun sortOps := (sortOps.steps, sortOps.writeCells)
  invFun pair := ⟨pair.1, pair.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

namespace TMCost

@[simps, grind]
instance : Zero TMCost := ⟨0, 0⟩

@[simps]
instance : LE TMCost where
  le soc₁ soc₂ := soc₁.steps ≤ soc₂.steps ∧ soc₁.writeCells ≤ soc₂.writeCells

instance : LT TMCost where
  lt soc₁ soc₂ := soc₁ ≤ soc₂ ∧ ¬soc₂ ≤ soc₁

@[grind]
instance : PartialOrder TMCost :=
  fast_instance% TMCost.equivProd.injective.partialOrder _ .rfl .rfl

@[simps]
instance : Add TMCost where
  add soc₁ soc₂ := ⟨soc₁.steps + soc₂.steps, soc₁.writeCells + soc₂.writeCells⟩

@[simps]
instance : SMul ℕ TMCost where
  smul n soc := ⟨n • soc.steps, n • soc.writeCells⟩

instance : AddCommMonoid TMCost :=
  fast_instance%
    TMCost.equivProd.injective.addCommMonoid _ rfl (fun _ _ => rfl) (fun _ _ => rfl)

end TMCost

/--
A model of `TMQuery` that uses `TMCost` as the cost type for operations.
Space complexity in this single tape TM is counted as the number of unread cells
written to during the TM's operation.
-/
@[simps, grind]
def sortModel (tm : SingleTapeTM Symbol) :
    Model (TMQuery tm) TMCost where
  evalQuery
    | .readTape cfg => cfg.BiTape.head
    | .readState cfg => cfg.state
    | .write cfg s => {BiTape := cfg.BiTape.write s, state := cfg.state}
    | .move cfg dir =>
        match dir with
        | .Left => {BiTape := cfg.BiTape.move_left, state := cfg.state}
        | .Right => {BiTape := cfg.BiTape.move_left, state := cfg.state}
        | .Stop => cfg
    | .update cfg st => {BiTape := cfg.BiTape, state := st}
  cost
    | .readTape _ => ⟨0, 0⟩
    | .readState _ => ⟨0, 0⟩
    | .write cfg _ =>
        match cfg.BiTape.head with
        | .some _ => ⟨0, 0⟩
        | .none => ⟨0, 1⟩
    | .move _ _ => ⟨1, 0⟩
    | .update _ _ => ⟨0, 0⟩

end Algorithms

end Cslib
