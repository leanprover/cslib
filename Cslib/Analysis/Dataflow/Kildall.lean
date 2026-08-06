/-
Copyright (c) 2026 Jacopo Moretti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacopo Moretti
-/

import Cslib.Analysis.Dataflow.CFG
import Mathlib.Order.Lattice
import Mathlib.Data.DFinsupp.WellFounded

/-!
# Forward Worklist dataflow algorithm

Implementation of Kildall's worklist algorithm for solving dataflow equations,
as described in @Kildall73.

## Main definitions

- `DFState` represents the result of a dataflow analysis algorithm, a mapping
  between CFG nodes and abstract states

## Main theorems

- Termination of the worklist algorithm

## References

* [G. Kildall, *A Unified Approach to Global Program Optimization*][Kildall73]
* [R. LaSpina, *Formal Verification of WTO-based Dataflow Solvers*][LaSpina25]
-/

variable {Node Edge : Type} [DecidableEq Node] [DecidableEq Edge]

/-- The state of a dataflow analysis on graph `g` is a mapping from nodes `n`
    of `g` to elements of the abstract domain `L`. -/
abbrev DFState (g : CFG Node Edge) (L : Type) : Type := NodeOf g -> L

namespace DFState

variable {L : Type} [SemilatticeSup L]

/-- The empty dataflow result, a function mapping every node to `⊥`. -/
def empty {g : CFG Node Edge} [Bot L] : DFState g L := fun _ => ⊥

/-- Update `ρ`'s value at node `n`, to new value `v`. -/
def update {g : CFG Node Edge} (ρ : DFState g L) (n : NodeOf g) (v : L) : DFState g L :=
  fun m => if m = n then v else ρ m

/-- Updating `ρ` at `n` with a value smaller than `ρ n` yields a smaller `ρ` -/
theorem lt_update {g : CFG Node Edge} (ρ : DFState g L) (n : NodeOf g) (v : L) (hlt : ρ n < v) :
    ρ < ρ.update n v := by
  rw [Pi.lt_def]
  refine ⟨fun m => ?_, n, ?_⟩ <;> grind [DFState.update]

end DFState

section Kildall

variable {L : Type} [SemilatticeSup L] [DecidableEq L] [Bot L]

/-- if there's no ascending chains in `L`, there are no ascending chains in `DFState g L` either -/
instance {g : CFG Node Edge} [WellFoundedGT L] : WellFoundedGT (DFState g L) :=
  -- since Mathlib only defines LT wellfoundedness for functions, we need to do some flips
  inferInstanceAs (WellFoundedLT (NodeOf g → Lᵒᵈ))

/-- Instance of wellfoundedness for the ordering on states. -/
local instance {g : CFG Node Edge} [WellFoundedGT L] : WellFoundedRelation (DFState g L) :=
  ⟨(· > ·), IsWellFounded.wf⟩

-- abstract shape of transfer function
abbrev Transfer (α L : Type) := α -> L -> L

def joinPred (g : CFG Node Edge) (eT : Transfer Edge L) (s : DFState g L) (n : NodeOf g) : L :=
  (g.inEdges n).foldl (fun acc e =>
    let src : NodeOf g := g.srcOf e
    acc ⊔ eT e (s src)
  ) ⊥

/-- Kildall's worklist algorithm, propagating updates to the worklist based on new information.
    The termination proof uses wellfoundedness of · < · on `L`, i.e. the fact that the lattice
    is of finite height. -/
def kildall [WellFoundedGT L]
    (g : CFG Node Edge) (nT : Transfer Node L) (eT : Transfer Edge L)
    (init : L) (acc : DFState g L := DFState.empty)
    (wl : List (NodeOf g) := g.nodesOf) : DFState g L :=
  match wl with
  | [] => acc
  | n :: rest =>
      let newIn := joinPred g eT acc n
      let newOut := (acc n) ⊔ (nT n newIn)
      if _h : newOut = (acc n) then
        kildall g nT eT init acc rest
      else
        let acc' := DFState.update acc n newOut
        let wl' := rest ++ g.succOf n
        kildall g nT eT init acc' wl'
termination_by (acc, wl.length)
decreasing_by
  · exact Prod.Lex.right acc (by simp)
  · refine Prod.Lex.left _ _ ?_
    apply DFState.lt_update
    apply le_sup_left.lt_of_ne; grind

end Kildall
