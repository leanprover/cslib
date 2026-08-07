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

Implementation of Kildall's worklist algorithm for solving dataflow equations, as described in
@Kildall73. Correctness follows an argument similar to the one found in @Nielson99, with a proof
technique borrowed from @LaSpina25.

## Main definitions

- `DFState` represents the result of a dataflow analysis algorithm, a mapping between CFG nodes and
  abstract states.
- Definitions of correctness (soundness + completeness) for the analysis result, as `Fixpoint`s over
  the analysis result `ρ`.
-

## Main theorems

- Termination of the worklist algorithm
- Correctness of the algorithm : computation of a postfixpoint.
- Correctness of the algorithm : computation of a fixpoint in the monotone transfer case.

## References

* [G. Kildall, *A Unified Approach to Global Program Optimization*][Kildall73]
* [F. Nielson, H.R. Nielson, C. Hankin, *Principles of Program Analysis*][Nielson99]
* [R. LaSpina, *Formal Verification of WTO-based Dataflow Solvers*][LaSpina25]
-/

variable {Node Edge : Type} [DecidableEq Node] [DecidableEq Edge]

/-- The state of a dataflow analysis on graph `g` is a mapping from nodes `n`
    of `g` to elements of the abstract domain `L`. -/
abbrev DFState (g : CFG Node Edge) (L : Type) : Type := NodeOf g -> L

namespace DFState

variable {L : Type} [SemilatticeSup L]

/-- The empty dataflow result, a function mapping every node to `⊥`. -/
def empty {g : CFG Node Edge} [OrderBot L] : DFState g L := fun _ => ⊥

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

variable {L : Type} [SemilatticeSup L] [DecidableEq L] [OrderBot L]

/-- if there's no ascending chains in `L`, there are no ascending chains in `DFState g L` either -/
instance {g : CFG Node Edge} [WellFoundedGT L] : WellFoundedGT (DFState g L) :=
  -- since Mathlib only defines LT wellfoundedness for functions, we need to do some flips
  inferInstanceAs (WellFoundedLT (NodeOf g → Lᵒᵈ))

/-- Instance of wellfoundedness for the ordering on states. -/
local instance {g : CFG Node Edge} [WellFoundedGT L] : WellFoundedRelation (DFState g L) :=
  ⟨(· > ·), IsWellFounded.wf⟩

-- abstract shape of transfer function
abbrev Transfer (α L : Type) := α -> L -> L

def joinPred (g : CFG Node Edge) (eT : Transfer Edge L) (init : L) (ρ : DFState g L)
    (n : NodeOf g) : L :=
  (g.inEdges n).foldl (fun acc (e : EdgeOf g) =>
    acc ⊔ eT e (ρ (g.srcOf e))
  ) (if n.val = g.entry then init else ⊥)

/-- Kildall's worklist algorithm, propagating updates to the worklist based on new information.
    The termination proof uses wellfoundedness of · < · on `L`, i.e. the fact that the lattice
    is of finite height. -/
def kildall [WellFoundedGT L]
    (g : CFG Node Edge) (nT : Transfer Node L) (eT : Transfer Edge L)
    (init : L) (ρ : DFState g L := DFState.empty)
    (wl : List (NodeOf g) := g.nodesOf) : DFState g L :=
  match wl with
  | [] => ρ
  | n :: rest =>
      let newIn := joinPred g eT init ρ n
      let newOut := (ρ n) ⊔ (nT n newIn)
      if _h : newOut = (ρ n) then
        kildall g nT eT init ρ rest
      else
        let ρ' := DFState.update ρ n newOut
        let wl' := rest ++ g.succOf n
        kildall g nT eT init ρ' wl'
termination_by (ρ, wl.length)
decreasing_by
  · exact Prod.Lex.right ρ (by simp)
  · refine Prod.Lex.left _ _ ?_
    apply DFState.lt_update
    apply le_sup_left.lt_of_ne; grind

end Kildall

section Properties

variable {L : Type} [SemilatticeSup L] [WellFoundedGT L] [OrderBot L]

omit [WellFoundedGT L] in
/-- Updating the abstract state at node `m` doesn't impact the incoming state at node `n` if `m` is
    not a predecessor of `n`. -/
lemma joinPred_neq_of_nonpred (g : CFG Node Edge) (eT : Transfer Edge L) (init : L)
    (ρ : DFState g L) (n m : NodeOf g) (v : L) (hm : n ∉ g.succOf m) :
    joinPred g eT init (ρ.update m v) n = joinPred g eT init ρ n := by
  simp only [joinPred]
  apply List.foldl_ext
  intro acc e he
  simp only [DFState.update]
  split
  case isFalse hneq => rfl
  case isTrue heq =>
    exfalso
    apply hm
    simp only [CFG.succOf, CFG.nodesOf, List.mem_filter, List.mem_attach, List.any_eq_true,
      decide_eq_true_eq, Subtype.exists, true_and]
    use e, e.property

omit [WellFoundedGT L] in
/-- Incoming states are monotone when every edge transfer is monotone. -/
lemma monotone_joinPred (g : CFG Node Edge) (eT : Transfer Edge L) (init : L)
    (heT : ∀ e, Monotone (eT e)) : Monotone (joinPred g eT init) := by
  intro ρ₁ ρ₂ hle
  apply Pi.le_def.2
  intro n
  simp only [joinPred]
  suffices ∀ init₁ init₂, init₁ <= init₂ →
    List.foldl _ init₁ (g.inEdges n) ≤ List.foldl _ init₂ (g.inEdges n) by
    apply Std.IsPreorder.le_refl _ |> this _ _
  induction g.inEdges n with
  | nil => simp
  | cons e t ih =>
    intros i₁ i₂ hlei
    simp only [List.foldl_cons]
    refine sup_le_sup hlei ?_ |> ih _ _
    exact heT e (hle _)

/- To prove properties on this algorithm, we adapt a technique from @LaSpina25 to exploit the
inductive structure of the algorithm's execution. -/

/-- The result of the worklist algorithm satisfies any invariant preserved through the
    algorithm's run. -/
lemma kildall_invariant [DecidableEq L]
    (g : CFG Node Edge) (nT : Transfer Node L) (eT : Transfer Edge L)
    (init : L) (ρ : DFState g L) (wl : List (NodeOf g))
    (P : DFState g L → List (NodeOf g) → Prop)
    (hinit : P ρ wl)
    (hstep_same : ∀ {ρ n rest}, P ρ (n :: rest) →
      let newOut := ρ n ⊔ nT n (joinPred g eT init ρ n)
      newOut = ρ n →
        P ρ rest)
    (hstep_changed : ∀ {ρ n rest}, P ρ (n :: rest) →
      let newOut := ρ n ⊔ nT n (joinPred g eT init ρ n)
      newOut ≠ ρ n →
        P (ρ.update n newOut) (rest ++ g.succOf n)) :
      P (kildall g nT eT init ρ wl) [] := by
  induction ρ, wl using kildall.induct g nT eT init with
  | case1 o => simpa [kildall]
  | case2 acc n rest nin nout heq ih =>
      simp only [kildall, dite_eq_ite]
      rw [if_pos heq]
      exact ih (hstep_same hinit heq)
  | case3 acc n r nin nout hnout acc' wl' ih =>
      simp only [kildall, dite_eq_ite]
      rw [if_neg hnout]
      exact ih (hstep_changed hinit hnout)

/-- An analysis result `ρ` on `g` is a postfixpoint if, at every node of `g`, computing the
    transfers of the incoming facts remains within the outgoing facts. -/
def ForwardPostFixpoint
    (g : CFG Node Edge) (nT : Transfer Node L) (eT : Transfer Edge L) (init : L)
    (ρ : DFState g L) (wl : List (NodeOf g)) : Prop :=
  ∀ n ∉ wl, nT n (joinPred g eT init ρ n) ≤ ρ n

/-- An analysis result `ρ` on `g` is a fixpoint if, at every node of `g`, the `ForwardPostFixpoint`
    bound is tight. -/
def ForwardFixpoint
    (g : CFG Node Edge) (nT : Transfer Node L) (eT : Transfer Edge L) (init : L)
    (ρ : DFState g L) (wl : List (NodeOf g)) : Prop :=
  ∀ n ∉ wl, nT n (joinPred g eT init ρ n) = ρ n

/-- The result of the worklist algorithm is a `ForwardPostfixpoint`. -/
theorem kildall_forwardPostFixpoint [DecidableEq L] (g : CFG Node Edge)
    (nT : Transfer Node L) (eT : Transfer Edge L) (init : L) (ρ : DFState g L)
    (wl : List (NodeOf g))
    (hinv0 : ∀ m : NodeOf g, m ∉ wl → nT m (joinPred g eT init ρ m) ≤ ρ m) :
    let res := kildall g nT eT init ρ wl
    ForwardPostFixpoint g nT eT init res [] := by
  refine kildall_invariant g nT eT init ρ wl (ForwardPostFixpoint g nT eT init) ?_ ?_ ?_
  · exact hinv0
  · intro ρ n rest hfp newOut heq m hm
    by_cases hmn : m = n
    · subst m
      exact le_sup_right.trans_eq heq
    · exact hfp m (by simp_all)
  · intro ρ n rest hfp newOut hnout m hm
    have hsucc : m ∉ g.succOf n := fun hin => (List.mem_append_right _ hin) |> hm
    rw [joinPred_neq_of_nonpred g eT init ρ m n newOut hsucc, DFState.update]
    split -- m ?= n
    case isTrue heq =>
      grind [le_sup_right]
    case isFalse hneq =>
      apply hfp; grind

/-- An analysis result `ρ` on `g` is a prefixpoint if every outgoing fact remains within the
    result of transferring its incoming facts. -/
def ForwardPreFixpoint (g : CFG Node Edge) (nT : Transfer Node L) (eT : Transfer Edge L) (init : L)
    (ρ : DFState g L) : Prop :=
  ∀ n, ρ n ≤ nT n (joinPred g eT init ρ n)

/-- The worklist algorithm preserves forward pre-fixpoints when all transfers are monotone. -/
lemma kildall_forwardPreFixpoint [DecidableEq L] (g : CFG Node Edge)
    (nT : Transfer Node L) (hnT : ∀ n, Monotone (nT n))
    (eT : Transfer Edge L) (heT : ∀ e, Monotone (eT e))
    (init : L) (ρ : DFState g L) (wl : List (NodeOf g))
    (hinv0 : ForwardPreFixpoint g nT eT init ρ) :
    let res := kildall g nT eT init ρ wl
    ForwardPreFixpoint g nT eT init res := by
  refine kildall_invariant g nT eT init ρ wl
    (fun ρ _ => ForwardPreFixpoint g nT eT init ρ) hinv0 ?_ ?_
  · exact fun hfp _ => hfp
  · intro ρ n rest hfp newOut hnout m
    have hle : ρ ≤ ρ.update n newOut := by
      intro k
      simp only [DFState.update]
      split <;> grind [le_refl, le_sup_left]
    have htransfer : nT m (joinPred g eT init ρ m) ≤
        nT m (joinPred g eT init (ρ.update n newOut) m) :=
      hnT m (monotone_joinPred g eT init heT hle m)
    grind [DFState.update, sup_le, hfp m]

/-- If the transfer functions are monotone, the result of the worklist algorithm is a
    `ForwardFixpoint`. -/
theorem kildall_forwardFixpoint [DecidableEq L] (g : CFG Node Edge)
    (nT : Transfer Node L) (hnT : ∀ n, Monotone (nT n))
    (eT : Transfer Edge L) (heT : ∀ e, Monotone (eT e))
    (init : L) (ρ : DFState g L) (wl : List (NodeOf g))
    (hpost0 : ∀ m ∉ wl, nT m (joinPred g eT init ρ m) ≤ ρ m)
    (hpre0 : ForwardPreFixpoint g nT eT init ρ) :
    let res := kildall g nT eT init ρ wl
    ForwardFixpoint g nT eT init res [] := by
  intro res
  have hpost : ForwardPostFixpoint g nT eT init res [] :=
    kildall_forwardPostFixpoint g nT eT init ρ wl hpost0
  have hpre : ForwardPreFixpoint g nT eT init res :=
    kildall_forwardPreFixpoint g nT hnT eT heT init ρ wl hpre0
  intro n hn
  exact le_antisymm (hpost n hn) (hpre n)

/-- Final theorem: the result of a full run of the algorithm with the default arguments is the least
    fixpoint of the equations induced by the transfer functions and the initial state. -/
theorem kildall_correct [DecidableEq L] (g : CFG Node Edge)
    (nT : Transfer Node L) (hnT : ∀ n, Monotone (nT n))
    (eT : Transfer Edge L) (heT : ∀ e, Monotone (eT e))
    (init : L) :
    let res := kildall g nT eT init
    ForwardFixpoint g nT eT init res [] := by
  apply kildall_forwardFixpoint g nT hnT eT heT init DFState.empty g.nodesOf
  case hpost0 => -- ≤
    -- `∀ m ∉ g.nodesOf, ...`
    -- since every `m` is in `g.nodesOf` this is vacuously true
    grind [CFG.nodesOf]
  case hpre0 => -- ≥
    -- `∀ m ∈ g.nodesOf, DFState.empty m ≤ ...`
    -- since `DFState.empty` is `λ _. ⊥`, it's ≤ anything, thanks to `OrderBot`.
    simp [ForwardPreFixpoint, DFState.empty]

end Properties
