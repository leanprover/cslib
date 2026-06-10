/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Syntax.SubformulaClosure

/-!
# F/P-Nesting Depth Computation and Maximum Depth Within Closure Sets

F/P-nesting depth, max nesting depth in closure, and F/P inner formula extraction.

Ported from BimodalLogic/Theories/Bimodal/Syntax/SubformulaClosure/NestingDepth.lean
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

@[expose] public section

namespace Cslib.Logic.Bimodal

open Formula

variable {Atom : Type*} [DecidableEq Atom]

def f_nesting_depth : Formula Atom → Nat
  | .untl inner (.imp .bot .bot) => 1 + f_nesting_depth inner
  | _ => 0

theorem f_nesting_depth_nonneg (phi : Formula Atom) : f_nesting_depth phi ≥ 0 := Nat.zero_le _

theorem someFuture_unfold (psi : Formula Atom) :
    Formula.someFuture psi = Formula.untl psi Formula.top := by
  rfl

theorem f_nesting_depth_someFuture (psi : Formula Atom) :
    f_nesting_depth (Formula.someFuture psi) = 1 + f_nesting_depth psi := by
  simp only [Formula.someFuture, Formula.top, f_nesting_depth]

@[simp]
theorem f_nesting_depth_atom (a : Atom) : f_nesting_depth (.atom a : Formula Atom) = 0 := rfl

@[simp]
theorem f_nesting_depth_bot : f_nesting_depth (.bot : Formula Atom) = 0 := rfl

@[simp]
theorem f_nesting_depth_box (psi : Formula Atom) : f_nesting_depth (.box psi) = 0 := rfl

@[simp]
theorem f_nesting_depth_allPast (psi : Formula Atom) : f_nesting_depth (Formula.allPast psi) = 0 := by
  simp only [Formula.allPast, Formula.somePast, Formula.neg, Formula.top, f_nesting_depth]

@[simp]
theorem f_nesting_depth_allFuture (psi : Formula Atom) : f_nesting_depth (Formula.allFuture psi) = 0 := by
  simp only [Formula.allFuture, Formula.someFuture, Formula.neg, Formula.top, f_nesting_depth]

def max_F_depth_in_closure (phi : Formula Atom) : Nat :=
  (closureWithNeg phi).sup f_nesting_depth

theorem f_depth_le_max {phi psi : Formula Atom} (h : psi ∈ closureWithNeg phi) :
    f_nesting_depth psi ≤ max_F_depth_in_closure phi := by
  exact Finset.le_sup h

def p_nesting_depth : Formula Atom → Nat
  | .snce inner (.imp .bot .bot) => 1 + p_nesting_depth inner
  | _ => 0

theorem p_nesting_depth_nonneg (phi : Formula Atom) : p_nesting_depth phi ≥ 0 := Nat.zero_le _

theorem somePast_unfold (psi : Formula Atom) :
    Formula.somePast psi = Formula.snce psi Formula.top := by
  rfl

theorem p_nesting_depth_somePast (psi : Formula Atom) :
    p_nesting_depth (Formula.somePast psi) = 1 + p_nesting_depth psi := by
  simp only [Formula.somePast, Formula.top, p_nesting_depth]

@[simp]
theorem p_nesting_depth_atom (a : Atom) : p_nesting_depth (.atom a : Formula Atom) = 0 := rfl

@[simp]
theorem p_nesting_depth_bot : p_nesting_depth (.bot : Formula Atom) = 0 := rfl

@[simp]
theorem p_nesting_depth_box (psi : Formula Atom) : p_nesting_depth (.box psi) = 0 := rfl

@[simp]
theorem p_nesting_depth_allFuture (psi : Formula Atom) : p_nesting_depth (Formula.allFuture psi) = 0 := by
  simp only [Formula.allFuture, Formula.someFuture, Formula.neg, Formula.top, p_nesting_depth]

@[simp]
theorem p_nesting_depth_allPast (psi : Formula Atom) : p_nesting_depth (Formula.allPast psi) = 0 := by
  simp only [Formula.allPast, Formula.somePast, Formula.neg, Formula.top, p_nesting_depth]

def max_P_depth_in_closure (phi : Formula Atom) : Nat :=
  (closureWithNeg phi).sup p_nesting_depth

theorem p_depth_le_max {phi psi : Formula Atom} (h : psi ∈ closureWithNeg phi) :
    p_nesting_depth psi ≤ max_P_depth_in_closure phi := by
  exact Finset.le_sup h

def extractFutureInner : Formula Atom → Option (Formula Atom)
  | .untl inner (.imp .bot .bot) => some inner
  | _ => none

def extractPastInner : Formula Atom → Option (Formula Atom)
  | .snce inner (.imp .bot .bot) => some inner
  | _ => none

theorem extractFutureInner_someFuture (chi : Formula Atom) :
    extractFutureInner (Formula.someFuture chi) = some chi := by
  simp only [Formula.someFuture, Formula.top, extractFutureInner]

theorem extractPastInner_somePast (chi : Formula Atom) :
    extractPastInner (Formula.somePast chi) = some chi := by
  simp only [Formula.somePast, Formula.top, extractPastInner]

def IsFutureFormula (f : Formula Atom) : Prop := (extractFutureInner f).isSome = true

instance : DecidablePred (IsFutureFormula (Atom := Atom)) :=
  fun f => decidable_of_iff ((extractFutureInner f).isSome = true)
    (by simp only [IsFutureFormula])

def IsPastFormula (f : Formula Atom) : Prop := (extractPastInner f).isSome = true

instance : DecidablePred (IsPastFormula (Atom := Atom)) :=
  fun f => decidable_of_iff ((extractPastInner f).isSome = true)
    (by simp only [IsPastFormula])

end Cslib.Logic.Bimodal
