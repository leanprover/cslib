/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Foundations.Semantics.LTS.Termination
public import Mathlib.Order.WellFounded

/-!
# Examples separating boundedness, termination, and acyclicity

On infinite state spaces, boundedness, termination, and acyclicity are distinct properties.
This file gives concrete LTSs witnessing that the converses in
`Bounded → Terminating → Acyclic` do not hold in general.
-/

@[expose] public section

namespace Cslib.LTS.Example

/-- The countdown LTS takes a natural number to its predecessor. -/
def countdownLTS : LTS ℕ Unit where
  Tr n _ m := n = m + 1

instance countdownLTS_terminating : countdownLTS.Terminating where
  terminating := by
    apply Subrelation.wf _ Nat.lt_wfRel.wf
    rintro s2 s1 ⟨_, rfl⟩
    exact Nat.lt_succ_self s2

example : countdownLTS.Acyclic := inferInstance
example : Relation.Acyclic countdownLTS.UnlabelledTr := inferInstance

private theorem countdownLTS_mTr (n : ℕ) :
    countdownLTS.MTr n (List.replicate n ()) 0 := by
  induction n with
  | zero => exact .refl
  | succ n ih =>
      simpa [List.replicate_succ] using MTr.stepL (by simp [countdownLTS]) ih

/-- The countdown LTS is not bounded. -/
theorem countdownLTS_not_bounded : ¬ countdownLTS.Bounded := by
  rintro ⟨bound, hbound⟩
  simpa using hbound bound (List.replicate bound ()) 0 (countdownLTS_mTr bound)

/-- The successor LTS takes each natural number to its successor. -/
def successorLTS : LTS ℕ Unit where
  Tr n _ m := m = n + 1

private theorem successorLTS_transGen_lt {n m : ℕ}
    (h : Relation.TransGen successorLTS.UnlabelledTr n m) : n < m := by
  apply Relation.transGen_minimal (r' := (· < ·)) at h
  · exact h
  · rintro n m ⟨μ, htr⟩
    simp only [successorLTS] at htr
    omega

instance successorLTS_acyclic : successorLTS.Acyclic where
  acyclic := ⟨fun n h => (Nat.lt_irrefl n) (successorLTS_transGen_lt h)⟩

/-- The successor LTS is not terminating. -/
theorem successorLTS_not_terminating : ¬ successorLTS.Terminating := by
  intro h
  exact (Relation.Terminating.iff_isEmpty_chain.mp h.terminating).false
    ⟨fun n => n, fun n => ⟨(), by simp [successorLTS]⟩⟩

/-- The self-loop LTS has a transition from its unique state to itself. -/
def selfLoopLTS : LTS Unit Unit where
  Tr _ _ _ := True

/-- The self-loop LTS is not acyclic. -/
theorem selfLoopLTS_not_acyclic : ¬ selfLoopLTS.Acyclic :=
  fun h => h.acyclic.irrefl () (.single ⟨(), trivial⟩)

end Cslib.LTS.Example
