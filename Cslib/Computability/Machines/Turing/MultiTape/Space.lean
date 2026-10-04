/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger, Aviv Bar Natan
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Cslib.Computability.Machines.Turing.MultiTape.Nondeterministic

/-!
# Space usage of multi-tape Turing machines

Defines the space used by a run path and space bounds for multi-tape Turing machines. Space
usage counts the positions visited by each work-tape head along the path and sums over the tapes.

## Design

The input tape is read-only with bounded head movement, and the output tape is write-only, so we
ignore both for space usage. The space usage is defined as the total number of cells the work tape
heads visited along a run path.

Instead of considering the cells _visited_ by the work tape heads, some textbooks
(including [AroraBarak09]) only consider the number of cells that contain
a non-blank symbol at some point in the execution or the number of cells written to. This allows
work tape heads to freely move at no cost as long as they do not write. It is
important to note that this causes `DSPACE(1)` to include `DSPACE(log log n)`, a class that
contains e.g. the non-regular language `{0^n 1^n | n ∈ ℕ}` (it is accepted by a TM that writes a
single marker on the work tape and then counts the number of symbols by work tape head movement
without writing).
Defining space usage via "cells visited" thus yields the more fine-grained "complexity world" in
which `DSPACE(1)` is exactly the class of regular languages.

Space bounds apply to every computation prefix, regardless of its outcome, following the
visited-cell convention in [Watrous, §2.1]
(https://cs.uwaterloo.ca/~watrous/Papers/SpaceBoundedQuantumSimulation.pdf).
`RunsInSpace` does not require termination.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Turing.MultiTapeNTM

variable {k : ℕ} {State Symbol : Type*} {input : List Symbol}
variable {ntm : MultiTapeNTM k Symbol State}

namespace RunPath

/-- The set of positions visited by the head of work tape `i` along a run path. -/
def visitedByTapeHead (p : ntm.RunPath input) (i : Fin k) : Finset ℤ :=
  Finset.univ.image fun n ↦ (p n).workTapePos i

/-- The number of cells touched by the head of work tape `i` along a run path. -/
def spaceUsedByTape (p : ntm.RunPath input) (i : Fin k) : ℕ :=
  (p.visitedByTapeHead i).card

/-- The number of work tape cells touched along a run path. -/
def space (p : ntm.RunPath input) : ℕ := ∑ i, p.spaceUsedByTape i

/-- Each tape's space usage is bounded by the total space used. -/
lemma spaceUsedByTape_le_space (p : ntm.RunPath input) (i : Fin k) :
    p.spaceUsedByTape i ≤ p.space :=
  Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)

/-- A path with no work tapes uses zero space. -/
@[simp]
lemma space_zero_tapes {ntm : MultiTapeNTM 0 Symbol State} (p : ntm.RunPath input) :
    p.space = 0 := by
  simp [space]

end RunPath

/-- The number of work tape cells touched along a computation path. -/
def ComputationPath.space (p : ntm.ComputationPath input) : ℕ := RunPath.space p.toRunPath

/-- Every computation prefix on `input` touches at most `s` work-tape cells, regardless of its
outcome. This does not require termination. -/
def RunsInSpace (ntm : MultiTapeNTM k Symbol State) (input : List Symbol) (s : ℕ) : Prop :=
  ∀ p : ntm.ComputationPath input, p.space ≤ s

/-- A space bound can be increased. -/
lemma RunsInSpace.mono {s s' : ℕ} (h : ntm.RunsInSpace input s) (hs : s ≤ s') :
    ntm.RunsInSpace input s' :=
  fun p ↦ (h p).trans hs

/-- A machine without work tapes satisfies every space bound. -/
@[simp]
lemma runsInSpace_zero_tapes (ntm : MultiTapeNTM 0 Symbol State) (input : List Symbol) (s : ℕ) :
    ntm.RunsInSpace input s := by
  intro p
  simp [ComputationPath.space, RunPath.space]

end Turing.MultiTapeNTM
