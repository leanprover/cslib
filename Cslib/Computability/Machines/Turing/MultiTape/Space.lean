/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger, Aviv Bar Natan
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Cslib.Computability.Machines.Turing.MultiTape.Nondeterministic

/-!
# Space usage of multi-tape Turing machines

Defines the space used by a run path and decision within time and space bounds. Space
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

Space bounds apply to every computation prefix, including rejecting branches, following the
visited-cell convention in [Watrous, §2.1]
(https://cs.uwaterloo.ca/~watrous/Papers/SpaceBoundedQuantumSimulation.pdf).
`UsesSpace` does not require termination; `DecidesInTimeAndSpace` also bounds running time.

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

end RunPath

/-- The number of work tape cells touched along a computation path. -/
def ComputationPath.space (p : ntm.ComputationPath input) : ℕ := RunPath.space p.toRunPath

/-- Every computation prefix on `input` touches at most `s` work-tape cells. This bounds
rejecting branches as well as successful ones, and does not itself require termination. -/
def UsesSpace (ntm : MultiTapeNTM k Symbol State) (input : List Symbol) (s : ℕ) : Prop :=
  ∀ p : ntm.ComputationPath input, p.space ≤ s

/-- The machine accepts exactly the members of `L`, within time and space bounds on every branch.
Halting outputs are `[true]` for acceptance and `[false]` for rejection. A branch with no permitted
transition also rejects. A member may have rejecting branches; a nonmember has no accepting one. -/
def DecidesInTimeAndSpace {α : Type*} (ntm : MultiTapeNTM k Bool State)
    (L : Set α) (enc : α ↪ List Bool) (t s : α → ℕ) : Prop :=
  ∀ a, (ntm.Accepts (enc a) ↔ a ∈ L) ∧
    ntm.RunsInTime (enc a) (t a) ∧ ntm.UsesSpace (enc a) (s a) ∧
    ∀ p : ntm.ComputationPath (enc a), p.last.Halted →
      p.last.output = [true] ∨ p.last.output = [false]

/-- Resource bounds can be weakened independently on every input. -/
theorem DecidesInTimeAndSpace.mono {α : Type*} {ntm : MultiTapeNTM k Bool State}
    {L : Set α} {enc : α ↪ List Bool} {t s t' s' : α → ℕ}
    (h : ntm.DecidesInTimeAndSpace L enc t s)
    (ht : ∀ a, t a ≤ t' a) (hs : ∀ a, s a ≤ s' a) :
    ntm.DecidesInTimeAndSpace L enc t' s' := fun a ↦
  ⟨(h a).1, (h a).2.1.mono (ht a), fun p ↦ ((h a).2.2.1 p).trans (hs a), (h a).2.2.2⟩

/-- A language is decidable within the bounds by a nondeterministic machine with a binary tape
alphabet and finitely many states. -/
def DecidableInTimeAndSpace {α : Type*} (L : Set α) (enc : α ↪ List Bool)
    (t s : α → ℕ) : Prop :=
  ∃ (k : ℕ) (State : Type) (_ : Finite State) (ntm : MultiTapeNTM k Bool State),
    ntm.DecidesInTimeAndSpace L enc t s

end Turing.MultiTapeNTM
