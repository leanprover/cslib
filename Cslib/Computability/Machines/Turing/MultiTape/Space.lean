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

Defines the space used by a run path and computation within time and space bounds. Space
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

/-- `ntm` computes `output` from `input` touching exactly `s` work tape cells. -/
def ComputesInExactSpace (ntm : MultiTapeNTM k Symbol State) (input output : List Symbol) (s : ℕ) :
    Prop :=
  ntm.ComputesSuchThat input output fun p ↦ p.space = s

/-- `ntm` computes `output` from `input` in `t` steps and `s` work tape cells, by a single
computation. -/
def ComputesInExactTimeAndSpace (ntm : MultiTapeNTM k Symbol State) (input output : List Symbol)
    (t s : ℕ) : Prop :=
  ntm.ComputesSuchThat input output fun p ↦ p.time = t ∧ p.space = s

/-- A machine computes `f` between the supplied encodings, within input-indexed bounds.
For every input `a`, at least one halting computation path must output `encOut (f a)` from
`encIn a` within the supplied time and space bounds. Other paths may produce different outputs or
fail to halt, so a nondeterministic machine can compute multiple distinct functions according to
this existential definition. -/
def ComputesFunInTimeAndSpace {α β : Type*}
    (ntm : MultiTapeNTM k Symbol State)
    (encIn : α ↪ List Symbol) (encOut : β ↪ List Symbol)
    (f : α → β) (t s : α → ℕ) : Prop :=
  ∀ a, ∃ t' ≤ t a, ∃ s' ≤ s a,
    ntm.ComputesInExactTimeAndSpace (encIn a) (encOut (f a)) t' s'

/-- Resource bounds can be weakened independently on every input. -/
theorem ComputesFunInTimeAndSpace.mono {α β : Type*}
    {ntm : MultiTapeNTM k Symbol State} {encIn : α ↪ List Symbol} {encOut : β ↪ List Symbol}
    {f : α → β} {t s t' s' : α → ℕ}
    (h : ntm.ComputesFunInTimeAndSpace encIn encOut f t s)
    (ht : ∀ a, t a ≤ t' a) (hs : ∀ a, s a ≤ s' a) :
    ntm.ComputesFunInTimeAndSpace encIn encOut f t' s' := fun a ↦ by
  obtain ⟨u, hu, v, hv, hc⟩ := h a
  exact ⟨u, hu.trans (ht a), v, hv.trans (hs a), hc⟩

/-- A machine emits at most one symbol per step, so the encoded result is no longer than its
time bound. -/
theorem ComputesFunInTimeAndSpace.length_encOut_le {α β : Type*}
    {ntm : MultiTapeNTM k Symbol State} {encIn : α ↪ List Symbol} {encOut : β ↪ List Symbol}
    {f : α → β} {t s : α → ℕ}
    (h : ntm.ComputesFunInTimeAndSpace encIn encOut f t s) (a : α) :
    (encOut (f a)).length ≤ t a := by
  obtain ⟨t', ht', s', _, p, _, hout, htime, _⟩ := h a
  have hlen := RunPath.length_output_le p.toRunPath
  rw [hout, p.head_eq] at hlen
  exact le_trans (by simpa [← htime, ComputationPath.time, RunPath.time] using hlen) ht'

/-- Computability by a nondeterministic machine with a binary tape alphabet and finitely many
states, within the supplied input-indexed bounds. Computation uses the existential path semantics
of `ComputesFunInTimeAndSpace`. -/
def ComputableInTimeAndSpace {α β : Type*}
    (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool) (t s : α → ℕ) : Prop :=
  ∃ (k : ℕ) (State : Type) (_ : Finite State) (ntm : MultiTapeNTM k Bool State),
    ntm.ComputesFunInTimeAndSpace encIn encOut f t s

end Turing.MultiTapeNTM
