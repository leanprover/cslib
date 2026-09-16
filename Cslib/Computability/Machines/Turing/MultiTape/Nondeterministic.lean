/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module

public import Mathlib.Data.List.Chain
public import Mathlib.Data.Int.Interval
public import Cslib.Foundations.Data.List.IsChainFromTo
public import Cslib.Computability.Machines.Turing.MultiTape.Configuration

/-!
# Nondeterministic Multi-Tape Turing Machines

Defines nondeterministic Turing machines with a read-only input tape, `k` work tapes and one
write-only output tape, and what it means for one to compute an output within a time and space
bound.

## Design

Following [Papadimitriou94], chapter 2.7, a nondeterministic machine is a Turing machine whose
transition function is replaced by a transition relation: `Tr q input work action` holds when
`action` is one of the actions permitted in that situation.

A halted configuration steps to itself, so once a machine has halted it has a run of every length.
A time bound is therefore an upper bound, with no separate account of the step at which it halted.

The transition relation may be empty at a running configuration, so a machine can get stuck. Every
notion below asks for a computation ending in a halted configuration, so a stuck one is not a
witness.

## Important Declarations

* `MultiTapeNTM`: the machine, an initial state and a transition relation
* `Step`: the one-step relation on configurations
* `ComputationPath`: a series of configurations from a specified start, which defaults to the
    initial configuration, each reached from the previous by a step
* `ComputationPath.space_le`: every path uses at most `k * time + k` work tape cells
* `ComputationPath.mem_visited_of_workTapes_ne`: a changed work tape cell was visited
* `ComputesSuchThat`: some computation halts, emits a given output and meets a given constraint
* `Computes`, `ComputesInExactTime`, `ComputesInExactSpace`, `ComputesInExactTimeAndSpace`:
    its instances, whose
    bounds all refer to a single computation
* `ComputesFunInTimeAndSpace`: a successful path for each encoded input, within input-indexed
    bounds; inherited unchanged by deterministic machines

## References

* [C. Papadimitriou, *Computational Complexity*][Papadimitriou94]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Turing

variable {k : ℕ} {State Symbol : Type*} {input : List Symbol}

/--
A nondeterministic multi-tape Turing machine with `k` work tapes over the alphabet of
`Option Symbol` (where `none` is the blank symbol). Neither `Symbol` nor `State` is required to be
finite.
-/
structure MultiTapeNTM (k : ℕ) (Symbol State : Type*) where
  /-- initial state -/
  q₀ : State
  /-- transition relation: which combinations of state, current input symbol, tuple of work head
  symbols and resulting actions are valid transitions -/
  Tr (q : State) (input : Option Symbol) (work : Fin k → Option Symbol)
    (action : Action k Symbol State) : Prop

namespace MultiTapeNTM

variable {ntm : MultiTapeNTM k Symbol State}

/-- The one-step relation on configurations. A halted configuration steps to itself; a running one
steps by any permitted transition. -/
@[scoped grind =]
def Step (ntm : MultiTapeNTM k Symbol State) (c₁ c₂ : Cfg k Symbol State input) : Prop :=
  match c₁.state with
  | none => c₂ = c₁
  | some q =>
    ∃ action, ntm.Tr q c₁.inputSymbol c₁.workTapeSymbols action ∧ c₂ = action.apply c₁

/-- A halted configuration steps only to itself. -/
lemma step_of_halt {c c' : Cfg k Symbol State input} (h : c.Halted) :
    ntm.Step c c' ↔ c' = c := by
  simp [Step, h]

/-- A work tape head moves by at most one cell in a step. -/
lemma Step.workTapePos_le {c c' : Cfg k Symbol State input} (h : ntm.Step c c') (i : Fin k) :
    |c'.workTapePos i - c.workTapePos i| ≤ 1 := by
  cases hs : c.state with
  | none => obtain rfl := (step_of_halt hs).mp h; simp
  | some q =>
    obtain ⟨action, _, rfl⟩ := (show ∃ action, ntm.Tr q c.inputSymbol c.workTapeSymbols action ∧
      c' = action.apply c from by simpa [Step, hs] using h)
    exact workTapePos_apply_le action c i

/-- A step preserves every work tape cell away from its head. -/
lemma Step.workTapes_eq_of_ne {c c' : Cfg k Symbol State input} (h : ntm.Step c c')
    (i : Fin k) (z : ℤ) (hz : z ≠ c.workTapePos i) : c'.workTapes i z = c.workTapes i z := by
  cases hs : c.state with
  | none => obtain rfl := (step_of_halt hs).mp h; rfl
  | some q =>
    obtain ⟨action, _, rfl⟩ := (show ∃ action, ntm.Tr q c.inputSymbol c.workTapeSymbols action ∧
      c' = action.apply c from by simpa [Step, hs] using h)
    exact action.apply_workTapes_eq_of_ne c i z hz

/-- The initial configuration corresponding to an input string. -/
@[simp]
def initCfg (ntm : MultiTapeNTM k Symbol State) (input : List Symbol) :
    Cfg k Symbol State input :=
  Cfg.init ntm.q₀ input

/-- A computation path of `ntm` on `input`, starting at `start`, which defaults to the initial
configuration. Consecutive configurations form a chain of steps. -/
structure ComputationPath (ntm : MultiTapeNTM k Symbol State) (input : List Symbol)
    (start : Cfg k Symbol State input := ntm.initCfg input) where
  /-- the configurations passed through, starting with `start` -/
  cfgs : List (Cfg k Symbol State input)
  /-- the configuration the path ends at -/
  last : Cfg k Symbol State input
  /-- consecutive configurations are joined by a step, from `start` to `last` -/
  isChainFromTo : cfgs.IsChainFromTo ntm.Step start last

namespace ComputationPath

variable {ntm : MultiTapeNTM k Symbol State} {input : List Symbol}
variable {start : Cfg k Symbol State input}

/-- A path is determined by its configuration list; its endpoint is the last entry. -/
@[ext]
theorem ext {p p' : ntm.ComputationPath input start} (h : p.cfgs = p'.cfgs) : p = p' := by
  cases p with
  | mk cfgs last hc =>
    cases p' with
    | mk cfgs' last' hc' =>
      cases h
      have hlast : last = last' := hc.getLast_eq.symm.trans hc'.getLast_eq
      cases hlast
      rfl

/-- The number of steps taken, the time the computation takes. -/
def time (p : ntm.ComputationPath input start) : ℕ := p.cfgs.length - 1

/-- The positions visited by the head of a work tape. -/
def visited (p : ntm.ComputationPath input start) (i : Fin k) : Finset ℤ :=
  visitedOfCfgs p.cfgs i

/-- The number of cells touched on one work tape. -/
def spaceByTape (p : ntm.ComputationPath input start) (i : Fin k) : ℕ := (p.visited i).card

/-- The number of work tape cells touched. -/
def space (p : ntm.ComputationPath input start) : ℕ := spaceUsedOfCfgs p.cfgs

/-- A path has one more configuration than steps. -/
lemma length_eq_time_add_one (p : ntm.ComputationPath input start) :
    p.cfgs.length = p.time + 1 := by
  have := p.isChainFromTo.length_pos
  simp only [time]
  omega

/-- Consecutive entries of a path are related by a step. -/
lemma step_getElem (p : ntm.ComputationPath input start) (n : ℕ) (h : n + 1 < p.cfgs.length) :
    ntm.Step p.cfgs[n] p.cfgs[n + 1] := p.isChainFromTo.isChain.getElem n h

/-- The configuration at the start of a path. -/
@[simp]
lemma getElem_zero (p : ntm.ComputationPath input start) :
    p.cfgs[0]'p.isChainFromTo.length_pos = start := p.isChainFromTo.getElem_zero

/-- The configuration at the end of a path. -/
@[simp]
lemma getElem_time (p : ntm.ComputationPath input start) :
    p.cfgs[p.time]'(by rw [p.length_eq_time_add_one]; omega) = p.last :=
  p.isChainFromTo.getElem_length_sub_one

/-- A head position in any configuration on the path is visited. -/
lemma workTapePos_mem_visited (p : ntm.ComputationPath input start) (i : Fin k)
    (n : ℕ) (h : n < p.cfgs.length) : p.cfgs[n].workTapePos i ∈ p.visited i := by
  simp only [visited, visitedOfCfgs, List.mem_toFinset, List.mem_map]
  exact ⟨p.cfgs[n], List.getElem_mem h, rfl⟩

/-- Every position between the starting head and any later head position is visited. -/
lemma uIcc_workTapePos_getElem_subset_visited (p : ntm.ComputationPath input start)
    (i : Fin k) (n : ℕ) (h : n < p.cfgs.length) :
    Finset.uIcc (start.workTapePos i) (p.cfgs[n].workTapePos i) ⊆ p.visited i := by
  induction n with
  | zero => simpa using p.workTapePos_mem_visited i 0 h
  | succ n ih =>
    have hprev := ih (by omega)
    have hstep := (p.step_getElem n h).workTapePos_le i
    have hself := p.workTapePos_mem_visited i (n + 1) h
    intro z hz
    grind [Finset.mem_uIcc]

/-- A changed work tape cell must have been visited. -/
lemma mem_visited_of_getElem_workTapes_ne (p : ntm.ComputationPath input start)
    (i : Fin k) (z : ℤ) (n : ℕ) (hn : n < p.cfgs.length)
    (h : p.cfgs[n].workTapes i z ≠ start.workTapes i z) : z ∈ p.visited i := by
  induction n with
  | zero => simp at h
  | succ n ih =>
    by_cases hz : z = p.cfgs[n].workTapePos i
    · exact hz ▸ p.workTapePos_mem_visited i n (by omega)
    · rw [(p.step_getElem n hn).workTapes_eq_of_ne i z hz] at h
      exact ih (by omega) h

/-- All positions between the starting and final work tape heads are visited. -/
lemma uIcc_workTapePos_subset_visited (p : ntm.ComputationPath input start) (i : Fin k) :
    Finset.uIcc (start.workTapePos i) (p.last.workTapePos i) ⊆ p.visited i := by
  simpa using p.uIcc_workTapePos_getElem_subset_visited i p.time
    (by rw [p.length_eq_time_add_one]; omega)

/-- Any cell whose final contents differ from its initial contents has been visited. -/
lemma mem_visited_of_workTapes_ne (p : ntm.ComputationPath input start) (i : Fin k) (z : ℤ)
    (h : p.last.workTapes i z ≠ start.workTapes i z) : z ∈ p.visited i :=
  p.mem_visited_of_getElem_workTapes_ne i z p.time
    (by rw [p.length_eq_time_add_one]; omega) (by simpa using h)

/-- The displacement of a visited cell is bounded by the tape's space usage. -/
lemma natAbs_le_spaceByTape_of_mem_visited (p : ntm.ComputationPath input start)
    (i : Fin k) {z : ℤ} (hz : z ∈ p.visited i) :
    (z - start.workTapePos i).natAbs ≤ p.spaceByTape i := by
  simp only [visited, visitedOfCfgs, List.mem_toFinset, List.mem_map] at hz
  obtain ⟨c, hc, rfl⟩ := hz
  obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hc
  have h := Finset.card_le_card (p.uIcc_workTapePos_getElem_subset_visited i n hn)
  rw [Int.card_uIcc] at h
  exact (Nat.le_succ _).trans h

/-- Each tape visits at most one additional cell per step. -/
lemma spaceByTape_le (p : ntm.ComputationPath input start) (i : Fin k) :
    p.spaceByTape i ≤ p.time + 1 := by
  simpa only [spaceByTape, visited, ← p.length_eq_time_add_one] using
    card_visitedOfCfgs_le p.cfgs i

/-- Total space is at most the number of configurations times the number of tapes. -/
lemma space_le (p : ntm.ComputationPath input start) : p.space ≤ k * p.time + k := by
  simpa only [space, p.length_eq_time_add_one, Nat.mul_succ] using spaceUsedOfCfgs_le p.cfgs

/-- Each tape's space usage is bounded by the total space. -/
lemma spaceByTape_le_space (p : ntm.ComputationPath input start) (i : Fin k) :
    p.spaceByTape i ≤ p.space :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

/-- A path of a zero-work-tape machine uses no work space. -/
@[simp]
lemma space_zero_tapes (p : ntm.ComputationPath input start) (h : k = 0) : p.space = 0 := by
  subst k
  simp [space, spaceUsedOfCfgs]

end ComputationPath

/-- `ntm` has a computation on `input` that starts at the initial configuration, halts, emits
`output` and satisfies `P`. The notions below are its instances, so their constraints all refer to
a single computation. -/
def ComputesSuchThat (ntm : MultiTapeNTM k Symbol State) (input output : List Symbol)
    (P : ntm.ComputationPath input → Prop) : Prop :=
  ∃ p : ntm.ComputationPath input, p.last.Halted ∧ p.last.output = output ∧ P p

/-- `ntm` computes `output` from `input`, with no bound on resources. -/
def Computes (ntm : MultiTapeNTM k Symbol State) (input output : List Symbol) : Prop :=
  ntm.ComputesSuchThat input output fun _ => True

/-- `ntm` computes `output` from `input` in exactly `t` steps. -/
def ComputesInExactTime (ntm : MultiTapeNTM k Symbol State) (input output : List Symbol) (t : ℕ) :
    Prop :=
  ntm.ComputesSuchThat input output fun p => p.time = t

/-- `ntm` computes `output` from `input` touching exactly `s` work tape cells. -/
def ComputesInExactSpace (ntm : MultiTapeNTM k Symbol State) (input output : List Symbol) (s : ℕ) :
    Prop :=
  ntm.ComputesSuchThat input output fun p => p.space = s

/-- `ntm` computes `output` from `input` in `t` steps and `s` work tape cells, by a single
computation. -/
def ComputesInExactTimeAndSpace (ntm : MultiTapeNTM k Symbol State) (input output : List Symbol)
    (t s : ℕ) : Prop :=
  ntm.ComputesSuchThat input output fun p => p.time = t ∧ p.space = s

/-- A compatibility spelling for computation with exact path length and space usage. Halting
configurations can be repeated to pad the path length. -/
abbrev ComputesInTimeAndSpace := @ComputesInExactTimeAndSpace

/-- A machine computes `f` between the supplied encodings, within input-indexed bounds.
For a nondeterministic machine this asks for one successful path for each input. -/
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
    ntm.ComputesFunInTimeAndSpace encIn encOut f t' s' := fun a => by
  obtain ⟨u, hu, v, hv, hc⟩ := h a
  exact ⟨u, hu.trans (ht a), v, hv.trans (hs a), hc⟩

end MultiTapeNTM

end Turing
