/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module

public import Mathlib.Data.List.Chain
public import Cslib.Foundations.Data.RelatesInSteps
public import Cslib.Computability.Machines.Turing.MultiTape.Configuration

/-!
# Nondeterministic Multi-Tape Turing Machines

Defines nondeterministic Turing machines with a read-only input tape, `k` work tapes and one
write-only output tape, and what it means for one to compute an output within a time and space
bound.

## Design

Following [Papadimitriou94], chapter 2.7, the transition relation `Tr q input work action` records
the actions permitted in each situation. A deterministic machine adds the requirement that exactly
one action is permitted; its type and derived evaluator are defined in `Deterministic.lean`.

A halted configuration steps to itself, so once a machine has halted it has a run of every length.
A time bound is therefore an upper bound, with no separate account of the step at which it halted.

The transition relation may be empty at a running configuration, so a machine can get stuck. The
computation predicates ask for a path ending in a halted configuration, so a stuck one is not a
witness.

## Important Declarations

* `MultiTapeNTM`: the machine, an initial state and a transition relation
* `IsDeterministic`: every situation permits exactly one action
* `Step`: the one-step relation on configurations
* `RunPath`: a series of configurations from a specified start, each reached by a step
* `ComputationPath`: a run path starting at the initial configuration
* `ComputesSuchThat`: some computation halts, emits a given output and meets a given constraint
* `Computes`, `ComputesInExactTime`, `ComputesInExactSpace`, `ComputesInExactTimeAndSpace`:
    its instances, whose
    bounds all refer to a single computation
* `ComputesFunInTimeAndSpace`: a successful path for each encoded input, within input-indexed
    bounds; inherited unchanged by deterministic machines
* `ComputableInTimeAndSpace`: existence of a machine within input-indexed resource bounds

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

/-- Every state and tuple of read symbols permits exactly one action. -/
def IsDeterministic (ntm : MultiTapeNTM k Symbol State) : Prop :=
  ∀ (q : State) (input : Option Symbol) (work : Fin k → Option Symbol),
    ∃! action, ntm.Tr q input work action

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

/-- The initial configuration corresponding to an input string. -/
@[simp]
def initCfg (ntm : MultiTapeNTM k Symbol State) (input : List Symbol) :
    Cfg k Symbol State input :=
  Cfg.init ntm.q₀ input

/-- A finite run of `ntm` from `start`. Consecutive configurations form a chain of steps. -/
structure RunPath (ntm : MultiTapeNTM k Symbol State) {input : List Symbol}
    (start : Cfg k Symbol State input) where
  /-- the configurations passed through, starting with `start` -/
  cfgs : List (Cfg k Symbol State input)
  /-- the configuration the path ends at -/
  last : Cfg k Symbol State input
  /-- consecutive configurations are joined by a step, from `start` to `last` -/
  isChainFromTo : cfgs.IsChainFromTo ntm.Step start last

/-- A computation path is a run starting at the initial configuration for `input`. -/
abbrev ComputationPath (ntm : MultiTapeNTM k Symbol State) (input : List Symbol) :=
  ntm.RunPath (ntm.initCfg input)

namespace RunPath

variable {ntm : MultiTapeNTM k Symbol State} {input : List Symbol}
variable {start : Cfg k Symbol State input}

/-- A path is determined by its configuration list; its endpoint is the last entry. -/
@[ext]
theorem ext {p p' : ntm.RunPath start} (h : p.cfgs = p'.cfgs) : p = p' := by
  cases p with
  | mk cfgs last hc =>
    cases p' with
    | mk cfgs' last' hc' =>
      cases h
      have hlast : last = last' := hc.getLast_eq.symm.trans hc'.getLast_eq
      cases hlast
      rfl

/-- The number of steps taken, the time the computation takes. -/
def time (p : ntm.RunPath start) : ℕ := p.cfgs.length - 1

/-- The positions visited by the head of a work tape. -/
def visited (p : ntm.RunPath start) (i : Fin k) : Finset ℤ :=
  visitedOfCfgs p.cfgs i

/-- The number of cells touched on one work tape. -/
def spaceByTape (p : ntm.RunPath start) (i : Fin k) : ℕ := (p.visited i).card

/-- The number of work tape cells touched. -/
def space (p : ntm.RunPath start) : ℕ := spaceUsedOfCfgs p.cfgs

/-- Total space is the sum of the space used by each work tape. -/
lemma space_eq_sum (p : ntm.RunPath start) : p.space = ∑ i, p.spaceByTape i := rfl

/-- A path has one more configuration than steps. -/
lemma length_eq_time_add_one (p : ntm.RunPath start) :
    p.cfgs.length = p.time + 1 := by
  have := p.isChainFromTo.length_pos
  simp only [time]
  omega

/-- Consecutive entries of a path are related by a step. -/
lemma step_getElem (p : ntm.RunPath start) (n : ℕ) (h : n + 1 < p.cfgs.length) :
    ntm.Step p.cfgs[n] p.cfgs[n + 1] := p.isChainFromTo.isChain.getElem n h

/-- The configuration at the start of a path. -/
@[simp]
lemma getElem_zero (p : ntm.RunPath start) :
    p.cfgs[0]'p.isChainFromTo.length_pos = start := p.isChainFromTo.getElem_zero

/-- The configuration at the end of a path. -/
@[simp]
lemma getElem_time (p : ntm.RunPath start) :
    p.cfgs[p.time]'(by rw [p.length_eq_time_add_one]; omega) = p.last :=
  p.isChainFromTo.getElem_length_sub_one

/-- The first `n` steps of a path. -/
@[simps cfgs last]
def take (p : ntm.RunPath start) (n : ℕ) (hn : n < p.cfgs.length) : ntm.RunPath start where
  cfgs := p.cfgs.take (n + 1)
  last := p.cfgs[n]
  isChainFromTo := p.isChainFromTo.take hn

@[simp]
lemma time_take (p : ntm.RunPath start) (n : ℕ) (hn : n < p.cfgs.length) :
    (p.take n hn).time = n := by
  simp [time, take, Nat.min_eq_left (show n + 1 ≤ p.cfgs.length by omega)]

/-- The suffix starting at configuration `n`. -/
@[simps cfgs last]
def drop (p : ntm.RunPath start) (n : ℕ) (hn : n < p.cfgs.length) :
    ntm.RunPath p.cfgs[n] where
  cfgs := p.cfgs.drop n
  last := p.last
  isChainFromTo := p.isChainFromTo.drop hn

@[simp]
lemma time_drop (p : ntm.RunPath start) (n : ℕ) (hn : n < p.cfgs.length) :
    (p.drop n hn).time = p.time - n := by
  simp [time, drop]
  omega

/-- Map a path through a simulation valid for each of its steps. -/
@[simps cfgs last]
def map {State' : Type*} {input' : List Symbol} {ntm' : MultiTapeNTM k Symbol State'}
    (p : ntm.RunPath start) (f : Cfg k Symbol State input → Cfg k Symbol State' input')
    (h : ∀ n (hn : n + 1 < p.cfgs.length), ntm'.Step (f p.cfgs[n]) (f p.cfgs[n + 1])) :
    ntm'.RunPath (f start) where
  cfgs := p.cfgs.map f
  last := f p.last
  isChainFromTo := List.IsChainFromTo.map f
    { p.isChainFromTo with isChain := by simpa [List.isChain_iff_getElem] using h }

@[simp]
lemma time_map {State' : Type*} {input' : List Symbol} {ntm' : MultiTapeNTM k Symbol State'}
    (p : ntm.RunPath start) (f : Cfg k Symbol State input → Cfg k Symbol State' input')
    (h : ∀ n (hn : n + 1 < p.cfgs.length), ntm'.Step (f p.cfgs[n]) (f p.cfgs[n + 1])) :
    (p.map f h).time = p.time := by simp [time, map]

/-- Join paths with matching endpoints, counting their shared configuration once. -/
@[simps cfgs last]
def append {middle : Cfg k Symbol State input}
    (p : ntm.RunPath start) (q : ntm.RunPath middle) (h : p.last = middle) :
    ntm.RunPath start where
  cfgs := p.cfgs ++ q.cfgs.tail
  last := q.last
  isChainFromTo := p.isChainFromTo.append_tail (h ▸ q.isChainFromTo)

@[simp]
lemma time_append {middle : Cfg k Symbol State input}
    (p : ntm.RunPath start) (q : ntm.RunPath middle) (h : p.last = middle) :
    (p.append q h).time = p.time + q.time := by
  simp only [time, append_cfgs, List.length_append, List.length_tail]
  have := p.isChainFromTo.length_pos
  omega

/-- Repeat a halted endpoint for `n` more steps. -/
@[simps cfgs last]
def pad (p : ntm.RunPath start) (n : ℕ) (hhalt : p.last.Halted) : ntm.RunPath start where
  cfgs := p.cfgs ++ List.replicate n p.last
  last := p.last
  isChainFromTo := by
    have hchain : (List.replicate (n + 1) p.last).IsChainFromTo ntm.Step p.last p.last :=
      { isChain := List.isChain_replicate_of_rel _ ((step_of_halt hhalt).mpr rfl)
        ne_nil := by simp
        head_eq := List.head_replicate _
        getLast_eq := List.getLast_replicate _ }
    simpa using p.isChainFromTo.append_tail hchain

@[simp]
lemma time_pad (p : ntm.RunPath start) (n : ℕ) (hhalt : p.last.Halted) :
    (p.pad n hhalt).time = p.time + n := by
  simp only [time, pad_cfgs, List.length_append, List.length_replicate]
  have := p.isChainFromTo.length_pos
  omega

/-- A run path witnesses reachability in exactly its number of steps. -/
lemma relatesInSteps (p : ntm.RunPath start) :
    Relation.RelatesInSteps ntm.Step start p.last p.time :=
  p.isChainFromTo.relatesInSteps p.length_eq_time_add_one

/-- Nothing changes along a path after it reaches a halted configuration. -/
lemma getElem_eq_of_halt (p : ntm.RunPath start) {m n : ℕ} (hmn : m ≤ n)
    (hn : n < p.cfgs.length) (hhalt : (p.cfgs[m]'(hmn.trans_lt hn)).Halted) :
    p.cfgs[n] = p.cfgs[m] := by
  induction n with
  | zero => obtain rfl := Nat.eq_zero_of_le_zero hmn; rfl
  | succ n ih =>
    rcases eq_or_lt_of_le hmn with rfl | hlt
    · rfl
    · have heq := ih (by omega) (by omega) hhalt
      exact ((step_of_halt (heq.symm ▸ hhalt)).mp (p.step_getElem n hn)).trans heq

/-- A run starting in a halted configuration ends at that same configuration. -/
lemma last_eq_of_halt (p : ntm.RunPath start) (hhalt : start.Halted) : p.last = start := by
  simpa using p.getElem_eq_of_halt (m := 0) (n := p.time) (Nat.zero_le _)
    (by rw [p.length_eq_time_add_one]; omega) (by simpa using hhalt)

/-- Every path ending in a halted configuration has a first halting time. -/
lemma exists_minimal_halting_time (p : ntm.RunPath start) (hhalt : p.last.Halted) :
    ∃ (n : ℕ) (hn : n < p.cfgs.length), p.cfgs[n].Halted ∧
      ∀ (m : ℕ) (hm : m < n), ¬(p.cfgs[m]'(hm.trans hn)).Halted := by
  classical
  have hex : ∃ n, ∃ hn : n < p.cfgs.length, p.cfgs[n].Halted :=
    ⟨p.time, by rw [p.length_eq_time_add_one]; omega, by simpa using hhalt⟩
  obtain ⟨hn, hh⟩ := Nat.find_spec hex
  exact ⟨Nat.find hex, hn, hh, fun m hm hh => Nat.find_min hex hm ⟨hm.trans hn, hh⟩⟩

/-- Along one path, at most one step first enters a halted configuration. -/
lemma halting_step_unique (p : ntm.RunPath start) {m n : ℕ}
    (hm : m < p.cfgs.length) (hn : n < p.cfgs.length)
    (hmhalt : p.cfgs[m].Halted ∧ ¬(p.cfgs[m - 1]'(by omega)).Halted)
    (hnhalt : p.cfgs[n].Halted ∧ ¬(p.cfgs[n - 1]'(by omega)).Halted) : m = n := by
  wlog hmn : m ≤ n generalizing m n
  · exact (this hn hm hnhalt hmhalt (Nat.le_of_not_le hmn)).symm
  by_contra hne
  have heq := p.getElem_eq_of_halt (show m ≤ n - 1 by omega) (by omega) hmhalt.1
  exact hnhalt.2 (heq.symm ▸ hmhalt.1)

end RunPath

/-- Reachability in exactly `t` steps is equivalent to a run path of length `t`. -/
lemma relatesInSteps_iff_exists_runPath {start finish : Cfg k Symbol State input} {t : ℕ} :
    Relation.RelatesInSteps ntm.Step start finish t ↔
      ∃ p : ntm.RunPath start, p.time = t ∧ p.last = finish := by
  constructor
  · intro h
    obtain ⟨cfgs, hchain, hlen⟩ := h.exists_isChainFromTo
    exact ⟨⟨cfgs, finish, hchain⟩, by simp [RunPath.time, hlen], rfl⟩
  · rintro ⟨p, rfl, rfl⟩
    exact p.relatesInSteps

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

/-- A function is computable within the input-indexed bounds by a binary machine with finitely
many states. `P` optionally restricts the witnessing machine; by default every machine is
allowed. -/
def ComputableInTimeAndSpace {α β : Type*}
    (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool) (t s : α → ℕ)
    (P : ∀ {k : ℕ} {State : Type}, MultiTapeNTM k Bool State → Prop := fun _ => True) :
    Prop :=
  ∃ (k : ℕ) (State : Type) (_ : Finite State) (ntm : MultiTapeNTM k Bool State),
    P ntm ∧ ntm.ComputesFunInTimeAndSpace encIn encOut f t s

end MultiTapeNTM

end Turing
