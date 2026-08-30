/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module

public import Mathlib.Data.List.Chain
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
* `ComputationPath`: a run of the machine: a non-empty list of configurations, each reached from
    the previous by a step, with `start` and `last` read off it
* `ComputationPath.space_le_linear`: a machine touches at most `k` cells per step
* `ComputationPath.single`, `ComputationPath.concat`: the runs of no steps and of one more,
    with `ComputationPath.induction` to reason by cases on the two
* `ComputationPath.reflTransGen`: a run reaches its last configuration from its first
* `ComputationPath.eq_of_start_of_time`: a machine whose steps are unique has exactly one run of
    each length from each configuration
* `ComputesSuchThat`: some computation halts, emits a given output and meets a given constraint
* `Computes`, `ComputesInExactTime`, `ComputesInExactSpace`, `ComputesInExactTimeAndSpace`:
    its instances, whose
    bounds all refer to a single computation

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
  c₁.StepWith c₂ fun q action => ntm.Tr q c₁.inputSymbol c₁.workTapeSymbols action

/-- A halted configuration steps only to itself. -/
lemma step_of_halt {c c' : Cfg k Symbol State input} (h : c.Halted) :
    ntm.Step c c' ↔ c' = c := by
  simp [Step, Cfg.StepWith, h]

/-- The initial configuration corresponding to an input string. -/
@[simp]
def initCfg (ntm : MultiTapeNTM k Symbol State) (input : List Symbol) :
    Cfg k Symbol State input :=
  Cfg.init ntm.q₀ input

/-- A computation path of `ntm` on `input`: the configurations it passes through, forming a
non-empty chain of steps. Neither end is designated; `start` and `last` are read off it. -/
structure ComputationPath (ntm : MultiTapeNTM k Symbol State) (input : List Symbol) where
  /-- the configurations passed through -/
  cfgs : List (Cfg k Symbol State input)
  /-- a run passes through at least one configuration -/
  ne_nil : cfgs ≠ []
  /-- consecutive configurations are joined by a step -/
  isChain : cfgs.IsChain ntm.Step

namespace ComputationPath

variable {ntm : MultiTapeNTM k Symbol State} {input : List Symbol}

/-- A run passes through at least one configuration. -/
lemma length_pos (p : ntm.ComputationPath input) : 0 < p.cfgs.length :=
  List.length_pos_iff.mpr p.ne_nil

/-- The configuration the run starts from. -/
def start (p : ntm.ComputationPath input) : Cfg k Symbol State input := p.cfgs.head p.ne_nil

/-- The configuration the run ends at. -/
def last (p : ntm.ComputationPath input) : Cfg k Symbol State input := p.cfgs.getLast p.ne_nil

/-- The number of steps taken, the time the computation takes. -/
def time (p : ntm.ComputationPath input) : ℕ := p.cfgs.length - 1

/-- The number of work tape cells touched. -/
def space (p : ntm.ComputationPath input) : ℕ := spaceUsedOfCfgs p.cfgs

/-- A path visiting `t + 1` configurations takes `t` steps. -/
lemma length_cfgs (p : ntm.ComputationPath input) : p.cfgs.length = p.time + 1 := by
  have := p.length_pos
  simp only [time]
  omega

/-- A machine touches at most `k` cells per step, whether or not it is deterministic. -/
theorem space_le_linear (p : ntm.ComputationPath input) : p.space ≤ k * p.time + k := by
  calc p.space ≤ k * p.cfgs.length := spaceUsedOfCfgs_le _
    _ = k * p.time + k := by rw [p.length_cfgs, Nat.mul_succ]

end ComputationPath

/-- The run that does nothing. -/
def ComputationPath.single {ntm : MultiTapeNTM k Symbol State} (c : Cfg k Symbol State input) :
    ntm.ComputationPath input where
  cfgs := [c]
  ne_nil := by simp
  isChain := by simp

/-- Extend a run by one step at its end. -/
def ComputationPath.concat (p : ntm.ComputationPath input) (c : Cfg k Symbol State input)
    (h : ntm.Step p.last c) : ntm.ComputationPath input where
  cfgs := p.cfgs ++ [c]
  ne_nil := by simp
  isChain := by
    simpa [List.isChain_append, List.getLast?_eq_some_getLast p.ne_nil,
      ComputationPath.last] using ⟨p.isChain, h⟩

@[simp] lemma ComputationPath.single_cfgs (c : Cfg k Symbol State input) :
    (single (ntm := ntm) c).cfgs = [c] := rfl

@[simp] lemma ComputationPath.single_start (c : Cfg k Symbol State input) :
    (single (ntm := ntm) c).start = c := rfl

@[simp] lemma ComputationPath.single_last (c : Cfg k Symbol State input) :
    (single (ntm := ntm) c).last = c := rfl

@[simp] lemma ComputationPath.single_time (c : Cfg k Symbol State input) :
    (single (ntm := ntm) c).time = 0 := rfl

@[simp] lemma ComputationPath.concat_cfgs (p : ntm.ComputationPath input) (c) (h) :
    (p.concat c h).cfgs = p.cfgs ++ [c] := rfl

@[simp] lemma ComputationPath.concat_last (p : ntm.ComputationPath input) (c) (h) :
    (p.concat c h).last = c := by simp [concat, last]

@[simp] lemma ComputationPath.concat_start (p : ntm.ComputationPath input) (c) (h) :
    (p.concat c h).start = p.start := by
  simp [concat, start, List.head_append_of_ne_nil p.ne_nil]

@[simp] lemma ComputationPath.concat_time (p : ntm.ComputationPath input) (c) (h) :
    (p.concat c h).time = p.time + 1 := by
  have := p.length_pos
  simp only [concat, time, List.length_append, List.length_cons, List.length_nil]
  omega

/-- Every run is either the run of no steps, or one more step on a shorter run. This gives runs
the induction of an inductive definition while they stay lists. -/
@[elab_as_elim]
theorem ComputationPath.induction {motive : ntm.ComputationPath input → Prop}
    (single : ∀ c, motive (ComputationPath.single c))
    (concat : ∀ (p : ntm.ComputationPath input) c h, motive p → motive (p.concat c h))
    (p : ntm.ComputationPath input) : motive p := by
  obtain ⟨cfgs, ne_nil, isChain⟩ := p
  induction cfgs using List.reverseRecOn with
  | nil => exact absurd rfl ne_nil
  | append_singleton l a ih =>
    rcases eq_or_ne l [] with rfl | hl
    · exact single a
    · have h : l.IsChain ntm.Step ∧ ntm.Step (l.getLast hl) a := by
        simpa [List.isChain_append, List.getLast?_eq_some_getLast hl] using isChain
      exact concat ⟨l, hl, h.1⟩ a h.2 (ih hl h.1)

/-- A run witnesses that its last configuration is reachable from the one it starts at. -/
theorem ComputationPath.reflTransGen (p : ntm.ComputationPath input) :
    Relation.ReflTransGen ntm.Step p.start p.last := by
  induction p using ComputationPath.induction with
  | single c => simp only [ComputationPath.single_start, ComputationPath.single_last]
                exact .refl
  | concat p c h ih => simpa using ih.tail (by simpa using h)

/-- A machine whose steps are unique has at most one run of a given length from a given
configuration: the two agree configuration by configuration. -/
theorem ComputationPath.getElem_eq
    (hdet : ∀ {c c' c'' : Cfg k Symbol State input}, ntm.Step c c' → ntm.Step c c'' → c' = c'')
    {p q : ntm.ComputationPath input} (hs : p.start = q.start) (i : ℕ)
    (h₁ : i < p.cfgs.length) (h₂ : i < q.cfgs.length) : p.cfgs[i] = q.cfgs[i] := by
  induction i with
  | zero => simpa [ComputationPath.start, List.getElem_zero] using hs
  | succ n ih =>
    have hp := List.isChain_iff_getElem.mp p.isChain n h₁
    have hq := List.isChain_iff_getElem.mp q.isChain n h₂
    rw [ih (by omega) (by omega)] at hp
    exact hdet hp hq

/-- Such a machine has at most one run of a given length from a given configuration. -/
theorem ComputationPath.cfgs_eq
    (hdet : ∀ {c c' c'' : Cfg k Symbol State input}, ntm.Step c c' → ntm.Step c c'' → c' = c'')
    {p q : ntm.ComputationPath input} (hs : p.start = q.start) (ht : p.time = q.time) :
    p.cfgs = q.cfgs :=
  List.ext_getElem (by rw [p.length_cfgs, q.length_cfgs, ht])
    fun i h₁ h₂ => ComputationPath.getElem_eq hdet hs i h₁ h₂

/-- Such a machine has exactly one run of a given length from a given configuration. -/
theorem ComputationPath.eq_of_start_of_time
    (hdet : ∀ {c c' c'' : Cfg k Symbol State input}, ntm.Step c c' → ntm.Step c c'' → c' = c'')
    {p q : ntm.ComputationPath input} (hs : p.start = q.start) (ht : p.time = q.time) : p = q := by
  cases p; cases q; simp_all only [ComputationPath.mk.injEq]
  exact cfgs_eq hdet hs ht

/-- `ntm` has a computation on `input` that starts at the initial configuration, halts, emits
`output` and satisfies `P`. The notions below are its instances, so their constraints all refer to
a single computation. -/
def ComputesSuchThat (ntm : MultiTapeNTM k Symbol State) (input output : List Symbol)
    (P : ntm.ComputationPath input → Prop) : Prop :=
  ∃ p : ntm.ComputationPath input, p.start = ntm.initCfg input ∧ p.last.Halted ∧
    p.last.output = output ∧ P p

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

end MultiTapeNTM

end Turing
