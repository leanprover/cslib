/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

import Cslib.Computability.Machines.Turing.MultiTape.ConfigBound
import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Sequential

namespace CslibTests.MultiTapeTM

open Turing

section SharedAPI

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}
variable (tm : MultiTapeTM k Symbol State) (c c' : Cfg k Symbol State input)

-- Inheritance shares the actual objects and predicates, without simulation theorems.
example : tm.initCfg input = (tm : MultiTapeNTM k Symbol State).initCfg input := rfl

example (output : List Symbol) (t s : ℕ) :
    tm.ComputesInTimeAndSpace input output t s ↔
      (tm : MultiTapeNTM k Symbol State).ComputesInExactTimeAndSpace input output t s := Iff.rfl

-- A nondeterministic run can start at any configuration, including a zero-step run.
example (ntm : MultiTapeNTM k Symbol State) : ntm.RunPath c where
  cfgs := [c]
  last := c
  isChainFromTo := List.isChainFromTo_singleton

-- Relational hypotheses simplify to function equations in either direction.
example (q : State) (i : Option Symbol) (w : Fin k → Option Symbol) (a : Action k Symbol State)
    (h : tm.Tr q i w a) : tm.tr q i w = a := by simpa using h

example (q : State) (i : Option Symbol) (w : Fin k → Option Symbol) (a : Action k Symbol State)
    (h : tm.tr q i w = a) : tm.Tr q i w a := by simpa using h

example (h : tm.Step c c') : tm.step c = c' := by simpa using h

example (h : tm.step c = c') : tm.Step c c' := by simpa using h

-- The shared halting theorem also proves deterministic equalities inside other expressions.
example {α : Type*} (f : Cfg k Symbol State input → α) (h : c.state = none) :
    f (tm.step c) = f c := congrArg f ((MultiTapeNTM.step_of_halt h).mp (tm.step_spec c))

-- A theorem proved for nondeterministic steps applies to a deterministic step directly.
example (i : Fin k) : |(tm.step c).workTapePos i - c.workTapePos i| ≤ 1 :=
  MultiTapeNTM.Step.workTapePos_le (tm.step_spec c) i

example (p : tm.RunPath c) : p.space ≤ k * p.time + k := p.space_le

-- The shared configuration-list bound applies to deterministic space usage.
example (t : ℕ) : tm.spaceUsed c t ≤ k * t + k := by
  simpa [MultiTapeTM.spaceUsed, Nat.mul_succ] using
    spaceUsedOfCfgs_le (List.ofFn fun n : Fin (t + 1) => tm.runFrom c n)

example (h : c.Halted) (t : ℕ) : tm.runFrom c t = c :=
  Function.iterate_fixed ((MultiTapeNTM.step_of_halt h).mp (tm.step_spec c)) t

example [Fintype Symbol] [Fintype State] {s : ℕ}
    (hs : ∀ t, tm.spaceUsed (tm.initCfg input) t ≤ s) :
    (Set.range fun t => (tm.runFrom (tm.initCfg input) t).core).encard ≤
      (input.length + 2) * storageBound Symbol State k s :=
  tm.encard_cores_le hs

-- Equal cores match steps relationally; uniqueness gives the deterministic equation.
example (h : c.core = c'.core) : (tm.step c).core = (tm.step c').core := by
  obtain ⟨d, hd, hcore⟩ := (tm.step_spec c).exists_core_eq h
  simpa only [← MultiTapeTM.step_iff.mp hd] using hcore

-- Function-based construction recovers the original function through the public simp API.
example (q₀ q : State)
    (f : State → Option Symbol → (Fin k → Option Symbol) → Action k Symbol State)
    (i : Option Symbol) (w : Fin k → Option Symbol) :
    (MultiTapeTM.ofTr q₀ f).tr q i w = f q i w := by simp

-- Shared computability still supplies one deterministic machine witnessing the bounds.
example {α β : Type*} {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    {t s : α → ℕ} (h : MultiTapeTM.ComputableInTimeAndSpace f encIn encOut t s) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State),
      tm.ComputesFunInTimeAndSpace encIn encOut f t s := by
  obtain ⟨k, State, hfinite, ntm, hdet, hcomputes⟩ := h
  exact ⟨k, State, hfinite, ⟨ntm, hdet⟩, hcomputes⟩

-- The deterministic constructor inherits the nondeterministic composition theorem by definition.
example {State₀ State₁ : Type*}
    (tm₀ : MultiTapeTM k Symbol State₀) (tm₁ : MultiTapeTM k Symbol State₁)
    {P₀ P₁ : List Symbol → (Fin k → List Symbol) → Prop}
    {Q₀ Q₁ : List Symbol → (Fin k → List Symbol) → (Fin k → List Symbol) → Prop}
    {t₀ s₀ t₁ s₁ : ℕ}
    (h₀ : tm₀.TransformsTapes P₀ Q₀ t₀ s₀) (h₁ : tm₁.TransformsTapes P₁ Q₁ t₁ s₁)
    (hmid : ∀ input ws ws', P₀ input ws → Q₀ input ws ws' → P₁ input ws') :
    (tm₀.seq tm₁).TransformsTapes P₀
      (fun input ws ws'' => ∃ ws', Q₀ input ws ws' ∧ Q₁ input ws' ws'')
      (t₀ + t₁) (s₀ + s₁) :=
  MultiTapeNTM.transformsTapes_seq h₀ h₁ hmid

end SharedAPI

private def stopAction : Action 0 Bool Unit := ⟨0, Fin.elim0, none, none⟩

-- This constructor supplies only a relation and its law, with no transition function.
private def stop : MultiTapeTM 0 Bool Unit where
  q₀ := ()
  Tr _ _ _ action := action = stopAction
  deterministic _ _ _ := by simp

example (i : Option Bool) (w : Fin 0 → Option Bool) : stop.tr () i w = stopAction := by
  apply MultiTapeTM.tr_iff.mp
  rfl

example (input : List Bool) : stop.ComputesInExactTimeAndSpace input [] 1 0 := by
  have htr : ∀ i w, stop.tr () i w = stopAction := fun _ _ => MultiTapeTM.tr_iff.mp rfl
  have hstep : stop.step (stop.initCfg input) = stopAction.apply (stop.initCfg input) := by
    rw [MultiTapeTM.step_of_state (by rfl), htr]
  let p : stop.ComputationPath input :=
    { cfgs := [stop.initCfg input, stopAction.apply (stop.initCfg input)]
      last := stopAction.apply (stop.initCfg input)
      isChainFromTo := by simpa using hstep }
  exact ⟨p, rfl, rfl, rfl, p.space_zero_tapes rfl⟩

-- Stuck machines remain possible in the weaker type.
private def stuck : MultiTapeNTM 0 Bool Unit where
  q₀ := ()
  Tr _ _ _ _ := False

example (input : List Bool) (c : Cfg 0 Bool Unit input) : ¬ stuck.Step (stuck.initCfg input) c := by
  simp [MultiTapeNTM.Step, stuck]

-- A stuck initial configuration has only zero-step paths; totality is not assumed.
example (input : List Bool) (p : stuck.ComputationPath input) : p.time = 0 := by
  by_contra h
  have hstep := p.step_getElem 0 (by rw [p.length_eq_time_add_one]; omega)
  simp [MultiTapeNTM.Step, stuck] at hstep

-- A genuine branching machine has two different successful runs from the same input.
private def emit (b : Bool) : Action 1 Bool Unit :=
  ⟨0, fun _ => (none, if b then 1 else -1), some b, none⟩

private def branching : MultiTapeNTM 1 Bool Unit where
  q₀ := ()
  Tr _ _ _ action := ∃ b, action = emit b

private def branchPath (input : List Bool) (b : Bool) : branching.ComputationPath input where
  cfgs := [branching.initCfg input, (emit b).apply (branching.initCfg input)]
  last := (emit b).apply (branching.initCfg input)
  isChainFromTo := by
    rw [List.isChainFromTo_pair_iff]
    refine ⟨?_, rfl, rfl⟩
    exact ⟨emit b, ⟨b, rfl⟩, rfl⟩

example (input : List Bool) (b : Bool) :
    branching.ComputesInExactTimeAndSpace input [b] 1 2 := by
  refine ⟨branchPath input b, rfl, rfl, rfl, ?_⟩
  cases b <;> simp [MultiTapeNTM.RunPath.space, spaceUsedOfCfgs,
    visitedOfCfgs, branchPath, emit]

-- A genuinely branching path can be padded without changing its chosen output or its space.
example (input : List Bool) (b : Bool) (n : ℕ) :
    branching.ComputesInExactTimeAndSpace input [b] (1 + n) 2 := by
  have hhalt : (branchPath input b).last.Halted := rfl
  refine ⟨(branchPath input b).pad n hhalt, hhalt, rfl, ?_, ?_⟩
  · exact ((branchPath input b).time_pad n hhalt).trans rfl
  · rw [MultiTapeNTM.RunPath.space_pad]
    cases b <;> simp [MultiTapeNTM.RunPath.space, spaceUsedOfCfgs,
      visitedOfCfgs, branchPath, emit]

-- Halting is absorbing for the common step relation, including a branching machine.
example (input : List Bool) (b : Bool) (c : Cfg 1 Bool Unit input) :
    branching.Step (branchPath input b).last c ↔ c = (branchPath input b).last :=
  MultiTapeNTM.step_of_halt rfl

-- Every continuation of a halted branch preserves its output, whatever its length.
example (input : List Bool) (b : Bool) (p : branching.RunPath (branchPath input b).last) :
    p.last.output = [b] := by
  rw [p.last_eq_of_halt rfl]
  rfl

-- Relational reachability can be repackaged as a computation path of a branching machine.
example (input : List Bool) (b : Bool) :
    ∃ p : branching.ComputationPath input, p.time = 1 ∧ p.last.output = [b] := by
  obtain ⟨p, ht, hl⟩ := MultiTapeNTM.relatesInSteps_iff_exists_runPath.mp
    (branchPath input b).relatesInSteps
  exact ⟨p, ht, by rw [hl]; rfl⟩

end CslibTests.MultiTapeTM
