/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas

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

example (t : ℕ) : tm.spaceUsed c t = (tm.runPath c t).space := rfl

example (t : ℕ) (i : Fin k) : tm.spaceUsedByTape c t i = (tm.runPath c t).spaceByTape i := rfl

example (p : tm.ComputationPath input c) :
    p = tm.runPath c p.time := tm.eq_runPath p

-- Relational hypotheses simplify to function equations in either direction.
example (q : State) (i : Option Symbol) (w : Fin k → Option Symbol) (a : Action k Symbol State)
    (h : tm.Tr q i w a) : tm.tr q i w = a := by simpa using h

example (q : State) (i : Option Symbol) (w : Fin k → Option Symbol) (a : Action k Symbol State)
    (h : tm.tr q i w = a) : tm.Tr q i w a := by simpa using h

example (h : tm.Step c c') : tm.step c = c' := by simpa using h

example (h : tm.step c = c') : tm.Step c c' := by simpa using h

-- A theorem proved for nondeterministic steps applies to a deterministic step directly.
example (i : Fin k) : |(tm.step c).workTapePos i - c.workTapePos i| ≤ 1 :=
  MultiTapeNTM.Step.workTapePos_le (tm.step_step c) i

example (p : tm.ComputationPath input c) : p.space ≤ k * p.time + k := p.space_le

-- Function-based construction recovers the original function through the public simp API.
example (q₀ q : State)
    (f : State → Option Symbol → (Fin k → Option Symbol) → Action k Symbol State)
    (i : Option Symbol) (w : Fin k → Option Symbol) :
    (MultiTapeTM.ofTr q₀ f).tr q i w = f q i w := by simp

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
  apply MultiTapeTM.computesInExactTimeAndSpace_iff_runFrom.mpr
  have htr : ∀ i w, stop.tr () i w = stopAction := fun _ _ => MultiTapeTM.tr_iff.mp rfl
  have hstep : stop.step (stop.initCfg input) = stopAction.apply (stop.initCfg input) := by
    change (stop.tr () _ _).apply _ = _
    rw [htr]
  simp only [MultiTapeTM.runFrom, Function.iterate_one, hstep]
  exact ⟨rfl, rfl, stop.spaceUsed_zero_tapes_eq_zero _ _ rfl⟩

-- Stuck machines remain possible in the weaker type.
private def stuck : MultiTapeNTM 0 Bool Unit where
  q₀ := ()
  Tr _ _ _ _ := False

example (input : List Bool) (c : Cfg 0 Bool Unit input) : ¬ stuck.Step (stuck.initCfg input) c := by
  simp [MultiTapeNTM.Step, stuck]

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
  cases b <;> simp [MultiTapeNTM.ComputationPath.space, spaceUsedOfCfgs,
    visitedOfCfgs, branchPath, emit]

-- Halting is absorbing for the common step relation, including a branching machine.
example (input : List Bool) (b : Bool) (c : Cfg 1 Bool Unit input) :
    branching.Step (branchPath input b).last c ↔ c = (branchPath input b).last :=
  MultiTapeNTM.step_of_halt rfl

end CslibTests.MultiTapeTM
