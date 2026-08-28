/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Cslib.Computability.Machines.Turing.MultiTape.Nondeterministic

/-!
# Deterministic Multi-Tape Turing Machines are Nondeterministic

Embeds `MultiTapeTM` into `MultiTapeNTM` and shows the embedding preserves computation.

`toNTM` permits exactly the transition `tr` prescribes: nondeterminism is the possibility of
several, so having exactly one is the special case. A deterministic computation is then witnessed
by the machine's own run. Both models idle once the machine has halted, so that run has exactly
`t` steps for every `t` and its measures match `runFrom` and `spaceUsed` directly, with no
reasoning about the step at which the machine halted.

## Important Declarations

* `MultiTapeTM.toNTM`: every deterministic machine is a nondeterministic one
* `MultiTapeTM.toNTMComputationPath`: the machine's own run, as a computation of `toNTM`
* `MultiTapeTM.toNTM_computes`: every deterministic computation is a nondeterministic one
-/

@[expose] public section

namespace Turing

variable {k : ℕ} {State Symbol : Type*} {input : List Symbol}

/-- Every deterministic machine is a nondeterministic one whose relation is a singleton. -/
def MultiTapeTM.toNTM (tm : MultiTapeTM k Symbol State) : MultiTapeNTM k Symbol State where
  q₀ := tm.q₀
  Tr q input work out := out = tm.tr q input work

namespace MultiTapeTM

variable {tm : MultiTapeTM k Symbol State} {t : ℕ}

@[simp]
lemma toNTM_initCfg (tm : MultiTapeTM k Symbol State) (input : List Symbol) :
    tm.toNTM.initCfg input = tm.initCfg input := rfl

/-- Each step of `tm` is a step of its nondeterministic reading. This holds at a halted
configuration too, where both models idle. -/
theorem toNTM_step (c : Cfg k Symbol State input) : tm.toNTM.Step c (tm.step c) := by
  cases hq : c.state <;> simp [MultiTapeNTM.Step, step, toNTM, hq]

/-- The configurations the machine passes through form a chain of steps. -/
lemma isChain_map_range (cfg : Cfg k Symbol State input) (t : ℕ) :
    ((List.range (t + 1)).map (tm.runFrom cfg)).IsChain tm.toNTM.Step := by
  rw [List.isChain_iff_getElem]
  intro i hi
  simp only [List.getElem_map, List.getElem_range]
  rw [runFrom_succ_eq_step']
  exact toNTM_step _

/-- The machine's own run for `t` steps, as a computation of its nondeterministic reading: the
configuration reached after each step. -/
def toNTMComputationPath (tm : MultiTapeTM k Symbol State) (input : List Symbol) (t : ℕ) :
    tm.toNTM.ComputationPath input where
  cfgs := (List.range (t + 1)).map (tm.runFrom (tm.initCfg input))
  last := tm.runFrom (tm.initCfg input) t
  isChainFromTo :=
    { isChain := isChain_map_range _ t
      ne_nil := by simp
      head_eq := by
        rw [List.head_map]
        simp [toNTM]
      getLast_eq := by
        rw [← Option.some_inj, ← List.getLast?_eq_some_getLast, List.range_succ, List.map_append]
        simp }

@[simp]
lemma toNTMComputationPath_time : (tm.toNTMComputationPath input t).time = t := by
  simp [MultiTapeNTM.ComputationPath.time, toNTMComputationPath]

@[simp]
lemma toNTMComputationPath_cfgs :
    (tm.toNTMComputationPath input t).cfgs
      = (List.range (t + 1)).map (tm.runFrom (tm.initCfg input)) := rfl

@[simp]
lemma toNTMComputationPath_last :
    (tm.toNTMComputationPath input t).last = tm.runFrom (tm.initCfg input) t := rfl

@[simp]
lemma toNTMComputationPath_space :
    (tm.toNTMComputationPath input t).space = tm.spaceUsed (tm.initCfg input) t := by
  simp [MultiTapeNTM.ComputationPath.space, spaceUsed_eq_spaceUsedOfCfgs]

/-- Every deterministic computation is a nondeterministic one, witnessed by the machine's own
run. -/
theorem toNTM_computes {output : List Symbol} {t s : ℕ}
    (h : tm.ComputesInTimeAndSpace input output t s) :
    tm.toNTM.ComputesInExactTimeAndSpace input output t s :=
  ⟨tm.toNTMComputationPath input t, by simpa using h.1, by simpa using h.2.1,
    toNTMComputationPath_time, toNTMComputationPath_space.trans h.2.2⟩

end MultiTapeTM

end Turing
