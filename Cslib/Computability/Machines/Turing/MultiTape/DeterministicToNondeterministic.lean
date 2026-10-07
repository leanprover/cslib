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
* `MultiTapeTM.toNTMComputationPath`: the machine's own run forms a computation of `toNTM`
* `MultiTapeTM.toNTM_computes`: every deterministic computation is a nondeterministic one
-/

@[expose] public section

namespace Turing

variable {k : ℕ} {State Symbol : Type*} {input : List Symbol}

/-- Every deterministic machine is a nondeterministic one whose relation is a singleton. -/
def MultiTapeTM.toNTM (tm : MultiTapeTM k Symbol State) : MultiTapeNTM k Symbol State where
  q₀ := tm.q₀
  Tr q input work action := action = tm.tr q input work

namespace MultiTapeTM

variable {tm : MultiTapeTM k Symbol State} {t : ℕ}

@[simp]
lemma toNTM_initCfg (tm : MultiTapeTM k Symbol State) (input : List Symbol) :
    tm.toNTM.initCfg input = tm.initCfg input := rfl

/-- Each step of `tm` is a step of its nondeterministic reading. This holds at a halted
configuration too, where both models idle. -/
theorem toNTM_step (c : Cfg k Symbol State input) : tm.toNTM.Step c (tm.step c) := by
  cases hq : c.state <;> simp [MultiTapeNTM.Step, step, toNTM, hq]

/-- The configurations reached during the machine's first `t` steps form a computation of its
nondeterministic reading. -/
def toNTMComputationPath (tm : MultiTapeTM k Symbol State) (input : List Symbol) (t : ℕ) :
    tm.toNTM.ComputationPath input where
  length := t
  toFun n := tm.runFrom (tm.initCfg input) n
  step n := by
    change tm.toNTM.Step (tm.runFrom (tm.initCfg input) n)
      (tm.runFrom (tm.initCfg input) (n + 1))
    simpa only [runFrom, Function.iterate_succ_apply'] using
      toNTM_step (tm.runFrom (tm.initCfg input) n)
  head_eq := rfl

/-- Every deterministic computation is a nondeterministic one, witnessed by the machine's own
run. -/
theorem toNTM_computes {output : List Symbol} {t s : ℕ}
    (h : tm.ComputesInTimeAndSpace input output t s) :
    tm.toNTM.ComputesInExactTimeAndSpace input output t s :=
  ⟨tm.toNTMComputationPath input t, h.1, h.2.1, rfl, h.2.2⟩

end MultiTapeTM

end Turing
