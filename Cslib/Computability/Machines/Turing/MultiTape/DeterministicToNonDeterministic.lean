/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.NonDeterministic

/-!
# Deterministic Multi-Tape Turing Machines are Nondeterministic

Embeds `MultiTapeTM` into `MultiTapeNTM` and shows the embedding preserves computation.

`toNTM` relates a situation to exactly the transition `tr` prescribes: nondeterminism is the
possibility of several, so having exactly one is the special case. Every step of `tm` is then a
transition of `tm.toNTM.lts` (`toNTM_lts_tr`), and `run` assembles those steps into a
`MultiTapeNTM.Computation` — the machine's own run, valid by construction.

What remains is to read the four measures off that run. Both models idle once the machine has
halted, so `run` reaches exactly `t` steps for every `t` and the measures match `configs`,
`outputString` and `spaceUsed` on the nose, with no reasoning about halting times.

## Important Declarations

* `MultiTapeTM.toNTM`: every deterministic machine is a nondeterministic one
* `MultiTapeTM.run`: the machine's own run, as a computation of its nondeterministic reading
* `MultiTapeTM.toNTM_computes`: every deterministic computation is a nondeterministic one
-/

@[expose] public section

open Cslib

namespace Turing

variable {k : ℕ} {State Symbol : Type*} {input : List Symbol}

/-- Every deterministic machine is a nondeterministic one whose relation is a singleton. -/
def MultiTapeTM.toNTM (tm : MultiTapeTM k Symbol State) : MultiTapeNTM k Symbol State where
  q₀ := tm.q₀
  Tr q input work out := out = tm.tr q input work

namespace MultiTapeTM

variable {tm : MultiTapeTM k Symbol State}

@[simp]
lemma toNTM_initCfg (tm : MultiTapeTM k Symbol State) (input : List Symbol) :
    tm.toNTM.initCfg input = tm.initCfg input := rfl

/-- Each step of `tm` is a transition of `tm.toNTM.lts`, labelled by the symbol `tm` emits. This
holds at a halted configuration too, where both models idle. -/
theorem toNTM_lts_tr (c : Cfg k Symbol State input) :
    (tm.toNTM.lts input).Tr c (tm.outputSymbol c) (tm.step c) := by
  cases hq : c.state with
  | none => simp [MultiTapeNTM.lts, hq]
  | some q => simp [MultiTapeNTM.lts, toNTM, outputSymbol, step, hq]

/-- The run of `tm` from `c` for `t` steps, as a computation of `tm.toNTM`. -/
def run (tm : MultiTapeTM k Symbol State) (c : Cfg k Symbol State input) :
    ℕ → tm.toNTM.Computation input c
  | 0 => .nil
  | n + 1 => .cons (tm.outputSymbol c) (toNTM_lts_tr c) (tm.run (tm.step c) n)

@[simp]
lemma run_final (c : Cfg k Symbol State input) (t : ℕ) :
    (tm.run c t).final = tm.configs c t := by
  induction t generalizing c with
  | zero => simp [run, MultiTapeNTM.Computation.final]
  | succ n ih => rw [run, MultiTapeNTM.Computation.final, ih, configs_succ_eq_step]

@[simp]
lemma run_labels (c : Cfg k Symbol State input) (t : ℕ) :
    (tm.run c t).labels = (List.range t).map fun j => tm.outputSymbol (tm.configs c j) := by
  induction t generalizing c with
  | zero => simp [run, MultiTapeNTM.Computation.labels]
  | succ n ih =>
    rw [run, MultiTapeNTM.Computation.labels, ih, List.range_succ_eq_map]
    simp [configs_succ_eq_step]

@[simp]
lemma run_visited (c : Cfg k Symbol State input) (t : ℕ) :
    (tm.run c t).visited = (List.range (t + 1)).map (tm.configs c) := by
  induction t generalizing c with
  | zero => simp [run, MultiTapeNTM.Computation.visited]
  | succ n ih =>
    rw [run, MultiTapeNTM.Computation.visited, ih, List.range_succ_eq_map (n := n + 1)]
    simp [configs_succ_eq_step]

@[simp]
lemma run_halts (c : Cfg k Symbol State input) (t : ℕ) :
    (tm.run c t).Halts ↔ (tm.configs c t).Halted := by
  simp [MultiTapeNTM.Computation.Halts]

@[simp]
lemma run_time (c : Cfg k Symbol State input) (t : ℕ) : (tm.run c t).time = t := by
  simp [MultiTapeNTM.Computation.time]

@[simp]
lemma run_output (c : Cfg k Symbol State input) (t : ℕ) :
    (tm.run c t).output = tm.outputString c t := by
  simp [MultiTapeNTM.Computation.output, outputString]

@[simp]
lemma run_space (c : Cfg k Symbol State input) (t : ℕ) :
    (tm.run c t).space = tm.spaceUsed c t := by
  simp [MultiTapeNTM.Computation.space, spaceUsed_eq_spaceUsedOfCfgs]

/--
Every deterministic computation is a nondeterministic one, witnessed by the machine's own run.
-/
theorem toNTM_computes {output : List Symbol} {t s : ℕ}
    (h : tm.ComputesInTimeAndSpace input output t s) :
    tm.toNTM.ComputesInTimeAndSpace input output t s :=
  ⟨tm.run (tm.initCfg input) t, by simpa using h.1, by simpa using h.2.1, by simp,
    by simpa using h.2.2⟩

end MultiTapeTM

end Turing
