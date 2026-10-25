/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Signature
public import Mathlib.Order.RelSeries
public import Mathlib.Logic.Function.Basic

/-!
# RAMs with words and additional data sorts

Programs use a typed signature independently of its interpretation and the runtime word width.
Every sort has a finite register bank and word-addressed memory. Addresses come from word
registers, even when the memory contains real numbers or field elements. Taking no additional
sorts gives a word RAM; additional sorts can carry exact reals, finite fields, or other data.

Words are `Fin (2 ^ w)`, so operations must return a word of the configured width. The
interpretation chooses checked or wrapping arithmetic and any explicit conversions between
sorts. Nullary operations supply data constants. Operations and tests may fail; a failed test
is distinct from a false test. Control labels are natural numbers, independent of word width.

The execution interface follows CSLib's Turing-machine development: configurations record
execution status, terminal configurations are fixed points of `step`, and `runFrom` iterates
that function. Finite runs are `RelSeries` paths. A halt instruction takes one step; paths may
then include terminal self-loops, so their lengths give time bounds rather than first-halting
times. Faults remain distinct from successful halts and retain the failing instruction pointer
and data. Interpretations may be noncomputable. Input encodings and bit-cost simulations are
separate developments.

## Scope and connections to other machines

Unlike `Cslib.URM`, which has unbounded natural-number registers and halts when its
instruction pointer leaves the program, this model distinguishes an explicit halt from
an invalid fetch. A simulation must translate that termination convention. Unbounded
natural-number data with zero, successor, and equality can express the URM instructions;
the simulation and its input/output conventions are not part of this core.

A word-only machine at a fixed width has finite data storage. Studying arbitrary input
sizes requires an explicit width policy. Width-independent program syntax alone does not
establish uniformity: operation symbols, their interpretations, and input/output encodings
must also be effective for classical computability results. Exact-real interpretations need
not meet these requirements. Program coding and a universal interpreter are separate
constructions; a stored-program architecture is not a prerequisite for defining semantics.

The common register count is a capacity for each sort; finitely many banks with different
requirements can use a common upper bound and leave excess registers unused. Memory banks
likewise share a word address space, without requiring that every cell be used. Word literals
are natural numbers so one program can run at different widths; a literal that does not fit
faults at evaluation.

The finite-register instruction semantics are adapted from the `GenericRAM` and `WordRAM`
developments in complexitylib2 by Erik Demaine and Samuel Schlesinger, originating in the
[MIT–ULB lean-trominoes project](https://github.com/edemaine/lean-trominoes).
The separation of words and real data follows Erickson, van der Hoog, and Miltzow,
[*Smoothing the Gap Between NP and ER*, §6.1](https://jeffe.cs.illinois.edu/pubs/pdf/realram.pdf).
This core leaves their particular arithmetic instruction set to an interpretation.
-/

@[expose] public section

namespace Cslib.RAM.Typed

/-- A distinguished word sort and an optional collection of additional data sorts. -/
inductive ValueSort (S : Type) where
  | word
  | data (sort : S)
  deriving DecidableEq

/-- Values at word width `w`; only the word sort is fixed by the machine. -/
abbrev Value {S : Type} (D : S → Type) (w : Nat) : ValueSort S → Type
  | .word => Fin (2 ^ w)
  | .data s => D s

/-- Operation and test symbols, with the sorts of their arguments and results. -/
structure Signature (S : Type) where
  /-- The operation symbols and their arities, including nullary constants. -/
  operations : Circuits.Signature
  /-- The sort of each operation argument. -/
  input : (op : operations.Op) → Fin (operations.Arity op) → ValueSort S
  /-- The result sort of each operation. -/
  output : operations.Op → ValueSort S
  /-- The test symbols and their arities. -/
  tests : Circuits.Signature
  /-- The sort of each test argument. -/
  testInput : (test : tests.Op) → Fin (tests.Arity test) → ValueSort S

/-- A partial interpretation of a signature, for every runtime word width. -/
structure Model {S : Type} (σ : Signature S) where
  /-- The carriers of the additional data sorts. -/
  D : S → Type
  /-- Primitive operations; `none` signals a fault. -/
  operation : (w : Nat) → (op : σ.operations.Op) →
    ((i : Fin (σ.operations.Arity op)) → Value D w (σ.input op i)) →
      Option (Value D w (σ.output op))
  /-- Primitive tests; `none` signals a fault, independently of the Boolean result. -/
  test : (w : Nat) → (test : σ.tests.Op) →
    ((i : Fin (σ.tests.Arity test)) → Value D w (σ.testInput test i)) → Option Bool

variable {S : Type} {σ : Signature S} {D : S → Type} {w r : Nat}

/-- Registers and memory, with a separate bank for each sort. -/
@[ext]
structure Data (D : S → Type) (w r : Nat) where
  /-- The `r` registers of each sort. -/
  regs : (s : ValueSort S) → Fin r → Value D w s
  /-- Each memory bank is indexed by machine words. -/
  mem : (s : ValueSort S) → Fin (2 ^ w) → Value D w s

/-- Update one register. -/
def Data.set [DecidableEq S] (x : Data D w r)
    (s : ValueSort S) (i : Fin r) (v : Value D w s) : Data D w r :=
  { x with regs := Function.update x.regs s (Function.update (x.regs s) i v) }

/-- Update one memory cell. -/
def Data.write [DecidableEq S] (x : Data D w r)
    (s : ValueSort S) (a : Fin (2 ^ w)) (v : Value D w s) : Data D w r :=
  { x with mem := Function.update x.mem s (Function.update (x.mem s) a v) }

section Updates

variable [DecidableEq S] (x : Data D w r) (s t : ValueSort S)

@[simp]
theorem Data.set_regs (i : Fin r) (v : Value D w s) : (x.set s i v).regs s i = v := by
  simp [Data.set]

@[simp]
theorem Data.set_regs_ne (i j : Fin r) (v : Value D w s) (h : j ≠ i) :
    (x.set s i v).regs s j = x.regs s j := by
  simp [Data.set, h]

@[simp]
theorem Data.set_regs_sort_ne (i j : Fin r) (v : Value D w s) (h : t ≠ s) :
    (x.set s i v).regs t j = x.regs t j := by
  simp [Data.set, h]

@[simp]
theorem Data.set_regs_index_ne (i j : Fin r) (v : Value D w s) (h : j ≠ i) :
    (x.set s i v).regs t j = x.regs t j := by
  by_cases hs : t = s
  · subst t; exact x.set_regs_ne s i j v h
  · exact x.set_regs_sort_ne s t i j v hs

@[simp]
theorem Data.set_mem (i : Fin r) (v : Value D w s) : (x.set s i v).mem = x.mem := rfl

@[simp]
theorem Data.write_mem (a : Fin (2 ^ w)) (v : Value D w s) :
    (x.write s a v).mem s a = v := by
  simp [Data.write]

@[simp]
theorem Data.write_mem_ne (a b : Fin (2 ^ w)) (v : Value D w s) (h : b ≠ a) :
    (x.write s a v).mem s b = x.mem s b := by
  simp [Data.write, h]

@[simp]
theorem Data.write_mem_sort_ne (a b : Fin (2 ^ w)) (v : Value D w s) (h : t ≠ s) :
    (x.write s a v).mem t b = x.mem t b := by
  simp [Data.write, h]

@[simp]
theorem Data.write_regs (a : Fin (2 ^ w)) (v : Value D w s) :
    (x.write s a v).regs = x.regs := rfl

end Updates

/-- Data instructions. A load or store obtains its address from a word register. -/
inductive DataInstr (σ : Signature S) (r : Nat) where
  | word (dst : Fin r) (literal : Nat)
  | copy (sort : ValueSort S) (dst src : Fin r)
  | apply (op : σ.operations.Op) (dst : Fin r) (args : Fin (σ.operations.Arity op) → Fin r)
  | load (sort : ValueSort S) (dst address : Fin r)
  | store (sort : ValueSort S) (address src : Fin r)

/-- Instructions of a flat program. Jump targets are instruction indices. -/
inductive Instr (σ : Signature S) (r : Nat) where
  | op (instruction : DataInstr σ r)
  | jump (target : Nat)
  | branch (test : σ.tests.Op) (args : Fin (σ.tests.Arity test) → Fin r) (target : Nat)
  | halt

/-- Program syntax does not depend on the carriers or word width. -/
abbrev Program (σ : Signature S) (r : Nat) := List (Instr σ r)

/-- Execution status, distinguishing successful termination from a fault. -/
inductive Status where
  | running
  | halted
  | faulted
  deriving DecidableEq

/-- A machine configuration, retaining its instruction pointer and data after termination. -/
structure Cfg (D : S → Type) (w r : Nat) where
  /-- The current instruction index. -/
  pc : Nat
  /-- The current registers and memory. -/
  data : Data D w r
  /-- Initially running; halts and faults are absorbing. -/
  status : Status := .running

/-- The configuration has successfully halted. -/
abbrev Cfg.Halted (cfg : Cfg D w r) : Prop := cfg.status = .halted

/-- The configuration has faulted. -/
abbrev Cfg.Faulted (cfg : Cfg D w r) : Prop := cfg.status = .faulted

/-- The configuration can execute an instruction. -/
abbrev Cfg.Running (cfg : Cfg D w r) : Prop := cfg.status = .running

variable [DecidableEq S]

/-- Evaluate a data instruction; word literals must fit rather than wrap. -/
def DataInstr.eval (M : Model σ) (w : Nat) : DataInstr σ r → Data M.D w r →
    Option (Data M.D w r)
  | .word d n, x => if h : n < 2 ^ w then some (x.set .word d ⟨n, h⟩) else none
  | .copy s d i, x => some (x.set s d (x.regs s i))
  | .apply op d args, x =>
      (M.operation w op (fun i => x.regs (σ.input op i) (args i))).map (x.set (σ.output op) d)
  | .load s d a, x => some (x.set s d (x.mem s (x.regs .word a)))
  | .store s a i, x => some (x.write s (x.regs .word a) (x.regs s i))

/-- Evaluate an instruction on a running configuration, independently of fetching. -/
def Instr.eval (M : Model σ) (w : Nat) (instruction : Instr σ r)
    (cfg : Cfg M.D w r) : Cfg M.D w r :=
  match instruction with
  | .op dataOp =>
      match dataOp.eval M w cfg.data with
      | none => { cfg with status := .faulted }
      | some data => ⟨cfg.pc + 1, data, .running⟩
  | .jump pc => ⟨pc, cfg.data, .running⟩
  | .branch test args pc =>
      match M.test w test (fun i => cfg.data.regs (σ.testInput test i) (args i)) with
      | none => { cfg with status := .faulted }
      | some b => ⟨if b then pc else cfg.pc + 1, cfg.data, .running⟩
  | .halt => { cfg with status := .halted }

/-- Execute one instruction, fixing terminal configurations. Invalid instruction indices fault. -/
def step (M : Model σ) (w : Nat) (p : Program σ r) (cfg : Cfg M.D w r) :
    Cfg M.D w r :=
  match cfg.status with
  | .halted | .faulted => cfg
  | .running =>
      match p[cfg.pc]? with
      | none => { cfg with status := .faulted }
      | some instruction => instruction.eval M w cfg

/-- The deterministic transition relation, including terminal self-loops. -/
def Step (M : Model σ) (w : Nat) (p : Program σ r)
    (cfg cfg' : Cfg M.D w r) : Prop := step M w p cfg = cfg'

/-- The step relation as a `SetRel`, following the Turing-machine API. -/
abbrev stepRel (M : Model σ) (w : Nat) (p : Program σ r) :
    SetRel (Cfg M.D w r) (Cfg M.D w r) := {(cfg, cfg') | Step M w p cfg cfg'}

/-- Steps whose source configuration is still running. -/
abbrev runningStepRel (M : Model σ) (w : Nat) (p : Program σ r) :
    SetRel (Cfg M.D w r) (Cfg M.D w r) :=
  {(cfg, cfg') | cfg.Running ∧ Step M w p cfg cfg'}

/-- A finite execution path, allowing padding after a halt or fault. -/
abbrev RunPath (M : Model σ) (w : Nat) (p : Program σ r) := RelSeries (stepRel M w p)

variable {M : Model σ} {p : Program σ r}

@[simp]
theorem step_iff {cfg cfg' : Cfg M.D w r} :
    Step M w p cfg cfg' ↔ step M w p cfg = cfg' := Iff.rfl

@[simp]
theorem step_of_halt {cfg : Cfg M.D w r} (h : cfg.status = .halted) :
    step M w p cfg = cfg := by simp [step, h]

@[simp]
theorem step_of_fault {cfg : Cfg M.D w r} (h : cfg.status = .faulted) :
    step M w p cfg = cfg := by simp [step, h]

/-- An invalid fetch faults only a running configuration, preserving its pointer and data. -/
theorem step_of_pc_ge {cfg : Cfg M.D w r} (hrun : cfg.status = .running)
    (hpc : p.length ≤ cfg.pc) :
    step M w p cfg = { cfg with status := .faulted } := by
  simp [step, hrun, List.getElem?_eq_none hpc]

/-- The configuration after `t` steps; extra steps leave terminal configurations unchanged. -/
def runFrom (M : Model σ) (w : Nat) (p : Program σ r)
    (cfg : Cfg M.D w r) (t : Nat) : Cfg M.D w r := (step M w p)^[t] cfg

@[simp]
theorem runFrom_zero (cfg : Cfg M.D w r) : runFrom M w p cfg 0 = cfg := rfl

@[simp]
theorem runFrom_succ (cfg : Cfg M.D w r) (t : Nat) :
    runFrom M w p cfg (t + 1) = step M w p (runFrom M w p cfg t) :=
  Function.iterate_succ_apply' ..

/-- Execute a prefix and then resume from its final configuration. -/
theorem runFrom_add (cfg : Cfg M.D w r) (s t : Nat) :
    runFrom M w p cfg (s + t) = runFrom M w p (runFrom M w p cfg s) t := by
  simpa only [runFrom, Nat.add_comm s t] using
    Function.iterate_add_apply (step M w p) t s cfg

/-- Extra time preserves a successful halt. -/
theorem runFrom_eq_of_halt {cfg : Cfg M.D w r} {s t : Nat} (hst : s ≤ t)
    (h : (runFrom M w p cfg s).Halted) : runFrom M w p cfg t = runFrom M w p cfg s := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hst
  rw [runFrom_add]
  exact Function.iterate_fixed (step_of_halt h) t

/-- Extra time preserves a fault, without converting it into a successful halt. -/
theorem runFrom_eq_of_fault {cfg : Cfg M.D w r} {s t : Nat} (hst : s ≤ t)
    (h : (runFrom M w p cfg s).Faulted) : runFrom M w p cfg t = runFrom M w p cfg s := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hst
  rw [runFrom_add]
  exact Function.iterate_fixed (step_of_fault h) t

/-- The duration of a run path, including any terminal padding. -/
def RunPath.time (path : RunPath M w p) : Nat := path.length

/-- The canonical path of `t` steps from a configuration. -/
def RunPath.ofDeterministic (M : Model σ) (w : Nat) (p : Program σ r)
    (cfg : Cfg M.D w r) (t : Nat) : RunPath M w p where
  length := t
  toFun n := runFrom M w p cfg n.val
  step n := by simp [stepRel, Step, runFrom_succ]

/-- Every run path is the canonical path from its head for its duration. -/
theorem RunPath.eq_ofDeterministic (path : RunPath M w p) :
    path = .ofDeterministic M w p path.head path.time := by
  refine RelSeries.ext rfl ?_
  change path.toFun = fun i => (step M w p)^[i.val] path.head
  refine funext (Fin.induction rfl fun i ih => ?_)
  simpa [Function.iterate_succ_apply'] using
    (step_iff.mp (path.step i)).symm.trans (congrArg (step M w p) ih)

@[simp]
theorem RunPath.head_ofDeterministic (cfg : Cfg M.D w r) (t : Nat) :
    (ofDeterministic M w p cfg t).head = cfg := rfl

@[simp]
theorem RunPath.last_ofDeterministic (cfg : Cfg M.D w r) (t : Nat) :
    (ofDeterministic M w p cfg t).last = runFrom M w p cfg t := rfl

/-- A path's endpoint agrees with iteration of the step function. -/
theorem RunPath.last_eq_runFrom (path : RunPath M w p) :
    path.last = runFrom M w p path.head path.time := by
  conv_lhs => rw [path.eq_ofDeterministic]
  rfl

end Cslib.RAM.Typed
