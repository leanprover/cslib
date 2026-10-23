/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Computability.Machines.RAM.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Field.ZMod

/-!
# RAM examples

Small addition fragments exercise words, exact reals, and finite fields without fixing a
standard arithmetic basis. The same routine computes its address, doubles a memory cell,
and halts in six instructions. Halts and faults are absorbing, as in the Turing-machine API.
-/

namespace CslibTests.RAM

open Cslib.RAM.Typed

inductive Primitive where
  | increment
  | add

abbrev signature {S : Type} (s : ValueSort S) : Signature S where
  operations := ⟨Primitive, fun op => match op with | .increment => 1 | .add => 2⟩
  input op _ := match op with | .increment => .word | .add => s
  output op := match op with | .increment => .word | .add => s
  tests := ⟨Unit, fun _ => 1⟩
  testInput _ _ := s

abbrev additionModel {S : Type} (Carrier : S → Type) (s : ValueSort S)
    (add : (w : Nat) → Value Carrier w s → Value Carrier w s → Option (Value Carrier w s))
    (isZero : (w : Nat) → Value Carrier w s → Option Bool) : Model (signature s) where
  Carrier := Carrier
  operation w op args := match op with
    | .increment =>
      if h : (args 0).val + 1 < 2 ^ w then some ⟨(args 0).val + 1, h⟩ else none
    | .add => add w (args 0) (args 1)
  test w _ args := isZero w (args 0)

abbrev words : Model (signature (S := Empty) .word) :=
  additionModel (fun s => nomatch s) .word
    (fun w x y => if h : x.val + y.val < 2 ^ w then some ⟨x.val + y.val, h⟩ else none)
    (fun _ x => some (decide (x.val = 0)))

abbrev fieldModel (K : Type) [Field K] [DecidableEq K] :
    Model (signature (S := Unit) (.data ())) :=
  additionModel (fun _ => K) (.data ()) (fun _ x y => some (x + y))
    (fun _ x => some (decide (x = 0)))

noncomputable abbrev reals := fieldModel ℝ

abbrev finiteField (p : Nat) [Fact p.Prime] := fieldModel (ZMod p)

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

def doubleCell {S : Type} (s : ValueSort S) : Program (signature s) 2 :=
  [.op (.word 0 0), .op (.apply .increment 0 ![0]), .op (.load s 1 0),
   .op (.apply .add 1 ![1, 1]), .op (.store s 0 1), .halt]

def initial {S : Type} [DecidableEq S] (Carrier : S → Type)
    (zero : (s : ValueSort S) → Value Carrier 3 s) (s : ValueSort S)
    (v : Value Carrier 3 s) : Data Carrier 3 2 :=
  (⟨fun t _ => zero t, fun t _ => zero t⟩ : Data Carrier 3 2).write s 1 v

def wordInitial (v : Fin 8) : Data words.Carrier 3 2 :=
  initial words.Carrier (fun s => match s with | .word => 0 | .data e => nomatch e) .word v

def fieldInitial (K : Type) [Field K] (v : K) : Data (fun _ : Unit => K) 3 2 :=
  initial (fun _ : Unit => K) (fun s => match s with | .word => 0 | .data _ => 0) (.data ()) v

-- One program, interpreted over words, finite fields, and exact reals.
example : (runFrom words 3 (doubleCell .word)
    ⟨0, wordInitial 3, .running⟩ 6).data.mem .word 1 = 6 := by decide

example : (runFrom (finiteField 5) 3 (doubleCell (.data ()))
    ⟨0, fieldInitial (ZMod 5) 3, .running⟩ 6).data.mem (.data ()) 1 = 1 := by decide

example (x : ℝ) : (runFrom reals 3 (doubleCell (.data ()))
    ⟨0, fieldInitial ℝ x, .running⟩ 6).data.mem (.data ()) 1 = x + x := by
  simp [runFrom, Function.iterate_succ_apply', step, doubleCell, Op.eval, fieldInitial, initial,
    Instr.eval, Data.set, Data.write, Function.update]

-- Five steps reach the halt instruction; the sixth executes it. Extra steps are padding.
example : (runFrom words 3 (doubleCell .word) ⟨0, wordInitial 3, .running⟩ 5).Running := by decide
example : (runFrom words 3 (doubleCell .word) ⟨0, wordInitial 3, .running⟩ 6).Halted := by decide
example : (runFrom words 3 (doubleCell .word) ⟨0, wordInitial 3, .running⟩ 100).Halted := by
  have h : (runFrom words 3 (doubleCell .word) ⟨0, wordInitial 3, .running⟩ 6).Halted := by
    decide
  rw [runFrom_eq_of_halt (by decide : 6 ≤ 100) h]
  exact h

-- Overflow faults and preserves the instruction pointer at the failed addition.
example : (runFrom words 3 (doubleCell .word) ⟨0, wordInitial 4, .running⟩ 6).Faulted := by decide
example : (runFrom words 3 (doubleCell .word) ⟨0, wordInitial 4, .running⟩ 6).pc = 3 := by decide

-- Branch failure is distinct from false; an invalid target faults on the next fetch.
def branchProgram : Program (signature (S := Unit) (.data ())) 2 :=
  [.branch () ![0] 3, .halt]

example : runFrom (finiteField 5) 3 branchProgram ⟨0, fieldInitial (ZMod 5) 0, .running⟩ 2 =
    ⟨3, fieldInitial (ZMod 5) 0, .faulted⟩ := rfl

example : runFrom { finiteField 5 with test := fun _ _ _ => some false } 3 branchProgram
    ⟨0, fieldInitial (ZMod 5) 1, .running⟩ 2 = ⟨1, fieldInitial (ZMod 5) 1, .halted⟩ := rfl

example : runFrom { finiteField 5 with test := fun _ _ _ => none } 3 branchProgram
    ⟨0, fieldInitial (ZMod 5) 1, .running⟩ 2 = ⟨0, fieldInitial (ZMod 5) 1, .faulted⟩ := rfl

-- Terminal configurations remain fixed even when their instruction pointer is invalid.
example (data : Data words.Carrier 3 2) :
    runFrom words 3 [] ⟨42, data, .halted⟩ 10 = ⟨42, data, .halted⟩ := by
  exact Function.iterate_fixed
    (step_of_halt (M := words) (p := []) (cfg := ⟨42, data, .halted⟩) rfl) 10

example (data : Data words.Carrier 3 2) :
    runFrom words 3 [] ⟨42, data, .faulted⟩ 10 = ⟨42, data, .faulted⟩ := by
  exact Function.iterate_fixed
    (step_of_fault (M := words) (p := []) (cfg := ⟨42, data, .faulted⟩) rfl) 10

-- Zero width still has one address; literals are checked rather than silently truncated.
def zeroWidth : Cfg words.Carrier 0 1 :=
  { pc := 0
    data.regs := fun s _ => match s with | .word => 0 | .data e => nomatch e
    data.mem := fun s _ => match s with | .word => 0 | .data e => nomatch e }

example : (runFrom words 0 [.op (.word 0 0), .halt] zeroWidth 2).Halted := by decide
example : (runFrom words 0 [.op (.word 0 1), .halt] zeroWidth 2).Faulted := by decide

-- The same finite-path API as Turing machines, with iteration giving its endpoint.
example (cfg : Cfg words.Carrier 3 2) (t : Nat) :
    (RunPath.ofDeterministic words 3 (doubleCell .word) cfg t).last =
      runFrom words 3 (doubleCell .word) cfg t := rfl

end CslibTests.RAM
