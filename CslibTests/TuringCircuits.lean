/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Computability.Circuit.Boolean.TuringMachine

/-!
# Turing-machine to circuit automation tests

Polynomial-time hypotheses compose with the circuit closure API on ordinary list functions.
-/

namespace CslibTests.TuringCircuits

open Cslib Cslib.Complexity Cslib.Circuits.Boolean Turing

example {f : BitString → BitString} (hf : FP f) : FPPoly f := by fun_prop

example {f : BitString → Bool} (hf : P f) : PPoly f := by fun_prop

-- A concrete machine emits the first input bit, if present, and immediately halts.
private def firstBitTM : MultiTapeTM 0 Bool Unit :=
  MultiTapeTM.ofTr () (fun _ bit _ => ⟨0, Fin.elim0, bit, none⟩)

private theorem firstBitTM_computes :
    firstBitTM.ComputesFunInTimeAndSpace (Function.Embedding.refl _) (Function.Embedding.refl _)
      (fun x => x.take 1) (fun _ => 1) (fun _ => 0) := by
  intro x
  have hhalt : (firstBitTM.runFrom (firstBitTM.initCfg x) 1).Halted := by
    change (firstBitTM.step _).state = none
    rw [MultiTapeTM.step_of_state rfl]
    simp [firstBitTM, Action.apply]
  refine ⟨⟨1, hhalt, ?_⟩, ?_, by simp⟩
  · change (firstBitTM.step (firstBitTM.initCfg x)).output = x.take 1
    rw [MultiTapeTM.step_of_state rfl]
    simp only [firstBitTM, MultiTapeTM.tr_ofTr, Action.apply_output, MultiTapeNTM.initCfg,
      Cfg.init, List.nil_append, Cfg.inputSymbol_eq_getElem?]
    cases x <;> rfl
  · simpa using MultiTapeTM.runsInTime_of_halted hhalt

example : FPPoly (fun x => x.take 1) := by
  have h := firstBitTM_computes
  fun_prop

-- A machine's verified running-time bound suffices; no circuit witness is supplied.
example {k : ℕ} {State : Type} [Finite State] (tm : MultiTapeTM k Bool State)
    {f : BitString → BitString} {s : BitString → ℕ}
    (h : tm.ComputesFunInTimeAndSpace (Function.Embedding.refl _) (Function.Embedding.refl _) f
      (fun x => x.length ^ 2 + 3 * x.length + 1) s) : FPPoly f := by fun_prop

-- A bound stated through any polynomially bounded function of the length is accepted too.
example {k : ℕ} {State : Type} [Finite State] (tm : MultiTapeTM k Bool State)
    {f : BitString → BitString} {time : ℕ → ℕ} {space : BitString → ℕ}
    (h : tm.ComputesFunInTimeAndSpace (Function.Embedding.refl _) (Function.Embedding.refl _) f
      (fun x => time x.length) space) (ht : PolynomiallyBounded time) : FPPoly f := by fun_prop

example {f : BitString → BitString} (hf : FP f) :
    FPPoly (fun x => (f (x.map not)).reverse ++ x.map not) := by fun_prop

example {f : BitString → BitString} {g : BitString → Bool} (hf : FP f) (hg : P g) :
    PPoly (fun x => g (f x ++ x.reverse) && (f x).any id) := by fun_prop

end CslibTests.TuringCircuits
