/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
module

public import Cslib.Computability.URM.Execution

/-! # URM-Computable Functions

This file defines the notion of URM-computability for partial functions on natural numbers.

## Main definitions

- `URM.Computes`: A program computes a given partial function.
- `URM.Computable`: A partial function is URM-computable if there exists a URM program that
  computes it.
-/

@[expose] public section

namespace Cslib.URM

/-- A program `p` computes a partial function `f : (Fin n → ℕ) → Part ℕ` if for any input,
`eval p inputs = f inputs` as partial values. This captures both:
- The program halts iff the function is defined on that input
- When both are defined, the program's output equals the function's value

Note: Inputs are provided in registers 0, 1, ..., n-1 and output is read from register 0. -/
def Computes (n : ℕ) (p : Program) (f : (Fin n → ℕ) → Part ℕ) : Prop :=
  ∀ inputs : Fin n → ℕ, eval p (List.ofFn inputs) = f inputs

/-- A partial function `f : (Fin n → ℕ) → Part ℕ` is URM-computable if there exists a URM program
that computes it. -/
def Computable (n : ℕ) (f : (Fin n → ℕ) → Part ℕ) : Prop :=
  ∃ p : Program, Computes n p f

namespace Computable

/-- Helper for single-instruction programs: proves eval equals a given value. -/
private theorem single_instr_eval {instr : Instr} {inputs : List ℕ} {finalRegs : Regs}
    (hstep : Step [instr] (State.init inputs) ⟨1, finalRegs⟩) :
    eval [instr] inputs = Part.some finalRegs.output := by
  have h_final_halted : (⟨1, finalRegs⟩ : State).isHalted [instr] := by simp
  apply Part.ext'
  · simp only [eval, Part.map_Dom, Part.some_dom, iff_true]
    exact ⟨⟨1, finalRegs⟩, Steps.single hstep, h_final_halted⟩
  · intro hHalts _
    have ⟨hsteps, hhalted⟩ := evalState_spec [instr] hHalts
    have heq := Steps.eq_of_halts hsteps hhalted (Steps.single hstep) h_final_halted
    simp only [eval, Part.map_get, Function.comp_apply, heq, Part.get_some]

/-- The successor function `S(x) = x + 1` is URM-computable.

Program: `[S 0]` - increment register 0 and halt. -/
theorem succ_computable : Computable 1 (fun inputs => Part.some (inputs 0 + 1)) := by
  use [Instr.S 0]
  intro inputs
  rw [single_instr_eval (Step.succ (p := [Instr.S 0]) rfl)]
  simp [Regs.output, Regs.write, Regs.read, State.init, Regs.ofInputs]

/-- General projection function `Uₖⁿ(x₀, ..., xₙ₋₁) = xₖ` is URM-computable.

Program: `[T k 0]` - copy register k to register 0. -/
theorem proj_computable (n : ℕ) (k : Fin n) :
    Computable n (fun inputs => Part.some (inputs k)) := by
  use [Instr.T k 0]
  intro inputs
  rw [single_instr_eval (Step.transfer (p := [Instr.T k 0]) rfl)]
  simp [Regs.output, Regs.write, Regs.read, State.init, Regs.ofInputs, k.isLt]

/-- The identity/projection function `U₁¹(x) = x` is URM-computable.

This is a special case of `proj_computable` with n = 1 and k = 0. -/
theorem id_computable : Computable 1 (fun inputs => Part.some (inputs 0)) :=
  proj_computable 1 0

end Computable

end Cslib.URM

end
