/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
module

public import Cslib.Computability.Urm.Execution

/-! # URM-Computable Functions

This file defines the notion of URM-computability for partial functions on natural numbers.

## Main definitions

- `Urm.Computes`: A program computes a given partial function.
- `Urm.Computable`: A partial function is URM-computable if there exists a URM program that
  computes it.
-/

@[expose] public section

namespace Cslib.Urm

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
private theorem single_instr_eval {instr : Instr} {inputs : List ℕ} {finalState : State}
    (hstep : Step [instr] (Config.init inputs) ⟨1, finalState⟩) :
    eval [instr] inputs = Part.some finalState.output := by
  have h_final_halted : (⟨1, finalState⟩ : Config).is_halted [instr] := by simp
  apply Part.ext'
  · simp only [eval, Part.some_dom, iff_true]
    exact ⟨⟨1, finalState⟩, Steps.single hstep, h_final_halted⟩
  · intro hHalts _
    obtain ⟨hsteps, hhalted⟩ := Classical.choose_spec hHalts
    have heq := Steps.eq_of_halts hsteps hhalted (Steps.single hstep) h_final_halted
    simp only [eval, heq, Part.get_some]

/-- The successor function `S(x) = x + 1` is URM-computable.

Program: `[S 0]` - increment register 0 and halt. -/
theorem succ_computable : Computable 1 (fun inputs => Part.some (inputs 0 + 1)) := by
  use [Instr.S 0]
  intro inputs
  rw [single_instr_eval (Step.succ (p := [Instr.S 0]) rfl)]
  simp [State.output, State.write, State.read, Config.init, State.of_inputs]

/-- General projection function `Uₖⁿ(x₀, ..., xₙ₋₁) = xₖ` is URM-computable.

Program: `[T k 0]` - copy register k to register 0. -/
theorem proj_computable (n : ℕ) (k : Fin n) :
    Computable n (fun inputs => Part.some (inputs k)) := by
  use [Instr.T k 0]
  intro inputs
  rw [single_instr_eval (Step.trans (p := [Instr.T k 0]) rfl)]
  simp [State.output, State.write, State.read, Config.init, State.of_inputs, k.isLt]

/-- The identity/projection function `U₁¹(x) = x` is URM-computable.

This is a special case of `proj_computable` with n = 1 and k = 0. -/
theorem id_computable : Computable 1 (fun inputs => Part.some (inputs 0)) :=
  proj_computable 1 0

end Computable

end Cslib.Urm

end
