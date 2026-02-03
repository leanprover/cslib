/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
module

public import Cslib.Computability.URM.Basic
public import Mathlib.Logic.Relation
public import Mathlib.Data.Part
public import Mathlib.Data.Setoid.Basic
public import Cslib.Foundations.Semantics.ReductionSystem.Basic

/-! # URM Execution Semantics

Single-step and multi-step execution semantics for URMs.

## Main definitions

- `URM.Step`: Single-step execution relation
- `URM.Steps`: Multi-step execution (reflexive-transitive closure of `Step`)
- `URM.Halts`: A program halts on given inputs
- `URM.Diverges`: A program diverges on given inputs
- `URM.HaltsWithResult`: A program halts on given inputs with a specific result

## Notation (scoped to `URM` namespace)

Standard computability theory notation:
- `p ↓ inputs` — program `p` halts on inputs
- `p ↑ inputs` — program `p` diverges on inputs
- `p ↓ inputs ≫ result` — program `p` halts on inputs with result in R[0]

Reduction system notation (aligned with CSLib's `ReductionSystem`):
- `s ⭢ᵉ s'` — single-step execution (`Step p s s'`)
- `s ↠ᵉ s'` — multi-step execution (`Steps p s s'`)

## Main statements

- `Step.deterministic`: The step relation is deterministic
- `Step.no_step_of_halted`: Halted configurations have no successor
- `haltsWithResult_iff_eval`: `p ↓ inputs ≫ result ↔ eval p inputs = Part.some result`
-/

@[expose] public section

namespace Cslib.URM

variable (p : Program)

/-- Single-step execution relation for URMs.

Each constructor corresponds to one of the four instruction types:
- `zero`: Execute `Z n` (set register n to 0)
- `succ`: Execute `S n` (increment register n)
- `transfer`: Execute `T m n` (copy register m to register n)
- `jump_eq`: Execute `J m n q` when registers m and n are equal (jump to q)
- `jump_ne`: Execute `J m n q` when registers m and n differ (proceed to next)
-/
@[grind]
inductive Step : State → State → Prop where
  | zero {s : State} {n : ℕ}
      (h : p[s.pc]? = some (Instr.Z n)) :
      Step s ⟨s.pc + 1, s.regs.write n 0⟩
  | succ {s : State} {n : ℕ}
      (h : p[s.pc]? = some (Instr.S n)) :
      Step s ⟨s.pc + 1, s.regs.write n (s.regs.read n + 1)⟩
  | transfer {s : State} {m n : ℕ}
      (h : p[s.pc]? = some (Instr.T m n)) :
      Step s ⟨s.pc + 1, s.regs.write n (s.regs.read m)⟩
  | jump_eq {s : State} {m n q : ℕ}
      (h : p[s.pc]? = some (Instr.J m n q))
      (heq : s.regs.read m = s.regs.read n) :
      Step s ⟨q, s.regs⟩
  | jump_ne {s : State} {m n q : ℕ}
      (h : p[s.pc]? = some (Instr.J m n q))
      (hne : s.regs.read m ≠ s.regs.read n) :
      Step s ⟨s.pc + 1, s.regs⟩

/-- ReductionSystem for URM execution, parameterized by program. -/
def stepRs : ReductionSystem State := ⟨Step p⟩

/-- Multi-step execution: the reflexive-transitive closure of `Step`. -/
abbrev Steps : State → State → Prop := Relation.ReflTransGen (Step p)

/-- Notation for single-step reduction: `s ⭢ᵉ s'` means `Step p s s'`. -/
scoped notation3:39 s:39 " ⭢ᵉ " s':39 => Step _ s s'
/-- Notation for multi-step reduction: `s ↠ᵉ s'` means `Steps p s s'`. -/
scoped notation3:39 s:39 " ↠ᵉ " s':39 => Steps _ s s'

namespace Step

variable {p : Program}

/-- The step relation is deterministic: each state has at most one successor. -/
theorem deterministic {s s' s'' : State} (h1 : Step p s s') (h2 : Step p s s'') : s' = s'' := by
  cases h1 <;> cases h2 <;> grind

/-- A halted state has no successor in the step relation. -/
theorem no_step_of_halted {s s' : State} (hhalted : s.isHalted p) : ¬Step p s s' := by
  intro hstep
  cases hstep <;> grind [State.isHalted]

/-- A single step preserves registers not written to by the current instruction.

This is a fundamental property of URM execution: each instruction modifies at most
one register (Z, S, T write to one register; J writes to none). -/
theorem preserves_register {s s' : State} {r : ℕ}
    (hstep : Step p s s')
    (hr : ∀ instr, p[s.pc]? = some instr → instr.writesTo ≠ some r) :
    s'.regs.read r = s.regs.read r := by
  cases hstep with
  | zero hinstr | succ hinstr | transfer hinstr =>
    have := hr _ hinstr
    simp only [Instr.writesTo, ne_eq, Option.some.injEq] at this
    exact Function.update_of_ne (Ne.symm this) _ _
  | jump_eq _ _ | jump_ne _ _ => rfl

end Step

namespace Steps

variable {p : Program}

/-- Steps compose transitively. -/
theorem trans {s₁ s₂ s₃ : State} (h1 : Steps p s₁ s₂) (h2 : Steps p s₂ s₃) : Steps p s₁ s₃ :=
  Relation.ReflTransGen.trans h1 h2

/-- One step implies multi-step. -/
theorem single {s s' : State} (h : Step p s s') : Steps p s s' :=
  Relation.ReflTransGen.single h

/-- Zero steps: reflexivity. -/
theorem refl (s : State) : Steps p s s :=
  Relation.ReflTransGen.refl

/-- Multi-step execution preserves registers not written by any executed instruction. -/
theorem preserves_register {s s' : State} {r : ℕ}
    (hsteps : Steps p s s')
    (hr : ∀ instr, instr ∈ p → instr.writesTo ≠ some r) :
    s'.regs.read r = s.regs.read r := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head hstep _ ih =>
    rw [ih]
    exact Step.preserves_register hstep fun instr hinstr =>
      hr instr (List.mem_of_getElem? hinstr)

/-- If two halted states are reachable from the same start, they are equal.

This follows from the determinism of `Step`: any two execution paths from the same
initial state must be prefixes of each other (or identical if both terminate). -/
theorem eq_of_halts {init s₁ s₂ : State}
    (h1 : Steps p init s₁) (hh1 : s₁.isHalted p)
    (h2 : Steps p init s₂) (hh2 : s₂.isHalted p) : s₁ = s₂ := by
  induction h1 using Relation.ReflTransGen.head_induction_on with
  | refl =>
    -- s₁ = init, so init is halted
    -- By no_step_of_halted, init cannot step, so h2 must also be refl
    cases h2 using Relation.ReflTransGen.head_induction_on with
    | refl => rfl
    | head hstep _ => exact absurd hstep (Step.no_step_of_halted hh1)
  | head hstep_s hrest ih =>
    -- init → s → ... → s₁, where hstep_s : Step p init s
    -- init is not halted (it can step)
    cases h2 using Relation.ReflTransGen.head_induction_on with
    | refl =>
      -- s₂ = init is halted, but init can step - contradiction
      exact absurd hstep_s (Step.no_step_of_halted hh2)
    | head hstep_s' hrest' =>
      -- init → s' → ... → s₂
      -- By determinism, s = s'
      have heq : _ = _ := Step.deterministic hstep_s hstep_s'
      subst heq
      exact ih hrest'

end Steps

/-- A program halts on given inputs if there exists a halted state reachable from
the initial state. -/
def Halts (inputs : List ℕ) : Prop :=
  ∃ s, Steps p (State.init inputs) s ∧ s.isHalted p

/-- A program diverges on given inputs if it does not halt. -/
def Diverges (inputs : List ℕ) : Prop := ¬Halts p inputs

/-- A program halts on given inputs with a specific result in R[0]. -/
def HaltsWithResult (inputs : List ℕ) (result : ℕ) : Prop :=
  ∃ s, Steps p (State.init inputs) s ∧ s.isHalted p ∧ s.regs.output = result

/-- Notation for halting: `p ↓ inputs` means program `p` halts on `inputs`. -/
scoped notation:50 p " ↓ " inputs:51 => Halts p inputs
/-- Notation for divergence: `p ↑ inputs` means program `p` diverges on `inputs`. -/
scoped notation:50 p " ↑ " inputs:51 => Diverges p inputs
/-- Notation for halting with result: `p ↓ inputs ≫ result` means program `p` halts on `inputs`
with `result` in R[0]. -/
scoped notation:50 p " ↓ " inputs:51 " ≫ " result:51 => HaltsWithResult p inputs result

namespace HaltsWithResult

variable {p : Program}

/-- If a program halts with a result, it halts. -/
theorem toHalts {inputs : List ℕ} {result : ℕ}
    (h : p ↓ inputs ≫ result) : p ↓ inputs :=
  let ⟨s, hsteps, hhalted, _⟩ := h
  ⟨s, hsteps, hhalted⟩

end HaltsWithResult

/-- Evaluation returning the full halting state. -/
noncomputable def evalState (inputs : List ℕ) : Part State :=
  ⟨Halts p inputs, fun h => Classical.choose h⟩

/-- Specification: the state from evalState satisfies Steps and isHalted. -/
theorem evalState_spec {inputs : List ℕ} (h : (evalState p inputs).Dom) :
    let s := (evalState p inputs).get h
    Steps p (State.init inputs) s ∧ s.isHalted p :=
  Classical.choose_spec h

namespace Halts

variable {p : Program}

/-- If a program halts, it halts with the output of the final state. -/
theorem toHaltsWithResult {inputs : List ℕ} (h : p ↓ inputs) :
    p ↓ inputs ≫ ((evalState p inputs).get h).regs.output :=
  let s := (evalState p inputs).get h
  let ⟨hsteps, hhalted⟩ := evalState_spec p h
  ⟨s, hsteps, hhalted, rfl⟩

end Halts

/-- Evaluation as a partial function using `Part`.
Defined when the program halts, returning the value in register 0. -/
noncomputable def eval (inputs : List ℕ) : Part ℕ :=
  (evalState p inputs).map (·.regs.output)

/-- A program halts with result `a` iff evaluation returns `Part.some a`. -/
theorem haltsWithResult_iff_eval {inputs : List ℕ} {result : ℕ} :
    p ↓ inputs ≫ result ↔ eval p inputs = Part.some result := by
  rw [Part.eq_some_iff, eval, Part.mem_map_iff]
  constructor
  · intro ⟨s, hsteps, hhalted, hresult⟩
    have hhalts : Halts p inputs := ⟨s, hsteps, hhalted⟩
    have heq : (evalState p inputs).get hhalts = s :=
      Steps.eq_of_halts (evalState_spec p hhalts).1 (evalState_spec p hhalts).2 hsteps hhalted
    exact ⟨(evalState p inputs).get hhalts, Part.get_mem hhalts, heq ▸ hresult⟩
  · intro ⟨s, hs_mem, hresult⟩
    rw [Part.mem_eq] at hs_mem
    obtain ⟨hdom, hget⟩ := hs_mem
    have hspec := evalState_spec p hdom
    exact ⟨s, hget ▸ hspec.1, hget ▸ hspec.2, hresult⟩

/-- Two programs are equivalent if they produce the same result for all inputs. -/
def ProgramEquiv (p q : Program) : Prop :=
  ∀ inputs : List ℕ, eval p inputs = eval q inputs

/-- Program equivalence is an equivalence relation. -/
theorem ProgramEquiv.equivalence : Equivalence ProgramEquiv where
  refl := fun _ _ => rfl
  symm := fun h inputs => (h inputs).symm
  trans := fun h₁ h₂ inputs => (h₁ inputs).trans (h₂ inputs)

/-- Setoid instance for programs, enabling the ≈ notation. -/
instance : Setoid Program where
  r := ProgramEquiv
  iseqv := ProgramEquiv.equivalence

/-- Equivalence is reflexive. -/
theorem ProgramEquiv.refl (p : Program) : p ≈ p := Setoid.refl p

/-- Equivalence is symmetric. -/
theorem ProgramEquiv.symm {p q : Program} (h : p ≈ q) : q ≈ p := Setoid.symm h

/-- Equivalence is transitive. -/
theorem ProgramEquiv.trans {p q r : Program} (h₁ : p ≈ q) (h₂ : q ≈ r) : p ≈ r :=
  Setoid.trans h₁ h₂

end Cslib.URM

end
