/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
module

public import Cslib.Computability.Urm.Config
public import Mathlib.Logic.Relation
public import Mathlib.Data.Part
public import Mathlib.Data.Setoid.Basic

/-! # URM Execution Semantics

Single-step and multi-step execution semantics for URMs.

## Main definitions

- `Urm.Step`: Single-step execution relation
- `Urm.Steps`: Multi-step execution (reflexive-transitive closure of `Step`)
- `Urm.Halts`: A program halts on given inputs
- `Urm.Diverges`: A program diverges on given inputs
- `Urm.HaltsWithResult`: A program halts on given inputs with a specific result

## Notation (scoped to `Urm` namespace)

Standard computability theory notation:
- `p ↓ inputs` — program `p` halts on inputs
- `p ↑ inputs` — program `p` diverges on inputs
- `p ↓ inputs ≫ result` — program `p` halts on inputs with result in R[0]

## Main statements

- `Step.deterministic`: The step relation is deterministic
- `Step.no_step_of_halted`: Halted configurations have no successor
- `haltsWithResult_iff_eval`: `p ↓ inputs ≫ result ↔ eval p inputs = Part.some result`
-/

@[expose] public section

namespace Cslib.Urm

variable (p : Program)

/-- Single-step execution relation for URMs.

Each constructor corresponds to one of the four instruction types:
- `zero`: Execute `Z n` (set register n to 0)
- `succ`: Execute `S n` (increment register n)
- `trans`: Execute `T m n` (copy register m to register n)
- `jump_eq`: Execute `J m n q` when registers m and n are equal (jump to q)
- `jump_ne`: Execute `J m n q` when registers m and n differ (proceed to next)
-/
@[grind]
inductive Step : Config → Config → Prop where
  | zero {c : Config} {n : ℕ}
      (h : p[c.pc]? = some (Instr.Z n)) :
      Step c ⟨c.pc + 1, c.state.write n 0⟩
  | succ {c : Config} {n : ℕ}
      (h : p[c.pc]? = some (Instr.S n)) :
      Step c ⟨c.pc + 1, c.state.write n (c.state.read n + 1)⟩
  | trans {c : Config} {m n : ℕ}
      (h : p[c.pc]? = some (Instr.T m n)) :
      Step c ⟨c.pc + 1, c.state.write n (c.state.read m)⟩
  | jump_eq {c : Config} {m n q : ℕ}
      (h : p[c.pc]? = some (Instr.J m n q))
      (heq : c.state.read m = c.state.read n) :
      Step c ⟨q, c.state⟩
  | jump_ne {c : Config} {m n q : ℕ}
      (h : p[c.pc]? = some (Instr.J m n q))
      (hne : c.state.read m ≠ c.state.read n) :
      Step c ⟨c.pc + 1, c.state⟩

/-- Multi-step execution: the reflexive-transitive closure of `Step`. -/
abbrev Steps : Config → Config → Prop := Relation.ReflTransGen (Step p)

namespace Step

variable {p : Program}

/-- The step relation is deterministic: each configuration has at most one successor. -/
theorem deterministic {c c' c'' : Config} (h1 : Step p c c') (h2 : Step p c c'') : c' = c'' := by
  cases h1 <;> cases h2 <;> grind

/-- A halted configuration has no successor in the step relation. -/
theorem no_step_of_halted {c c' : Config} (hhalted : c.is_halted p) : ¬Step p c c' := by
  intro hstep
  cases hstep <;> grind [Config.is_halted]

/-- A single step preserves registers not written to by the current instruction.

This is a fundamental property of URM execution: each instruction modifies at most
one register (Z, S, T write to one register; J writes to none). -/
theorem preserves_register {c c' : Config} {r : ℕ}
    (hstep : Step p c c')
    (hr : ∀ instr, p[c.pc]? = some instr → instr.writes_to ≠ some r) :
    c'.state.read r = c.state.read r := by
  cases hstep with
  | zero hinstr | succ hinstr | trans hinstr =>
    have := hr _ hinstr
    simp only [Instr.writes_to, ne_eq, Option.some.injEq] at this
    exact Function.update_of_ne (Ne.symm this) _ _
  | jump_eq _ _ | jump_ne _ _ => rfl

end Step

namespace Steps

variable {p : Program}

/-- Steps compose transitively. -/
theorem trans {c₁ c₂ c₃ : Config} (h1 : Steps p c₁ c₂) (h2 : Steps p c₂ c₃) : Steps p c₁ c₃ :=
  Relation.ReflTransGen.trans h1 h2

/-- One step implies multi-step. -/
theorem single {c c' : Config} (h : Step p c c') : Steps p c c' :=
  Relation.ReflTransGen.single h

/-- Zero steps: reflexivity. -/
theorem refl (c : Config) : Steps p c c :=
  Relation.ReflTransGen.refl

/-- Multi-step execution preserves registers not written by any executed instruction. -/
theorem preserves_register {c c' : Config} {r : ℕ}
    (hsteps : Steps p c c')
    (hr : ∀ instr, instr ∈ p → instr.writes_to ≠ some r) :
    c'.state.read r = c.state.read r := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head hstep _ ih =>
    rw [ih]
    exact Step.preserves_register hstep fun instr hinstr =>
      hr instr (List.mem_of_getElem? hinstr)

/-- If two halted configurations are reachable from the same start, they are equal.

This follows from the determinism of `Step`: any two execution paths from the same
initial configuration must be prefixes of each other (or identical if both terminate). -/
theorem eq_of_halts {init c₁ c₂ : Config}
    (h1 : Steps p init c₁) (hh1 : c₁.is_halted p)
    (h2 : Steps p init c₂) (hh2 : c₂.is_halted p) : c₁ = c₂ := by
  induction h1 using Relation.ReflTransGen.head_induction_on with
  | refl =>
    -- c₁ = init, so init is halted
    -- By no_step_of_halted, init cannot step, so h2 must also be refl
    cases h2 using Relation.ReflTransGen.head_induction_on with
    | refl => rfl
    | head hstep _ => exact absurd hstep (Step.no_step_of_halted hh1)
  | head hstep_c hrest ih =>
    -- init → c → ... → c₁, where hstep_c : Step p init c
    -- init is not halted (it can step)
    cases h2 using Relation.ReflTransGen.head_induction_on with
    | refl =>
      -- c₂ = init is halted, but init can step - contradiction
      exact absurd hstep_c (Step.no_step_of_halted hh2)
    | head hstep_c' hrest' =>
      -- init → c' → ... → c₂
      -- By determinism, c = c'
      have heq : _ = _ := Step.deterministic hstep_c hstep_c'
      subst heq
      exact ih hrest'

end Steps

/-- A program halts on given inputs if there exists a halted configuration reachable from
the initial configuration. -/
def Halts (inputs : List ℕ) : Prop :=
  ∃ c, Steps p (Config.init inputs) c ∧ c.is_halted p

/-- A program diverges on given inputs if it does not halt. -/
def Diverges (inputs : List ℕ) : Prop := ¬Halts p inputs

/-- A program halts on given inputs with a specific result in R[0]. -/
def HaltsWithResult (inputs : List ℕ) (result : ℕ) : Prop :=
  ∃ c, Steps p (Config.init inputs) c ∧ c.is_halted p ∧ c.state.output = result

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
  let ⟨c, hsteps, hhalted, _⟩ := h
  ⟨c, hsteps, hhalted⟩

end HaltsWithResult

namespace Halts

variable {p : Program}

/-- If a program halts, it halts with the output of the final configuration. -/
theorem toHaltsWithResult {inputs : List ℕ} (h : p ↓ inputs) :
    p ↓ inputs ≫ (Classical.choose h).state.output :=
  let c := Classical.choose h
  let ⟨hsteps, hhalted⟩ := Classical.choose_spec h
  ⟨c, hsteps, hhalted, rfl⟩

end Halts

/-- Evaluation as a partial function using `Part`.
Defined when the program halts, returning the value in register 0. -/
noncomputable def eval (inputs : List ℕ) : Part ℕ :=
  ⟨Halts p inputs, fun h => (Classical.choose h).state.output⟩

/-- A program halts with result `a` iff evaluation returns `Part.some a`. -/
theorem haltsWithResult_iff_eval {inputs : List ℕ} {result : ℕ} :
    p ↓ inputs ≫ result ↔ eval p inputs = Part.some result := by
  rw [Part.eq_some_iff]
  constructor
  · intro ⟨c, hsteps, hhalted, hresult⟩
    -- Show result ∈ eval p inputs
    refine ⟨⟨c, hsteps, hhalted⟩, ?_⟩
    -- Need to show (eval p inputs).get _ = result
    simp only [eval]
    have hhalts : Halts p inputs := ⟨c, hsteps, hhalted⟩
    have heq : Classical.choose hhalts = c :=
      Steps.eq_of_halts (Classical.choose_spec hhalts).1 (Classical.choose_spec hhalts).2
        hsteps hhalted
    simp [heq, hresult]
  · intro ⟨hdom, hget⟩
    -- hdom is exactly Halts p inputs by definition of eval
    let c := Classical.choose hdom
    have hspec := Classical.choose_spec hdom
    exact ⟨c, hspec.1, hspec.2, hget⟩

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

end Cslib.Urm

end
