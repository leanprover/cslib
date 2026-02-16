/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
module

public import Cslib.Computability.URM.Basic
public import Cslib.Foundations.Data.Relation
public import Mathlib.Data.Part
public import Mathlib.Data.Setoid.Basic

/-! # URM Execution Semantics

Single-step and multi-step execution semantics for URMs.

## Main definitions

- `URM.Step`: Single-step execution relation
- `URM.Steps`: Multi-step execution (reflexive-transitive closure of `Step`)
- `URM.Halts`: A program halts on given inputs
- `URM.Diverges`: A program diverges on given inputs
- `URM.HaltsWithResult`: A program halts on given inputs with a specific result

Bridge lemmas:
- `isHalted_iff_normal`: `s.isHalted p ↔ Relation.Normal (Step p) s`
- `halts_iff_normalizable`: `Halts p inputs ↔ Relation.Normalizable (Step p) (State.init inputs)`
- `step_confluent`: The step relation is confluent (follows from determinism)

## Notation (scoped to `URM` namespace)

Standard computability theory notation:
- `p ↓ inputs` — program `p` halts on inputs
- `p ↑ inputs` — program `p` diverges on inputs
- `p ↓ inputs ≫ result` — program `p` halts on inputs with result in R[0]

## Main results

- `Step.deterministic`: The step relation is deterministic
- `step_confluent`: The step relation is confluent (from determinism)
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

/-- Multi-step execution: the reflexive-transitive closure of `Step`. -/
abbrev Steps : State → State → Prop := Relation.ReflTransGen (Step p)

namespace Step

variable {p : Program}

/-- The step relation is deterministic: each state has at most one successor. -/
theorem deterministic {s s' s'' : State} (h1 : Step p s s') (h2 : Step p s s'') : s' = s'' := by
  grind

/-- A halted state has no successor in the step relation. -/
theorem no_step_of_halted {s s' : State} (hhalted : s.isHalted p) : ¬Step p s s' := by
  grind [State.isHalted]

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

/-! ### Step Properties -/

/-- A state is halted iff it is normal (has no successor) in the reduction system. -/
theorem isHalted_iff_normal {p : Program} {s : State} :
    s.isHalted p ↔ Relation.Normal (Step p) s := by
  constructor
  · intro hhalted ⟨s', hstep⟩
    exact Step.no_step_of_halted hhalted hstep
  · intro hnormal
    -- If not halted, then p[s.pc]? = some instr for some instruction
    by_contra hnothalted
    simp only [State.isHalted, not_le] at hnothalted
    have hlt : s.pc < p.length := hnothalted
    have hinstr : p[s.pc]? = some p[s.pc] := List.getElem?_eq_getElem hlt
    -- Any instruction can step, contradicting hnormal
    cases hp : p[s.pc] with
    | Z n => exact hnormal ⟨_, Step.zero (hp ▸ hinstr)⟩
    | S n => exact hnormal ⟨_, Step.succ (hp ▸ hinstr)⟩
    | T m n => exact hnormal ⟨_, Step.transfer (hp ▸ hinstr)⟩
    | J m n q =>
      by_cases heq : s.regs.read m = s.regs.read n
      · exact hnormal ⟨_, Step.jump_eq (hp ▸ hinstr) heq⟩
      · exact hnormal ⟨_, Step.jump_ne (hp ▸ hinstr) heq⟩

/-- The step relation is confluent.

For a deterministic relation, any two execution paths from the same state must follow
the same sequence of steps, so if both reach some state, they reach the same state.
We prove this directly rather than via Diamond since Diamond requires the relation
to always have successors. -/
theorem step_confluent (p : Program) : Relation.Confluent (Step p) := by
  intro init s₁ s₂ h1 h2
  -- Two multi-step reductions from init must follow the same path due to determinism
  induction h1 using Relation.ReflTransGen.head_induction_on generalizing s₂ with
  | refl =>
    -- s₁ = init, so s₂ is reachable from s₁
    exact ⟨s₂, h2, Relation.ReflTransGen.refl⟩
  | head hstep_a hrest_a ih =>
    -- init → a → ... → s₁
    cases h2 using Relation.ReflTransGen.head_induction_on with
    | refl =>
      -- s₂ = init, so s₁ is reachable from s₂
      exact ⟨s₁, Relation.ReflTransGen.refl, Relation.ReflTransGen.head hstep_a hrest_a⟩
    | head hstep_b hrest_b =>
      -- init → b → ... → s₂
      -- By determinism, a = b
      have heq := Step.deterministic hstep_a hstep_b
      subst heq
      -- Now both paths go through the same intermediate state
      exact ih hrest_b

namespace Steps

variable {p : Program}

/-- Multi-step execution preserves registers not written by any executed instruction. -/
theorem preserves_register {s s' : State} {r : ℕ}
    (hsteps : Steps p s s')
    (hr : ∀ instr, instr ∈ p → instr.writesTo ≠ some r) :
    s'.regs.read r = s.regs.read r := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head => grind [Step.preserves_register]

/-- If two halted states are reachable from the same start, they are equal.

This follows from confluence: since `Step p` is confluent and both `s₁` and `s₂`
are normal forms reachable from `init`, they must be equal. -/
theorem eq_of_halts {init s₁ s₂ : State}
    (h1 : Steps p init s₁) (hh1 : s₁.isHalted p)
    (h2 : Steps p init s₂) (hh2 : s₂.isHalted p) : s₁ = s₂ := by
  -- Use confluence: both s₁ and s₂ are reachable from init, so they're joinable
  have ⟨w, hw1, hw2⟩ := step_confluent p h1 h2
  -- But s₁ and s₂ are normal forms, so w must equal both
  have hn1 := isHalted_iff_normal.mp hh1
  have hn2 := isHalted_iff_normal.mp hh2
  grind

end Steps

/-- A program halts on given inputs if execution reaches a halted state.

This is equivalent to `(Step p).Normalizable (State.init inputs)` —
see `halts_iff_normalizable`. -/
def Halts (inputs : List ℕ) : Prop :=
  ∃ s, Steps p (State.init inputs) s ∧ s.isHalted p

/-- Halting is equivalent to normalizability in the reduction system. -/
theorem halts_iff_normalizable {p : Program} {inputs : List ℕ} :
    Halts p inputs ↔ Relation.Normalizable (Step p) (State.init inputs) := by
  grind [Halts, isHalted_iff_normal]

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
instance : Setoid Program := Setoid.mk _ ProgramEquiv.equivalence

end Cslib.URM

end
