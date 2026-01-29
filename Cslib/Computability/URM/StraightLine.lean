/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
module

public import Cslib.Computability.URM.Execution

/-! # Straight-Line Programs

This file defines straight-line programs (those without jumps) and proves
they always halt exactly at their length.

## Main definitions

- `Program.IsStraightLine`: a program contains no jump instructions

## Main results

- `straight_line_halts`: straight-line programs always halt
- `straightLine_finalState`: final state after running a straight-line program
-/

@[expose] public section

namespace Cslib.URM

/-! ## Straight-Line Programs -/

/-- A program is "straight-line" if it contains no jump instructions. -/
def Program.IsStraightLine (p : Program) : Prop :=
  ∀ i ∈ p, ¬i.IsJump

instance (p : Program) : Decidable p.IsStraightLine :=
  inferInstanceAs (Decidable (∀ i ∈ p, ¬i.IsJump))

/-- Append preserves straight-line property. -/
theorem Program.IsStraightLine.append {p q : Program}
    (hp : p.IsStraightLine) (hq : q.IsStraightLine) :
    (p ++ q).IsStraightLine := by
  intro i hi
  simp only [List.mem_append] at hi
  rcases hi with hi | hi <;> [exact hp i hi; exact hq i hi]

/-- Cons of non-jumping instruction preserves straight-line. -/
theorem Program.IsStraightLine.cons {instr : Instr} {p : Program}
    (hinstr : ¬instr.IsJump) (hp : p.IsStraightLine) :
    Program.IsStraightLine (instr :: p) := by
  intro i hi
  simp only [List.mem_cons] at hi
  rcases hi with rfl | hi <;> [exact hinstr; exact hp i hi]

/-- Singleton non-jumping instruction is straight-line. -/
theorem Program.IsStraightLine.singleton {instr : Instr}
    (h : ¬instr.IsJump) : Program.IsStraightLine [instr] := by
  intro i hi
  simp only [List.mem_singleton] at hi
  exact hi ▸ h

/-! ## Straight-Line Program Execution -/

/-- A non-jumping instruction produces a step that increments PC by 1. -/
theorem Step.of_nonJump {p : Program} {s : State} (hlt : s.pc < p.length)
    (hnonjump : ¬(p[s.pc]'hlt).IsJump) :
    ∃ s', Step p s s' ∧ s'.pc = s.pc + 1 := by
  have hinstr : p[s.pc]? = some p[s.pc] := List.getElem?_eq_getElem hlt
  cases hp : (p[s.pc]'hlt) with
  | Z n => exact ⟨_, Step.zero (hp ▸ hinstr), rfl⟩
  | S n => exact ⟨_, Step.succ (hp ▸ hinstr), rfl⟩
  | T m n => exact ⟨_, Step.transfer (hp ▸ hinstr), rfl⟩
  | J _ _ _ => exact False.elim (hnonjump (hp ▸ trivial))

/-- Straight-line programs halt from any starting registers, not just State.init.
Useful for chaining: after running one program, we can run the next
straight-line segment from whatever registers we're in. -/
theorem straight_line_halts_from_regs {p : Program} (hsl : p.IsStraightLine) (r : Regs) :
    ∃ s, Steps p ⟨0, r⟩ s ∧ s.isHalted p ∧ s.pc = p.length := by
  suffices h : ∀ s : State, s.pc ≤ p.length → ∃ s', Steps p s s' ∧ s'.pc = p.length by
    obtain ⟨s', hsteps, hpc'⟩ := h ⟨0, r⟩ (Nat.zero_le _)
    exact ⟨s', hsteps, Nat.le_of_eq hpc'.symm, hpc'⟩
  intro s hpc_le
  generalize hrem : p.length - s.pc = remaining
  induction remaining using Nat.strong_induction_on generalizing s with
  | _ remaining ih =>
    by_cases hhalted : s.pc ≥ p.length
    · exact ⟨s, Relation.ReflTransGen.refl, by omega⟩
    · push_neg at hhalted
      have hnonjump := hsl p[s.pc] (List.getElem_mem hhalted)
      obtain ⟨s', hstep', hpc'⟩ := Step.of_nonJump hhalted hnonjump
      obtain ⟨s'', hsteps'', hpc''⟩ := ih (p.length - s'.pc) (by omega) s' (by omega) rfl
      exact ⟨s'', Relation.ReflTransGen.head hstep' hsteps'', hpc''⟩

/-- A straight-line program halts on any input. -/
theorem straight_line_halts {p : Program} (hsl : p.IsStraightLine) (inputs : List ℕ) :
    Halts p inputs := by
  obtain ⟨s, hsteps, hhalted, _⟩ := straight_line_halts_from_regs hsl (Regs.ofInputs inputs)
  exact ⟨s, hsteps, hhalted⟩

/-- The halting state for a straight-line program starting from registers r.
Wraps Classical.choose to hide it from the API. -/
noncomputable def straightLine_finalState {p : Program}
    (hsl : p.IsStraightLine) (r : Regs) : State :=
  Classical.choose (straight_line_halts_from_regs hsl r)

/-- Specification: the state from straightLine_finalState satisfies Steps, isHalted,
and has pc = p.length. -/
theorem straightLine_finalState_spec {p : Program} (hsl : p.IsStraightLine) (r : Regs) :
    let s := straightLine_finalState hsl r
    Steps p ⟨0, r⟩ s ∧ s.isHalted p ∧ s.pc = p.length :=
  Classical.choose_spec (straight_line_halts_from_regs hsl r)

/-- The final registers after running a straight-line program from given starting registers. -/
noncomputable def straightLine_finalRegs {p : Program}
    (hsl : p.IsStraightLine) (r : Regs) : Regs :=
  (straightLine_finalState hsl r).regs

/-- For a straight-line program, s.regs equals straightLine_finalRegs if halted from r. -/
theorem straightLine_finalRegs_eq_of_halted {p : Program} (hsl : p.IsStraightLine)
    (r : Regs) (s : State) (hsteps : Steps p ⟨0, r⟩ s) (hhalted : s.isHalted p) :
    s.regs = straightLine_finalRegs hsl r :=
  Steps.eq_of_halts hsteps hhalted (straightLine_finalState_spec hsl r).1
    (straightLine_finalState_spec hsl r).2.1 ▸ rfl

/-- In a straight-line program, we can characterize the state at any intermediate pc.
This gives us the state after executing instructions 0..pc-1. -/
theorem straight_line_state_at_pc {p : Program} (hsl : p.IsStraightLine)
    (r : Regs) (targetPc : ℕ) (htarget : targetPc ≤ p.length) :
    ∃ s, Steps p ⟨0, r⟩ s ∧ s.pc = targetPc := by
  induction targetPc with
  | zero => exact ⟨⟨0, r⟩, Relation.ReflTransGen.refl, rfl⟩
  | succ n ih =>
    obtain ⟨s_n, hsteps_n, hpc_n⟩ := ih (Nat.le_of_succ_le htarget)
    have hn_lt : n < p.length := Nat.lt_of_succ_le htarget
    have hpc_lt : s_n.pc < p.length := hpc_n ▸ hn_lt
    have hnonjump := hsl p[s_n.pc] (List.getElem_mem hpc_lt)
    obtain ⟨s', hstep', hpc'⟩ := Step.of_nonJump hpc_lt hnonjump
    exact ⟨s', Relation.ReflTransGen.tail hsteps_n hstep', hpc_n ▸ hpc'⟩

end Cslib.URM

end
