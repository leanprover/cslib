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
theorem Step.of_nonJump {p : Program} {c : Config} (hlt : c.pc < p.length)
    (hnonjump : ¬(p[c.pc]'hlt).IsJump) :
    ∃ c', Step p c c' ∧ c'.pc = c.pc + 1 := by
  have hinstr : p[c.pc]? = some p[c.pc] := List.getElem?_eq_getElem hlt
  cases hp : (p[c.pc]'hlt) with
  | Z n => exact ⟨_, Step.zero (hp ▸ hinstr), rfl⟩
  | S n => exact ⟨_, Step.succ (hp ▸ hinstr), rfl⟩
  | T m n => exact ⟨_, Step.transfer (hp ▸ hinstr), rfl⟩
  | J _ _ _ => exact False.elim (hnonjump (hp ▸ trivial))

/-- Straight-line programs halt from any starting state, not just Config.init.
Useful for chaining: after running one program, we can run the next
straight-line segment from whatever state we're in. -/
theorem straight_line_halts_from_state {p : Program} (hsl : p.IsStraightLine) (s : State) :
    ∃ c, Steps p ⟨0, s⟩ c ∧ c.isHalted p ∧ c.pc = p.length := by
  suffices h : ∀ c : Config, c.pc ≤ p.length → ∃ c', Steps p c c' ∧ c'.pc = p.length by
    obtain ⟨c', hsteps, hpc'⟩ := h ⟨0, s⟩ (Nat.zero_le _)
    exact ⟨c', hsteps, Nat.le_of_eq hpc'.symm, hpc'⟩
  intro c hpc_le
  generalize hrem : p.length - c.pc = remaining
  induction remaining using Nat.strong_induction_on generalizing c with
  | _ remaining ih =>
    by_cases hhalted : c.pc ≥ p.length
    · exact ⟨c, Relation.ReflTransGen.refl, by omega⟩
    · push_neg at hhalted
      have hnonjump := hsl p[c.pc] (List.getElem_mem hhalted)
      obtain ⟨c', hstep', hpc'⟩ := Step.of_nonJump hhalted hnonjump
      obtain ⟨c'', hsteps'', hpc''⟩ := ih (p.length - c'.pc) (by omega) c' (by omega) rfl
      exact ⟨c'', Relation.ReflTransGen.head hstep' hsteps'', hpc''⟩

/-- A straight-line program halts on any input. -/
theorem straight_line_halts {p : Program} (hsl : p.IsStraightLine) (inputs : List ℕ) :
    Halts p inputs := by
  obtain ⟨c, hsteps, hhalted, _⟩ := straight_line_halts_from_state hsl (State.ofInputs inputs)
  exact ⟨c, hsteps, hhalted⟩

/-- The halting configuration for a straight-line program starting from state s.
Wraps Classical.choose to hide it from the API. -/
noncomputable def straightLine_finalConfig {p : Program}
    (hsl : p.IsStraightLine) (s : State) : Config :=
  Classical.choose (straight_line_halts_from_state hsl s)

/-- Specification: the config from straightLine_finalConfig satisfies Steps, isHalted,
and has pc = p.length. -/
theorem straightLine_finalConfig_spec {p : Program} (hsl : p.IsStraightLine) (s : State) :
    let c := straightLine_finalConfig hsl s
    Steps p ⟨0, s⟩ c ∧ c.isHalted p ∧ c.pc = p.length :=
  Classical.choose_spec (straight_line_halts_from_state hsl s)

/-- The final state after running a straight-line program from a given starting state. -/
noncomputable def straightLine_finalState {p : Program}
    (hsl : p.IsStraightLine) (s : State) : State :=
  (straightLine_finalConfig hsl s).state

/-- For a straight-line program, c.state equals straightLine_finalState if halted from s. -/
theorem straightLine_finalState_eq_of_halted {p : Program} (hsl : p.IsStraightLine)
    (s : State) (c : Config) (hsteps : Steps p ⟨0, s⟩ c) (hhalted : c.isHalted p) :
    c.state = straightLine_finalState hsl s :=
  Steps.eq_of_halts hsteps hhalted (straightLine_finalConfig_spec hsl s).1
    (straightLine_finalConfig_spec hsl s).2.1 ▸ rfl

/-- In a straight-line program, we can characterize the state at any intermediate pc.
This gives us the configuration after executing instructions 0..pc-1. -/
theorem straight_line_state_at_pc {p : Program} (hsl : p.IsStraightLine)
    (s : State) (targetPc : ℕ) (htarget : targetPc ≤ p.length) :
    ∃ c, Steps p ⟨0, s⟩ c ∧ c.pc = targetPc := by
  induction targetPc with
  | zero => exact ⟨⟨0, s⟩, Relation.ReflTransGen.refl, rfl⟩
  | succ n ih =>
    obtain ⟨c_n, hsteps_n, hpc_n⟩ := ih (Nat.le_of_succ_le htarget)
    have hn_lt : n < p.length := Nat.lt_of_succ_le htarget
    have hpc_lt : c_n.pc < p.length := hpc_n ▸ hn_lt
    have hnonjump := hsl p[c_n.pc] (List.getElem_mem hpc_lt)
    obtain ⟨c', hstep', hpc'⟩ := Step.of_nonJump hpc_lt hnonjump
    exact ⟨c', Relation.ReflTransGen.tail hsteps_n hstep', hpc_n ▸ hpc'⟩

end Cslib.URM

end
