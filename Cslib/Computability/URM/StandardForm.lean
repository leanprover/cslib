/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
module

public import Cslib.Computability.URM.StraightLine

/-! # Standard Form Programs

This file defines standard-form programs (those with bounded jump targets)
and proves their execution properties.

## Main definitions

- `Program.IsStandardForm`: all jump targets are bounded by program length
- `Program.toStandardForm`: convert a program to standard form

## Main results

- `straight_line_IsStandardForm`: straight-line programs are standard form
- `Halts.toStandardForm_iff`: halting equivalence with normalized programs
-/

@[expose] public section

namespace Cslib.URM

/-! ## Standard Form Definitions -/

namespace Program

/-- A program is in standard form if all jump targets are bounded by the program length.
Jumps can target any instruction (0..length-1) or the "virtual halt" position (length). -/
def IsStandardForm (p : Program) : Prop :=
  ∀ instr ∈ p, instr.JumpsBoundedBy p.length

instance (p : Program) : Decidable p.IsStandardForm :=
  inferInstanceAs (Decidable (∀ instr ∈ p, instr.JumpsBoundedBy p.length))

/-- Convert a program to standard form by capping all jump targets at the program length. -/
def toStandardForm (p : Program) : Program :=
  p.map (Instr.capJump p.length)

/-- toStandardForm preserves program length. -/
@[simp]
theorem toStandardForm_length (p : Program) :
    p.toStandardForm.length = p.length := by
  simp [toStandardForm]

/-- toStandardForm produces a standard form program. -/
theorem toStandardForm_isStandardForm (p : Program) :
    p.toStandardForm.IsStandardForm := by
  unfold IsStandardForm toStandardForm
  rw [List.length_map]
  intro instr hinstr
  obtain ⟨orig, _, rfl⟩ := List.mem_map.mp hinstr
  exact Instr.JumpsBoundedBy.capJump p.length orig

/-- Accessing an instruction in toStandardForm gives the capJump'd instruction. -/
theorem getElem?_toStandardForm (p : Program) (i : ℕ) :
    p.toStandardForm[i]? = (p[i]?).map (Instr.capJump p.length) := by
  simp only [toStandardForm, List.getElem?_map]

/-- toStandardForm is idempotent: applying it twice equals applying it once. -/
@[simp]
theorem toStandardForm_idempotent (p : Program) :
    p.toStandardForm.toStandardForm = p.toStandardForm := by
  simp only [toStandardForm, List.length_map, List.map_map]
  congr 1
  funext instr
  exact Instr.capJump_idempotent p.length instr

end Program

/-! ## Standard Form Properties -/

/-- Straight-line programs are in standard form. -/
theorem straight_line_IsStandardForm {p : Program} (hsl : p.IsStraightLine) :
    p.IsStandardForm := by
  intro instr hinstr
  exact Instr.jumpsBoundedBy_of_nonJump (hsl instr hinstr) p.length

/-! ## Behavioral Equivalence

Two programs are behaviorally equivalent if they halt on the same inputs
and produce the same results. We prove that p and p.toStandardForm are
behaviorally equivalent. -/

/-! ### Behavioral Equivalence via Step Correspondence

p and p.toStandardForm differ only for jumps with target q > p.length:
- Original: jumps to q (halted since q ≥ p.length)
- Standard form: jumps to min q p.length = p.length (also halted)
- Both halt with the same state

For all other cases, both programs step identically. -/

/-- Forward step correspondence: if p steps from c to c', then either:
    (1) p.toStandardForm steps from c to c' (same step), or
    (2) c' is halted in p, and p.toStandardForm steps to a config that is also halted
        with the same state (this only happens for jumps with unbounded targets). -/
theorem Step.toStandardForm {p : Program} {c c' : Config} (hstep : Step p c c') :
    Step p.toStandardForm c c' ∨
    (c'.isHalted p ∧ ∃ c₂, Step p.toStandardForm c c₂ ∧
      c₂.isHalted p.toStandardForm ∧ c'.state = c₂.state) := by
  cases hstep with
  | zero hinstr =>
    left
    exact Step.zero (by simp [Program.getElem?_toStandardForm, hinstr])
  | succ hinstr =>
    left
    exact Step.succ (by simp [Program.getElem?_toStandardForm, hinstr])
  | transfer hinstr =>
    left
    exact Step.transfer (by simp [Program.getElem?_toStandardForm, hinstr])
  | @jump_ne m n q hinstr hne =>
    left
    have hcap : p.toStandardForm[c.pc]? = some (Instr.J m n (min q p.length)) := by
      simp [Program.getElem?_toStandardForm, hinstr]
    exact Step.jump_ne hcap hne
  | @jump_eq m n q hinstr heq =>
    have (x : ℕ) (h : min q p.length = x) : p.toStandardForm[c.pc]? = some (Instr.J m n x) := by
      grind [Program.getElem?_toStandardForm, Instr.capJump]
    by_cases q ≤ p.length
    · grind [Step.jump_eq]
    · right
      split_ands
      · grind [Config.isHalted]
      · use ⟨p.length, c.state⟩
        grind [Config.isHalted, Program.toStandardForm_length]

/-- Forward halting: if p reaches a halted config, p.toStandardForm reaches a halted config
    with the same state. -/
theorem Steps.toStandardForm_halts {p : Program} {c c' : Config}
    (hsteps : Steps p c c') (hhalted : c'.isHalted p) :
    ∃ c₂, Steps p.toStandardForm c c₂ ∧
      c₂.isHalted p.toStandardForm ∧ c'.state = c₂.state := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl =>
    refine ⟨c', Steps.refl _, ?_, rfl⟩
    simp only [Config.isHalted, Program.toStandardForm_length]
    exact hhalted
  | head hstep hrest ih =>
    rcases Step.toStandardForm hstep with
      hsame | ⟨hhalted_mid, c_mid, hstep_mid, hhalted_mid', hstate_eq⟩
    · obtain ⟨c₂, hsteps₂, hhalted₂, hstate_eq⟩ := ih
      exact ⟨c₂, Steps.trans (Steps.single hsame) hsteps₂, hhalted₂, hstate_eq⟩
    · grind [(Steps.refl _).eq_of_halts hhalted_mid hrest hhalted]

/-- Forward halting theorem. -/
theorem Halts.toStandardForm {p : Program} {inputs : List ℕ} (h : Halts p inputs) :
    Halts p.toStandardForm inputs := by
  obtain ⟨c, hsteps, hhalted⟩ := h
  obtain ⟨c₂, hsteps₂, hhalted₂, _⟩ := Steps.toStandardForm_halts hsteps hhalted
  exact ⟨c₂, hsteps₂, hhalted₂⟩

/-- Reverse step correspondence: if p.toStandardForm steps from c to c', then either:
    (1) p steps from c to c' (same step), or
    (2) c' is halted in p.toStandardForm, and p steps to a config that is also halted
        with the same state (this only happens for jumps with unbounded targets). -/
theorem Step.from_toStandardForm {p : Program} {c c' : Config}
    (hstep : Step p.toStandardForm c c') :
    Step p c c' ∨
    (c'.isHalted p.toStandardForm ∧ ∃ c₂, Step p c c₂ ∧
      c₂.isHalted p ∧ c'.state = c₂.state) := by
  cases hstep with
  | zero hinstr | succ hinstr | transfer hinstr | jump_ne hinstr _ =>
    left
    rw [Program.getElem?_toStandardForm] at hinstr
    simp only [Option.map_eq_some_iff] at hinstr
    obtain ⟨instr, hinstr', hcap⟩ := hinstr
    cases instr <;> simp only [Instr.capJump] at hcap
    all_goals grind
  | jump_eq hinstr heq =>
    rw [Program.getElem?_toStandardForm] at hinstr
    simp only [Option.map_eq_some_iff] at hinstr
    obtain ⟨instr, hinstr', hcap⟩ := hinstr
    cases instr with
    | Z _ | S _ | T _ _ => simp at hcap
    | J m' n' q' =>
      simp only [Instr.capJump, Instr.J.injEq] at hcap
      obtain ⟨rfl, rfl, htarget⟩ := hcap
      by_cases hbounded : q' ≤ p.length
      · simp only [Nat.min_eq_left hbounded] at htarget
        subst htarget
        left
        grind
      · simp only [Nat.min_eq_right (Nat.le_of_not_le hbounded)] at htarget
        subst htarget
        right
        refine ⟨?_, ⟨q', c.state⟩, Step.jump_eq hinstr' heq, ?_, rfl⟩
        · grind [Config.isHalted, Program.toStandardForm_length]
        · grind [Config.isHalted]

/-- Reverse halting: if p.toStandardForm reaches a halted config, p reaches a halted config
    with the same state. -/
theorem Steps.from_toStandardForm_halts {p : Program} {c c' : Config}
    (hsteps : Steps p.toStandardForm c c') (hhalted : c'.isHalted p.toStandardForm) :
    ∃ c₂, Steps p c c₂ ∧ c₂.isHalted p ∧ c'.state = c₂.state := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl =>
    refine ⟨c', Steps.refl _, ?_, rfl⟩
    simp only [Config.isHalted, Program.toStandardForm_length] at hhalted ⊢
    exact hhalted
  | head hstep hrest ih =>
    rcases Step.from_toStandardForm hstep with
      hsame | ⟨hhalted_mid, c_mid, hstep_mid, hhalted_mid', hstate_eq⟩
    · obtain ⟨c₂, hsteps₂, hhalted₂, hstate_eq⟩ := ih
      exact ⟨c₂, Steps.trans (Steps.single hsame) hsteps₂, hhalted₂, hstate_eq⟩
    · rename_i c_next
      have hrest_trivial : c_next = c' := Steps.eq_of_halts (Steps.refl _) hhalted_mid hrest hhalted
      subst hrest_trivial
      exact ⟨c_mid, Steps.single hstep_mid, hhalted_mid', hstate_eq⟩

/-- Reverse halting theorem. -/
theorem Halts.of_toStandardForm {p : Program} {inputs : List ℕ}
    (h : Halts p.toStandardForm inputs) : Halts p inputs := by
  obtain ⟨c, hsteps, hhalted⟩ := h
  obtain ⟨c₂, hsteps₂, hhalted₂, _⟩ := Steps.from_toStandardForm_halts hsteps hhalted
  exact ⟨c₂, hsteps₂, hhalted₂⟩

/-- Halting equivalence: original halts iff standard form halts. -/
theorem Halts.toStandardForm_iff {p : Program} {inputs : List ℕ} :
    Halts p inputs ↔ Halts p.toStandardForm inputs :=
  ⟨Halts.toStandardForm, Halts.of_toStandardForm⟩

/-! ### eval Preservation -/

/-- State preservation: both reach configs with the same state. -/
theorem evalConfig_toStandardForm_state {p : Program} {inputs : List ℕ}
    (hp : (evalConfig p inputs).Dom) (hq : (evalConfig p.toStandardForm inputs).Dom) :
    ((evalConfig p inputs).get hp).state =
      ((evalConfig p.toStandardForm inputs).get hq).state := by
  have ⟨hsteps, hhalted⟩ := evalConfig_spec p hp
  have ⟨hsteps', hhalted'⟩ := evalConfig_spec p.toStandardForm hq
  obtain ⟨c₂, hsteps₂, hhalted₂, hstate_eq⟩ := Steps.toStandardForm_halts hsteps hhalted
  rw [Steps.eq_of_halts hsteps' hhalted' hsteps₂ hhalted₂, hstate_eq]

/-- eval equality: both programs produce the same partial result. -/
theorem eval_toStandardForm {p : Program} {inputs : List ℕ} :
    eval p inputs = eval p.toStandardForm inputs := by
  simp only [eval]
  apply Part.ext'
  · simp only [Part.map_Dom]
    exact Halts.toStandardForm_iff
  · intro hp hq
    simp only [Part.map_get, Function.comp_apply, State.output,
               evalConfig_toStandardForm_state hp hq]

/-- A program is equivalent to its standard form. -/
theorem toStandardForm_equiv (p : Program) : p.toStandardForm ≈ p :=
  fun _ => eval_toStandardForm.symm

end Cslib.URM

end
