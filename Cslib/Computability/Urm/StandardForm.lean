/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
module

public import Cslib.Computability.Urm.StraightLine

/-! # Standard Form Programs

This file defines standard-form programs (those with bounded jump targets)
and proves their execution properties.

## Main definitions

- `Program.isStandardForm`: all jump targets are bounded by program length
- `Program.IsStandardForm`: Prop version of the standard form property
- `Program.to_standard_form`: convert a program to standard form

## Main results

- `straight_line_isStandardForm`: straight-line programs are standard form
- `Halts.to_standard_form_iff`: halting equivalence with normalized programs
-/

@[expose] public section

namespace Cslib.Urm

/-! ## Standard Form Definitions -/

namespace Program

/-- A program is in standard form if all jump targets are bounded by the program length.
Jumps can target any instruction (0..length-1) or the "virtual halt" position (length). -/
def isStandardForm (p : Program) : Bool :=
  p.all (Instr.jumps_bounded_by p.length)

/-- Prop version: a program is in standard form. -/
def IsStandardForm (p : Program) : Prop :=
  ∀ instr ∈ p, instr.JumpsBoundedBy p.length

instance (p : Program) : Decidable p.IsStandardForm :=
  inferInstanceAs (Decidable (∀ instr ∈ p, instr.JumpsBoundedBy p.length))

theorem isStandardForm_iff_IsStandardForm (p : Program) :
    p.isStandardForm = true ↔ p.IsStandardForm := by
  simp only [isStandardForm, IsStandardForm, Instr.JumpsBoundedBy, List.all_eq_true]

/-- Convert a program to standard form by capping all jump targets at the program length. -/
def to_standard_form (p : Program) : Program :=
  p.map (Instr.cap_jump p.length)

/-- to_standard_form preserves program length. -/
@[simp]
theorem to_standard_form_length (p : Program) :
    p.to_standard_form.length = p.length := by
  simp [to_standard_form]

/-- to_standard_form produces a standard form program. -/
theorem to_standard_form_isStandardForm (p : Program) :
    p.to_standard_form.IsStandardForm := by
  unfold IsStandardForm to_standard_form
  rw [List.length_map]
  intro instr hinstr
  obtain ⟨orig, _, rfl⟩ := List.mem_map.mp hinstr
  exact Instr.JumpsBoundedBy.cap_jump p.length orig

/-- Accessing an instruction in to_standard_form gives the cap_jump'd instruction. -/
theorem getElem?_to_standard_form (p : Program) (i : ℕ) :
    p.to_standard_form[i]? = (p[i]?).map (Instr.cap_jump p.length) := by
  simp only [to_standard_form, List.getElem?_map]

/-- to_standard_form is idempotent: applying it twice equals applying it once. -/
@[simp]
theorem to_standard_form_idempotent (p : Program) :
    p.to_standard_form.to_standard_form = p.to_standard_form := by
  simp only [to_standard_form, List.length_map, List.map_map]
  congr 1
  funext instr
  exact Instr.cap_jump_idempotent p.length instr

end Program

/-! ## Standard Form Properties -/

/-- Straight-line programs are in standard form. -/
theorem straight_line_isStandardForm {p : Program} (hsl : p.IsStraightLine) :
    p.IsStandardForm := by
  unfold Program.IsStandardForm
  intro instr hinstr
  unfold Program.IsStraightLine Program.is_straight_line at hsl
  simp only [List.all_eq_true, Bool.not_eq_true'] at hsl
  have hnotJump : ¬instr.IsJump := by
    unfold Instr.IsJump; simp only [Bool.not_eq_true]; exact hsl instr hinstr
  exact Instr.JumpsBoundedBy_of_not_IsJump hnotJump p.length

/-! ## Behavioral Equivalence

Two programs are behaviorally equivalent if they halt on the same inputs
and produce the same results. We prove that p and p.to_standard_form are
behaviorally equivalent. -/

/-! ### Behavioral Equivalence via Step Correspondence

p and p.to_standard_form differ only for jumps with target q > p.length:
- Original: jumps to q (halted since q ≥ p.length)
- Standard form: jumps to min q p.length = p.length (also halted)
- Both halt with the same state

For all other cases, both programs step identically. -/

/-- Forward step correspondence: if p steps from c to c', then either:
    (1) p.to_standard_form steps from c to c' (same step), or
    (2) c' is halted in p, and p.to_standard_form steps to a config that is also halted
        with the same state (this only happens for jumps with unbounded targets). -/
theorem Step.to_standard_form {p : Program} {c c' : Config} (hstep : Step p c c') :
    Step p.to_standard_form c c' ∨
    (c'.is_halted p ∧ ∃ c₂, Step p.to_standard_form c c₂ ∧
      c₂.is_halted p.to_standard_form ∧ c'.state = c₂.state) := by
  cases hstep with
  | zero hinstr =>
    left; exact Step.zero (by simp [Program.getElem?_to_standard_form, hinstr])
  | succ hinstr =>
    left; exact Step.succ (by simp [Program.getElem?_to_standard_form, hinstr])
  | trans hinstr =>
    left; exact Step.trans (by simp [Program.getElem?_to_standard_form, hinstr])
  | jump_ne hinstr hne =>
    left
    rename_i m n q
    have hcap : p.to_standard_form[c.pc]? = some (Instr.J m n (min q p.length)) := by
      simp [Program.getElem?_to_standard_form, hinstr]
    exact Step.jump_ne hcap hne
  | jump_eq hinstr heq =>
    rename_i m n q
    by_cases hbounded : q ≤ p.length
    · left
      have hcap : p.to_standard_form[c.pc]? = some (Instr.J m n q) := by
        simp [Program.getElem?_to_standard_form, hinstr, Instr.cap_jump, Nat.min_eq_left hbounded]
      exact Step.jump_eq hcap heq
    · right
      have hgt : q > p.length := Nat.not_le.mp hbounded
      have hcap : p.to_standard_form[c.pc]? = some (Instr.J m n p.length) := by
        simp [Program.getElem?_to_standard_form, hinstr, Instr.cap_jump,
              Nat.min_eq_right (Nat.le_of_lt hgt)]
      exact ⟨by simp [Config.is_halted]; omega,
             ⟨p.length, c.state⟩, Step.jump_eq hcap heq,
             by simp [Config.is_halted, Program.to_standard_form_length], rfl⟩

/-- Forward halting: if p reaches a halted config, p.to_standard_form reaches a halted config
    with the same state. -/
theorem Steps.to_standard_form_halts {p : Program} {c c' : Config}
    (hsteps : Steps p c c') (hhalted : c'.is_halted p) :
    ∃ c₂, Steps p.to_standard_form c c₂ ∧
      c₂.is_halted p.to_standard_form ∧ c'.state = c₂.state := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl =>
    refine ⟨c', Steps.refl _, ?_, rfl⟩
    simp only [Config.is_halted, Program.to_standard_form_length]; exact hhalted
  | head hstep hrest ih =>
    rcases Step.to_standard_form hstep with
      hsame | ⟨hhalted_mid, c_mid, hstep_mid, hhalted_mid', hstate_eq⟩
    · obtain ⟨c₂, hsteps₂, hhalted₂, hstate_eq⟩ := ih
      exact ⟨c₂, Steps.trans (Steps.single hsame) hsteps₂, hhalted₂, hstate_eq⟩
    · rename_i c_next
      have hrest_trivial : c_next = c' := Steps.eq_of_halts (Steps.refl _) hhalted_mid hrest hhalted
      subst hrest_trivial
      exact ⟨c_mid, Steps.single hstep_mid, hhalted_mid', hstate_eq⟩

/-- Forward halting theorem. -/
theorem Halts.to_standard_form {p : Program} {inputs : List ℕ} (h : Halts p inputs) :
    Halts p.to_standard_form inputs := by
  obtain ⟨c, hsteps, hhalted⟩ := h
  obtain ⟨c₂, hsteps₂, hhalted₂, _⟩ := Steps.to_standard_form_halts hsteps hhalted
  exact ⟨c₂, hsteps₂, hhalted₂⟩

/-- Reverse step correspondence: if p.to_standard_form steps from c to c', then either:
    (1) p steps from c to c' (same step), or
    (2) c' is halted in p.to_standard_form, and p steps to a config that is also halted
        with the same state (this only happens for jumps with unbounded targets). -/
theorem Step.from_to_standard_form {p : Program} {c c' : Config}
    (hstep : Step p.to_standard_form c c') :
    Step p c c' ∨
    (c'.is_halted p.to_standard_form ∧ ∃ c₂, Step p c c₂ ∧
      c₂.is_halted p ∧ c'.state = c₂.state) := by
  cases hstep with
  | zero hinstr =>
    left
    rw [Program.getElem?_to_standard_form] at hinstr
    simp only [Option.map_eq_some_iff] at hinstr
    obtain ⟨instr, hinstr', hcap⟩ := hinstr
    cases instr with
    | Z n' => simp only [Instr.cap_jump, Instr.Z.injEq] at hcap; subst hcap; exact Step.zero hinstr'
    | S _ | T _ _ | J _ _ _ => simp at hcap
  | succ hinstr =>
    left
    rw [Program.getElem?_to_standard_form] at hinstr
    simp only [Option.map_eq_some_iff] at hinstr
    obtain ⟨instr, hinstr', hcap⟩ := hinstr
    cases instr with
    | S n' => simp only [Instr.cap_jump, Instr.S.injEq] at hcap; subst hcap; exact Step.succ hinstr'
    | Z _ | T _ _ | J _ _ _ => simp at hcap
  | trans hinstr =>
    left
    rw [Program.getElem?_to_standard_form] at hinstr
    simp only [Option.map_eq_some_iff] at hinstr
    obtain ⟨instr, hinstr', hcap⟩ := hinstr
    cases instr with
    | T m' n' =>
      simp only [Instr.cap_jump, Instr.T.injEq] at hcap
      obtain ⟨rfl, rfl⟩ := hcap; exact Step.trans hinstr'
    | Z _ | S _ | J _ _ _ => simp at hcap
  | jump_ne hinstr hne =>
    left
    rw [Program.getElem?_to_standard_form] at hinstr
    simp only [Option.map_eq_some_iff] at hinstr
    obtain ⟨instr, hinstr', hcap⟩ := hinstr
    cases instr with
    | J m' n' q' =>
      simp only [Instr.cap_jump, Instr.J.injEq] at hcap
      obtain ⟨rfl, rfl, _⟩ := hcap; exact Step.jump_ne hinstr' hne
    | Z _ | S _ | T _ _ => simp at hcap
  | jump_eq hinstr heq =>
    rw [Program.getElem?_to_standard_form] at hinstr
    simp only [Option.map_eq_some_iff] at hinstr
    obtain ⟨instr, hinstr', hcap⟩ := hinstr
    cases instr with
    | J m' n' q' =>
      simp only [Instr.cap_jump, Instr.J.injEq] at hcap
      obtain ⟨rfl, rfl, htarget⟩ := hcap
      by_cases hbounded : q' ≤ p.length
      · left
        rw [Nat.min_eq_left hbounded] at htarget; subst htarget
        exact Step.jump_eq hinstr' heq
      · right
        have hgt : q' > p.length := Nat.not_le.mp hbounded
        rw [Nat.min_eq_right (Nat.le_of_lt hgt)] at htarget; subst htarget
        exact ⟨by simp [Config.is_halted, Program.to_standard_form_length],
               ⟨q', c.state⟩, Step.jump_eq hinstr' heq,
               by simp [Config.is_halted]; omega, rfl⟩
    | Z _ | S _ | T _ _ => simp at hcap

/-- Reverse halting: if p.to_standard_form reaches a halted config, p reaches a halted config
    with the same state. -/
theorem Steps.from_to_standard_form_halts {p : Program} {c c' : Config}
    (hsteps : Steps p.to_standard_form c c') (hhalted : c'.is_halted p.to_standard_form) :
    ∃ c₂, Steps p c c₂ ∧ c₂.is_halted p ∧ c'.state = c₂.state := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl =>
    refine ⟨c', Steps.refl _, ?_, rfl⟩
    simp only [Config.is_halted, Program.to_standard_form_length] at hhalted ⊢; exact hhalted
  | head hstep hrest ih =>
    rcases Step.from_to_standard_form hstep with
      hsame | ⟨hhalted_mid, c_mid, hstep_mid, hhalted_mid', hstate_eq⟩
    · obtain ⟨c₂, hsteps₂, hhalted₂, hstate_eq⟩ := ih
      exact ⟨c₂, Steps.trans (Steps.single hsame) hsteps₂, hhalted₂, hstate_eq⟩
    · rename_i c_next
      have hrest_trivial : c_next = c' := Steps.eq_of_halts (Steps.refl _) hhalted_mid hrest hhalted
      subst hrest_trivial
      exact ⟨c_mid, Steps.single hstep_mid, hhalted_mid', hstate_eq⟩

/-- Reverse halting theorem. -/
theorem Halts.of_to_standard_form {p : Program} {inputs : List ℕ}
    (h : Halts p.to_standard_form inputs) : Halts p inputs := by
  obtain ⟨c, hsteps, hhalted⟩ := h
  obtain ⟨c₂, hsteps₂, hhalted₂, _⟩ := Steps.from_to_standard_form_halts hsteps hhalted
  exact ⟨c₂, hsteps₂, hhalted₂⟩

/-- Halting equivalence: original halts iff standard form halts. -/
theorem Halts.to_standard_form_iff {p : Program} {inputs : List ℕ} :
    Halts p inputs ↔ Halts p.to_standard_form inputs :=
  ⟨Halts.to_standard_form, Halts.of_to_standard_form⟩

/-! ### eval Preservation -/

/-- State preservation: both reach configs with the same state. -/
theorem eval_to_standard_form_state {p : Program} {inputs : List ℕ}
    (hp : Halts p inputs) (hq : Halts p.to_standard_form inputs) :
    (Classical.choose hp).state = (Classical.choose hq).state := by
  have ⟨hsteps, hhalted⟩ := Classical.choose_spec hp
  have ⟨hsteps', hhalted'⟩ := Classical.choose_spec hq
  obtain ⟨c₂, hsteps₂, hhalted₂, hstate_eq⟩ := Steps.to_standard_form_halts hsteps hhalted
  rw [Steps.eq_of_halts hsteps' hhalted' hsteps₂ hhalted₂, hstate_eq]

/-- eval equality: both programs produce the same partial result. -/
theorem eval_to_standard_form {p : Program} {inputs : List ℕ} :
    eval p inputs = eval p.to_standard_form inputs := by
  apply Part.ext'
  · simp only [eval]
    exact Halts.to_standard_form_iff
  · intro hp hq
    simp only [eval, State.output, eval_to_standard_form_state hp hq]

/-- A program is equivalent to its standard form. -/
theorem to_standard_form_equiv (p : Program) : p.to_standard_form ≈ p :=
  fun _ => eval_to_standard_form.symm

end Cslib.Urm

end
