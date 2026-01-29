/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
module

public import Cslib.Computability.Urm.Defs

/-! # URM Basic Lemmas

This file contains basic lemmas and helper operations for URM instructions and programs.

## Main definitions

- `Instr.isJump`: predicate for jump instructions
- `Instr.jumps_bounded_by`: checks if jump targets are bounded
- `Instr.cap_jump`: caps jump targets to a given length

## Main results

- `JumpsBoundedBy.mono`: bounded jumps are monotonic in the bound
- `JumpsBoundedBy.shift_jumps`: shifting preserves bounded jumps
- `Program.mem_max_register`: instruction max_register bounded by program max_register
-/

@[expose] public section

namespace Cslib.Urm

namespace Instr

/-! ## Jump Instructions -/

/-- An instruction is a jump instruction if it's J. -/
def isJump : Instr → Bool
  | J _ _ _ => true
  | _ => false

/-- Prop version: an instruction is a jump. -/
def IsJump (instr : Instr) : Prop := instr.isJump = true

instance (instr : Instr) : Decidable instr.IsJump :=
  decidable_of_iff (instr.isJump = true) Iff.rfl

/-- Z instruction is not a jump. -/
@[simp, scoped grind =]
theorem Z_not_isJump (n : ℕ) : (Z n).isJump = false := rfl

/-- S instruction is not a jump. -/
@[simp, scoped grind =]
theorem S_not_isJump (n : ℕ) : (S n).isJump = false := rfl

/-- T instruction is not a jump. -/
@[simp, scoped grind =]
theorem T_not_isJump (m n : ℕ) : (T m n).isJump = false := rfl

/-- J instruction is a jump. -/
@[simp, scoped grind =]
theorem J_isJump (m n q : ℕ) : (J m n q).isJump = true := rfl

/-- Z instruction is not a jump (Prop version). -/
@[simp]
theorem Z_not_IsJump (n : ℕ) : ¬(Z n).IsJump := by simp [IsJump]

/-- S instruction is not a jump (Prop version). -/
@[simp]
theorem S_not_IsJump (n : ℕ) : ¬(S n).IsJump := by simp [IsJump]

/-- T instruction is not a jump (Prop version). -/
@[simp]
theorem T_not_IsJump (m n : ℕ) : ¬(T m n).IsJump := by simp [IsJump]

/-- J instruction is a jump (Prop version). -/
theorem J_IsJump (m n q : ℕ) : (J m n q).IsJump := rfl

/-- shift_jumps is identity for non-jumping instructions. -/
theorem shift_jumps_of_not_isJump {instr : Instr}
    (h : instr.isJump = false) (offset : ℕ) : instr.shift_jumps offset = instr := by
  cases instr with
  | Z _ | S _ | T _ _ => rfl
  | J _ _ _ => simp [isJump] at h

/-! ## Bounded Jump Targets -/

/-- Check if an instruction's jump target is bounded by a given length.
Non-jump instructions trivially satisfy this. -/
def jumps_bounded_by (len : ℕ) : Instr → Bool
  | Z _ => true
  | S _ => true
  | T _ _ => true
  | J _ _ q => q ≤ len

/-- Prop version: an instruction's jump target is bounded. -/
def JumpsBoundedBy (len : ℕ) (instr : Instr) : Prop := instr.jumps_bounded_by len = true

instance (len : ℕ) (instr : Instr) : Decidable (instr.JumpsBoundedBy len) :=
  decidable_of_iff (instr.jumps_bounded_by len = true) Iff.rfl

/-- Non-jumping instructions have bounded jumps for any length. -/
theorem JumpsBoundedBy_of_not_IsJump {instr : Instr} (h : ¬instr.IsJump)
    (len : ℕ) : instr.JumpsBoundedBy len := by
  unfold IsJump at h; simp only [Bool.not_eq_true] at h
  cases instr <;> grind [isJump, jumps_bounded_by, JumpsBoundedBy]

/-- jumps_bounded_by is monotonic: if bounded for len1, then bounded for any len2 ≥ len1. -/
theorem JumpsBoundedBy.mono {instr : Instr} {len1 len2 : ℕ}
    (h : instr.JumpsBoundedBy len1) (hle : len1 ≤ len2) :
    instr.JumpsBoundedBy len2 := by
  unfold JumpsBoundedBy at h ⊢
  cases instr with
  | Z _ | S _ | T _ _ => simp [jumps_bounded_by]
  | J _ _ q => simp only [jumps_bounded_by, decide_eq_true_eq] at h ⊢; omega

/-- shift_jumps preserves bounded jumps with adjusted bound. -/
theorem JumpsBoundedBy.shift_jumps {instr : Instr} {len offset : ℕ}
    (h : instr.JumpsBoundedBy len) :
    (instr.shift_jumps offset).JumpsBoundedBy (offset + len) := by
  unfold JumpsBoundedBy at h ⊢
  cases instr with
  | Z _ | S _ | T _ _ => rfl
  | J _ _ q => simp only [Instr.shift_jumps, jumps_bounded_by, decide_eq_true_eq] at h ⊢; omega

/-! ## Jump Target Capping -/

/-- Cap a jump target to be at most `len`. Non-jump instructions are unchanged. -/
def cap_jump (len : ℕ) : Instr → Instr
  | Z n => Z n
  | S n => S n
  | T m n => T m n
  | J m n q => J m n (min q len)

@[simp]
theorem cap_jump_Z (len n : ℕ) : (Z n).cap_jump len = Z n := rfl

@[simp]
theorem cap_jump_S (len n : ℕ) : (S n).cap_jump len = S n := rfl

@[simp]
theorem cap_jump_T (len m n : ℕ) : (T m n).cap_jump len = T m n := rfl

@[simp]
theorem cap_jump_J (len m n q : ℕ) :
    (J m n q).cap_jump len = J m n (min q len) := rfl

/-- cap_jump always produces an instruction with bounded jump. -/
theorem JumpsBoundedBy.cap_jump (len : ℕ) (instr : Instr) :
    (instr.cap_jump len).JumpsBoundedBy len := by
  unfold JumpsBoundedBy
  cases instr <;> grind [cap_jump, jumps_bounded_by]

/-- cap_jump is idempotent: capping twice is the same as capping once. -/
@[simp]
theorem cap_jump_idempotent (len : ℕ) (instr : Instr) :
    (instr.cap_jump len).cap_jump len = instr.cap_jump len := by
  cases instr with
  | Z | S | T => rfl
  | J m n q => simp [cap_jump]

end Instr

namespace Program

/-- Any instruction in a program has max_register at most the program's max_register. -/
theorem mem_max_register {p : Program} {instr : Instr} (h : instr ∈ p) :
    instr.max_register ≤ p.max_register := by
  unfold max_register
  rw [List.foldl_map.symm, List.foldl_eq_foldr]
  exact List.le_max_of_le' 0 (List.mem_map.mpr ⟨instr, h, rfl⟩) (le_refl _)

end Program

end Cslib.Urm

end
