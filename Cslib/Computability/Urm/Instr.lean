/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
module

public import Cslib.Init
public import Mathlib.Data.Finset.Insert

/-! # URM Instructions

This file defines URM instructions and their basic operations.

## Main definitions

- `Urm.Instr`: The four URM instructions (Z, S, T, J)
- `Instr.isJump`: predicate for J instructions
- `Instr.max_register`: maximum register index referenced
- `Instr.jumps_bounded_by`: checks if an instruction's jump target is bounded
- `Instr.cap_jump`: caps jump targets to a given length
-/

@[expose] public section

namespace Cslib.Urm

/-- URM instructions.
- `Z n`: Set register n to zero
- `S n`: Increment register n by one
- `T m n`: Transfer (copy) the contents of register m to register n
- `J m n q`: If registers m and n have equal contents, jump to instruction q;
             otherwise proceed to the next instruction
-/
@[grind]
inductive Instr : Type where
  | Z : ℕ → Instr
  | S : ℕ → Instr
  | T : ℕ → ℕ → Instr
  | J : ℕ → ℕ → ℕ → Instr
deriving DecidableEq, Repr

namespace Instr

/-- The registers read by an instruction. -/
@[scoped grind =]
def reads_from : Instr → Finset ℕ
  | Z _ => ∅
  | S n => {n}
  | T m _ => {m}
  | J m n _ => {m, n}

/-- The register written to by an instruction, if any. -/
@[scoped grind =]
def writes_to : Instr → Option ℕ
  | Z n => some n
  | S n => some n
  | T _ n => some n
  | J _ _ _ => none

/-- The maximum register index referenced by an instruction. -/
@[scoped grind =]
def max_register : Instr → ℕ
  | Z n => n
  | S n => n
  | T m n => max m n
  | J m n _ => max m n

/-- Shift all jump targets in an instruction by `offset`.
Used when concatenating programs to maintain correct jump destinations. -/
@[scoped grind =]
def shift_jumps (offset : ℕ) : Instr → Instr
  | Z n => Z n
  | S n => S n
  | T m n => T m n
  | J m n q => J m n (q + offset)

/-- Shift all register references in an instruction by `offset`.
Used to isolate register usage when composing programs. -/
@[scoped grind =]
def shift_registers (offset : ℕ) : Instr → Instr
  | Z n => Z (n + offset)
  | S n => S (n + offset)
  | T m n => T (m + offset) (n + offset)
  | J m n q => J (m + offset) (n + offset) q

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

end Cslib.Urm

end
