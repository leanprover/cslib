/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
module

public import Cslib.Computability.Urm.Defs

/-! # URM Basic Lemmas

This file contains basic lemmas and helper operations for URM types.

## Main definitions

- `Instr.IsJump`: predicate for jump instructions
- `Instr.JumpsBoundedBy`: checks if jump targets are bounded
- `Instr.cap_jump`: caps jump targets to a given length

## Main results

- `State.write_read_self`, `State.write_read_of_ne`: state read/write lemmas
- `Config.is_halted_iff`, `Config.ext`: configuration lemmas
- `JumpsBoundedBy.mono`: bounded jumps are monotonic in the bound
- `JumpsBoundedBy.shift_jumps`: shifting preserves bounded jumps
- `Program.mem_max_register`: instruction max_register bounded by program max_register
-/

@[expose] public section

namespace Cslib.Urm

/-! ## State Lemmas -/

namespace State

@[simp, scoped grind =]
theorem write_read_self (σ : State) (n v : ℕ) : (σ.write n v).read n = v := by
  simp only [write, read, Function.update_self]

@[simp, scoped grind =]
theorem write_read_of_ne (σ : State) (m n v : ℕ) (h : m ≠ n) :
    (σ.write n v).read m = σ.read m := by
  simp only [write, read, Function.update_of_ne h]

end State

/-! ## Config Lemmas -/

namespace Config

@[simp]
theorem is_halted_iff (c : Config) (p : Program) : c.is_halted p ↔ p.length ≤ c.pc := Iff.rfl

/-- Extensionality for Config: two configs are equal iff their components are equal. -/
@[ext]
theorem ext {c₁ c₂ : Config} (hpc : c₁.pc = c₂.pc) (hstate : c₁.state = c₂.state) : c₁ = c₂ := by
  cases c₁; cases c₂; simp only at hpc hstate; simp [hpc, hstate]

end Config

/-! ## Instruction Lemmas -/

namespace Instr

/-! ## Jump Instructions -/

/-- An instruction is a jump instruction. -/
def IsJump : Instr → Prop
  | J _ _ _ => True
  | _ => False

instance (instr : Instr) : Decidable instr.IsJump := by
  cases instr <;> simp only [IsJump] <;> infer_instance

/-- Z instruction is not a jump. -/
@[simp]
theorem Z_nonJump (n : ℕ) : ¬(Z n).IsJump := not_false

/-- S instruction is not a jump. -/
@[simp]
theorem S_nonJump (n : ℕ) : ¬(S n).IsJump := not_false

/-- T instruction is not a jump. -/
@[simp]
theorem T_nonJump (m n : ℕ) : ¬(T m n).IsJump := not_false

/-- J instruction is a jump. -/
@[simp]
theorem J_IsJump (m n q : ℕ) : (J m n q).IsJump := trivial

/-- shift_jumps is identity for non-jumping instructions. -/
theorem shift_jumps_of_nonJump {instr : Instr}
    (h : ¬instr.IsJump) (offset : ℕ) : instr.shift_jumps offset = instr := by
  cases instr with
  | Z _ | S _ | T _ _ => rfl
  | J _ _ _ => exact absurd trivial h

/-! ## Bounded Jump Targets -/

/-- An instruction's jump target is bounded by a given length.
Non-jump instructions trivially satisfy this. -/
def JumpsBoundedBy (len : ℕ) : Instr → Prop
  | J _ _ q => q ≤ len
  | _ => True

instance (len : ℕ) (instr : Instr) : Decidable (instr.JumpsBoundedBy len) := by
  cases instr <;> simp only [JumpsBoundedBy] <;> infer_instance

/-- Non-jumping instructions have bounded jumps for any length. -/
theorem JumpsBoundedBy_of_nonJump {instr : Instr} (h : ¬instr.IsJump)
    (len : ℕ) : instr.JumpsBoundedBy len := by
  cases instr with
  | J _ _ _ => exact absurd trivial h
  | _ => trivial

/-- JumpsBoundedBy is monotonic: if bounded for len1, then bounded for any len2 ≥ len1. -/
theorem JumpsBoundedBy.mono {instr : Instr} {len1 len2 : ℕ}
    (h : instr.JumpsBoundedBy len1) (hle : len1 ≤ len2) :
    instr.JumpsBoundedBy len2 := by
  cases instr with
  | J _ _ q => exact Nat.le_trans h hle
  | _ => trivial

/-- shift_jumps preserves bounded jumps with adjusted bound. -/
theorem JumpsBoundedBy.shift_jumps {instr : Instr} {len offset : ℕ}
    (h : instr.JumpsBoundedBy len) :
    (instr.shift_jumps offset).JumpsBoundedBy (offset + len) := by
  cases instr with
  | J _ _ q => simp only [Instr.shift_jumps, JumpsBoundedBy] at h ⊢; omega
  | _ => trivial

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
  cases instr with
  | J _ _ q => exact Nat.min_le_right q len
  | _ => trivial

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
