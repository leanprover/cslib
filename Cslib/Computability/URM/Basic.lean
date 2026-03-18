/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
module

public import Cslib.Computability.URM.Defs
public import Mathlib.Data.List.MinMax

/-! # URM Basic Lemmas

This file contains basic lemmas and helper operations for URM types.

## Main definitions

- `Instr.IsJump`: predicate for jump instructions
- `Instr.JumpsBoundedBy`: checks if jump targets are bounded
- `Instr.capJump`: caps jump targets to a given length

## Main results

- `Regs.write_read_self`, `Regs.write_read_of_ne`: register read/write lemmas
- `State.isHalted_iff`, `State.ext`: state lemmas
- `JumpsBoundedBy.mono`: bounded jumps are monotonic in the bound
- `JumpsBoundedBy.shiftJumps`: shifting preserves bounded jumps
- `Program.mem_maxRegister`: instruction maxRegister bounded by program maxRegister
-/

@[expose] public section

namespace Cslib.URM

/-! ## Register Lemmas -/

namespace Regs

@[simp, scoped grind =]
theorem write_read_self (σ : Regs) (n v : ℕ) : (σ.write n v).read n = v := by
  simp only [write, read, Function.update_self]

@[simp, scoped grind =]
theorem write_read_of_ne (σ : Regs) (m n v : ℕ) (h : m ≠ n) :
    (σ.write n v).read m = σ.read m := by
  simp only [write, read, Function.update_of_ne h]

end Regs

/-! ## State Lemmas -/

namespace State

@[simp]
theorem isHalted_iff (s : State) (p : Program) : s.isHalted p ↔ p.length ≤ s.pc := Iff.rfl

/-- Extensionality for State: two states are equal iff their components are equal. -/
@[ext]
theorem ext {s₁ s₂ : State} (hpc : s₁.pc = s₂.pc) (hregs : s₁.regs = s₂.regs) : s₁ = s₂ := by
  cases s₁; cases s₂; simp only at hpc hregs; simp [hpc, hregs]

end State

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

/-- shiftJumps is identity for non-jumping instructions. -/
theorem shiftJumps_of_nonJump {instr : Instr}
    (h : ¬instr.IsJump) (offset : ℕ) : instr.shiftJumps offset = instr := by
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
theorem jumpsBoundedBy_of_nonJump {instr : Instr} (h : ¬instr.IsJump)
    (len : ℕ) : instr.JumpsBoundedBy len := by
  cases instr with
  | J _ _ _ => exact absurd trivial h
  | _ => trivial

/-- JumpsBoundedBy is monotonic: if bounded for len1, then bounded for any len2 ≥ len1. -/
theorem JumpsBoundedBy.mono {instr : Instr} {len1 len2 : ℕ}
    (h : instr.JumpsBoundedBy len1) (hle : len1 ≤ len2) :
    instr.JumpsBoundedBy len2 := by
  grind [JumpsBoundedBy]

/-- shiftJumps preserves bounded jumps with adjusted bound. -/
theorem JumpsBoundedBy.shiftJumps {instr : Instr} {len offset : ℕ}
    (h : instr.JumpsBoundedBy len) :
    (instr.shiftJumps offset).JumpsBoundedBy (offset + len) := by
  cases instr with
  | J _ _ q => simp only [Instr.shiftJumps, JumpsBoundedBy] at h ⊢; omega
  | _ => trivial

/-! ## Jump Target Capping -/

/-- Cap a jump target to be at most `len`. Non-jump instructions are unchanged. -/
@[scoped grind =]
def capJump (len : ℕ) : Instr → Instr
  | Z n => Z n
  | S n => S n
  | T m n => T m n
  | J m n q => J m n (min q len)

@[simp]
theorem capJump_Z (len n : ℕ) : (Z n).capJump len = Z n := rfl

@[simp]
theorem capJump_S (len n : ℕ) : (S n).capJump len = S n := rfl

@[simp]
theorem capJump_T (len m n : ℕ) : (T m n).capJump len = T m n := rfl

@[simp]
theorem capJump_J (len m n q : ℕ) :
    (J m n q).capJump len = J m n (min q len) := rfl

/-- capJump always produces an instruction with bounded jump. -/
theorem JumpsBoundedBy.capJump (len : ℕ) (instr : Instr) :
    (instr.capJump len).JumpsBoundedBy len := by
  cases instr with
  | J _ _ q => exact Nat.min_le_right q len
  | _ => trivial

/-- capJump is idempotent: capping twice is the same as capping once. -/
@[simp]
theorem capJump_idempotent (len : ℕ) (instr : Instr) :
    (instr.capJump len).capJump len = instr.capJump len := by
  cases instr with
  | Z | S | T => rfl
  | J m n q => simp [capJump]

end Instr

namespace Program

/-- Any instruction in a program has maxRegister at most the program's maxRegister. -/
theorem mem_maxRegister {p : Program} {instr : Instr} (h : instr ∈ p) :
    instr.maxRegister ≤ p.maxRegister := by
  unfold maxRegister
  rw [List.foldl_map.symm, List.foldl_eq_foldr]
  exact List.le_max_of_le' 0 (List.mem_map.mpr ⟨instr, h, rfl⟩) (le_refl _)

end Program

end Cslib.URM

end
