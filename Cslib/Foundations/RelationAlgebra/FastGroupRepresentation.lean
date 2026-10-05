/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.FastCycles
public import Cslib.Foundations.RelationAlgebra.FiniteRepresentation
public import Mathlib.Data.ZMod.Basic

/-!
# Checking group representations with product masks

For each group element, collect the pairs of labels of its factorizations into one bitmask.
Comparing this mask with the cycle table checks all pairs of atoms together, so each group
factorization is evaluated only once.
-/

@[expose] public section

namespace Cslib.RelationAlgebra

namespace Code

/-- The pairs of atoms whose product contains atom `c`. -/
def factorMask (n t c : ℕ) : ℕ :=
  bitsOf (fun i => bitAt t (index n (Nat.div i n) (Nat.mod i n) c)) (Nat.mul n n)

private theorem pairIndex_lt {n a b : ℕ} (ha : a < n) (hb : b < n) :
    index n 0 a b < n * n := by
  simp only [index_eq, Nat.zero_mul, Nat.zero_add]
  calc
    a * n + b < a * n + n := Nat.add_lt_add_left hb _
    _ = (a + 1) * n := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ n * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt ha)

theorem bitAt_factorMask {n t a b c : ℕ} (ha : a < n) (hb : b < n) :
    bitAt (factorMask n t c) (index n 0 a b) = bitAt t (index n a b c) := by
  change bitAt (bitsOf (fun i => bitAt t (index n (i / n) (i % n) c)) (n * n))
    (index n 0 a b) = _
  rw [bitAt_bitsOf (pairIndex_lt ha hb), index_div hb, index_mod hb,
    Nat.zero_mul, Nat.zero_add]

variable {j k : ℕ} {G : Type*} [Group G]

/-- Label pairs of all enumerated factorizations of `g`. -/
def groupFactorMask (size : ℕ) (label : G → Atom j k) (enum : ℕ → G) (g : G) : ℕ :=
  orBelow (fun h => Nat.shiftLeft 1
    (index (atomCount j k) 0 (label (enum h)).code (label ((enum h)⁻¹ * g)).code)) size

/-- Check the factorization mask at every enumerated group element. -/
def groupCompositionCheck (size t : ℕ) (label : G → Atom j k) (enum : ℕ → G) : Bool :=
  allBelow (fun g => Nat.beq (factorMask (atomCount j k) t (label (enum g)).code)
    (groupFactorMask size label enum (enum g))) size

theorem bitAt_groupFactorMask (size : ℕ) (label : G → Atom j k) (enum : ℕ → G)
    (g : G) (a b : Atom j k) :
    bitAt (groupFactorMask size label enum g) (index (atomCount j k) 0 a.code b.code) = true ↔
      ∃ h < size, label (enum h) = a ∧ label ((enum h)⁻¹ * g) = b := by
  rw [groupFactorMask, bitAt_eq_testBit, testBit_orBelow]
  apply exists_congr
  intro h
  apply and_congr_right
  intro _
  simp only [Nat.shiftLeft_eq', Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq]
  constructor
  · intro heq
    obtain ⟨_, ha, hb⟩ := index_injective (label (enum h)).code_lt
      (label ((enum h)⁻¹ * g)).code_lt a.code_lt b.code_lt heq
    exact ⟨Atom.code_injective ha, Atom.code_injective hb⟩
  · rintro ⟨ha, hb⟩
    rw [ha, hb]

end Code

/-- One mask comparison per group element proves the composition field of a representation. -/
theorem groupComposition_of_check {j k : ℕ} {G : Type*} [Group G]
    {cycles : Finset (Cycle j k)} {t : ℕ} (ht : EncodesTable cycles t)
    (size : ℕ) (label : G → Atom j k) (enum : ℕ → G)
    (cover : ∀ g, ∃ i < size, enum i = g)
    (check : Code.groupCompositionCheck size t label enum = true)
    (a b : Atom j k) (g : G) :
    cycleClosure cycles a b (label g) ↔ ∃ h, label h = a ∧ label (h⁻¹ * g) = b := by
  obtain ⟨i, hi, rfl⟩ := cover g
  have h := Code.allBelow_eq_true.mp check i hi
  simp only [Nat.beq_eq] at h
  rw [cycleClosure_iff_bitAt ht, ← Code.bitAt_factorMask a.code_lt b.code_lt, h,
    Code.bitAt_groupFactorMask]
  constructor
  · rintro ⟨h, _, ha, hb⟩
    exact ⟨enum h, ha, hb⟩
  · rintro ⟨h, ha, hb⟩
    obtain ⟨r, hr, rfl⟩ := cover h
    exact ⟨r, hr, ha, hb⟩

/-- Composition for a cyclic group, using its standard residue enumeration. -/
theorem zmodComposition_of_check {j k modulus : ℕ} [NeZero modulus]
    {cycles : Finset (Cycle j k)} {t : ℕ} (ht : EncodesTable cycles t)
    (label : Multiplicative (ZMod modulus) → Atom j k)
    (check : Code.groupCompositionCheck modulus t label
      (fun i => Multiplicative.ofAdd (i : ZMod modulus)) = true)
    (a b : Atom j k) (g : Multiplicative (ZMod modulus)) :
    cycleClosure cycles a b (label g) ↔ ∃ h, label h = a ∧ label (h⁻¹ * g) = b :=
  groupComposition_of_check ht modulus label _
    (fun g => ⟨g.toAdd.val, ZMod.val_lt _,
      congrArg Multiplicative.ofAdd (ZMod.natCast_zmod_val _)⟩) check a b g

end Cslib.RelationAlgebra
