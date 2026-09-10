/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Boolean.Synthesis
public import Mathlib.Data.Fintype.BigOperators

/-!
# Lupanov's block construction

Split the truth table into address rows and data columns, and divide the rows into blocks.
Within each block, group columns with identical patterns. These groups partition the data
assignments, so disjoining their shared minterms contributes `2 ^ d` OR gates per block,
the leading term in the bound.

## References

* [O. B. Lupanov, *On a Method of Circuit Synthesis*][Lupanov1958],
  Section 1, equation (1.1), pp. 120-122: the original `(k, s)` representation.
* [Stasys Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012],
  Theorem 1.15: a modern exposition.
* [C. E. Shannon, *The Synthesis of Two-Terminal Switching Circuits*][Shannon1949],
  Section 3(d), pp. 73-77: the earlier universal-network method for relay contacts.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Lupanov

noncomputable section
variable {k d s : ℕ}

private abbrev Assignment (k : ℕ) := Fin k → Bool

private def index (k : ℕ) : Assignment k ≃ Fin (2 ^ k) :=
  Fintype.equivOfCardEq (by simp)

private def minterm : Assignment k ⊕ Assignment d → BooleanFunction (k + d)
  | .inl a => fun x => decide ((fun i => x (Fin.castAdd d i)) = a)
  | .inr b => fun x => decide ((fun i => x (Fin.natAdd k i)) = b)

private theorem minterms_synthesis :
    Synthesis (inputs (k + d)) (Set.range (minterm (k := k) (d := d)))
      ((2 ^ k + 2 ^ d) * (2 * (k + d) + 1)) := by
  have h (a : Assignment k ⊕ Assignment d) :
      Synthesis (inputs (k + d)) {minterm a} (2 * (k + d) + 1) := by
    cases a with
    | inl a =>
        exact (synthesis_minterm (Fin.castAdd d) a).mono
          Set.Subset.rfl Set.Subset.rfl (by omega)
    | inr b =>
        exact (synthesis_minterm (Fin.natAdd k) b).mono
          Set.Subset.rfl Set.Subset.rfl (by omega)
  simpa using Synthesis.family minterm (fun _ => 2 * (k + d) + 1) h

private theorem minterm_available (a : Assignment k ⊕ Assignment d) :
    Synthesis (Set.range minterm) {minterm a} 0 :=
  Synthesis.of_subset (by rintro _ rfl; exact ⟨a, rfl⟩)

private def column (f : BooleanFunction (k + d)) (block : ℕ) (data : Assignment d) : Assignment s :=
  fun offset => if h : block * s + offset.val < 2 ^ k then
    f (Fin.append ((index k).symm ⟨block * s + offset.val, h⟩) data) else false

private def leftRow (block : ℕ) (pattern : Assignment s) (offset : Fin s) :
    BooleanFunction (k + d) :=
  if pattern offset then
    if h : block * s + offset.val < 2 ^ k then
      minterm (.inl ((index k).symm ⟨block * s + offset.val, h⟩))
    else fun _ => false
  else fun _ => false

private def left (block : ℕ) (pattern : Assignment s) : BooleanFunction (k + d) :=
  fun x => decide (∃ offset, leftRow (d := d) block pattern offset x = true)

private def support (f : BooleanFunction (k + d)) (block : ℕ) (pattern : Assignment s) :
    Finset (Assignment d) := Finset.univ.filter fun data => column f block data = pattern

private def right (f : BooleanFunction (k + d)) (block : ℕ) (pattern : Assignment s) :
    BooleanFunction (k + d) :=
  fun x => decide (∃ data ∈ support f block pattern, minterm (.inr data) x = true)

private theorem support_card_sum (f : BooleanFunction (k + d)) (block : ℕ) :
    ∑ pattern : Assignment s, (support f block pattern).card = 2 ^ d := by
  simpa [support] using (Finset.card_eq_sum_card_fiberwise
    (s := Finset.univ) (t := Finset.univ) (f := column (s := s) f block) (by simp)).symm

private theorem left_synthesis (block : ℕ) (pattern : Assignment s) :
    Synthesis (Set.range (minterm (k := k) (d := d))) {left block pattern} (2 * s + 1) := by
  have h (offset : Fin s) :
      Synthesis (Set.range (minterm (k := k) (d := d))) {leftRow block pattern offset} 1 := by
    unfold leftRow
    split
    · split
      · exact (minterm_available _).mono
          Set.Subset.rfl Set.Subset.rfl (by omega : 0 ≤ 1)
      · exact Synthesis.const false
    · exact Synthesis.const false
  change Synthesis (Set.range (minterm (k := k) (d := d)))
    {fun x => decide (∃ offset, leftRow block pattern offset x = true)} (2 * s + 1)
  simpa [Nat.mul_comm] using Synthesis.exists_mem Finset.univ
    (leftRow (d := d) block pattern) (fun _ => 1) (fun i _ => h i)

private theorem right_synthesis (f : BooleanFunction (k + d)) (block : ℕ) (pattern : Assignment s) :
    Synthesis (Set.range minterm) {right f block pattern} ((support f block pattern).card + 1) := by
  change Synthesis (Set.range (minterm (k := k) (d := d)))
    {fun x => decide (∃ data ∈ support f block pattern, minterm (.inr data) x = true)} _
  simpa using Synthesis.exists_mem (support f block pattern)
    (fun data => minterm (.inr data)) (fun _ => 0)
    (fun data _ => minterm_available (.inr data))

private theorem left_eq_true (block : ℕ) (pattern : Assignment s) (x : Assignment (k + d)) :
    left block pattern x = true ↔ ∃ offset : Fin s,
      ∃ h : block * s + offset.val < 2 ^ k,
        (index k).symm ⟨block * s + offset.val, h⟩ = (fun i => x (Fin.castAdd d i)) ∧
          pattern offset = true := by
  simp only [left, decide_eq_true_eq]
  apply exists_congr
  intro offset
  by_cases h : block * s + offset.val < 2 ^ k <;>
    cases hp : pattern offset <;> simp [leftRow, hp, h, minterm, eq_comm]

private theorem right_eq_true (f : BooleanFunction (k + d)) (block : ℕ) (pattern : Assignment s)
    (x : Assignment (k + d)) :
    right f block pattern x = true ↔ column f block (fun i => x (Fin.natAdd k i)) = pattern := by
  simp [right, support, minterm, eq_comm]

private def table (f : BooleanFunction (k + d)) (s : ℕ) : BooleanFunction (k + d) :=
  fun x => decide (∃ pair : Fin (2 ^ k / s + 1) × Assignment s,
    (left pair.1.val pair.2 x && right f pair.1.val pair.2 x) = true)

private theorem table_eq (f : BooleanFunction (k + d)) (hs : 0 < s) : table f s = f := by
  funext x
  apply Bool.eq_iff_iff.mpr
  simp only [table, decide_eq_true_eq, Prod.exists, Bool.and_eq_true,
    left_eq_true, right_eq_true]
  constructor
  · rintro ⟨block, pattern, ⟨offset, hrow, haddress, hbit⟩, hpattern⟩
    rw [← hpattern] at hbit
    simpa [column, hrow, haddress, Fin.append_castAdd_natAdd] using hbit
  · intro hx
    let address := index k (fun i => x (Fin.castAdd d i))
    let block : Fin (2 ^ k / s + 1) :=
      ⟨address.val / s, Nat.lt_succ_of_le (Nat.div_le_div_right address.isLt.le)⟩
    let offset : Fin s := ⟨address.val % s, Nat.mod_lt _ hs⟩
    have hrow : block.val * s + offset.val = address.val := Nat.div_add_mod' _ _
    have hvalid : block.val * s + offset.val < 2 ^ k := hrow ▸ address.isLt
    have haddress : (index k).symm ⟨block.val * s + offset.val, hvalid⟩ =
        (fun i => x (Fin.castAdd d i)) := by
      rw [show (⟨block.val * s + offset.val, hvalid⟩ : Fin (2 ^ k)) = address by
        exact Fin.ext hrow]
      exact (index k).symm_apply_apply _
    refine ⟨block, column f block.val (fun i => x (Fin.natAdd k i)),
      ⟨offset, hvalid, haddress, ?_⟩, rfl⟩
    simpa [column, hvalid, haddress, Fin.append_castAdd_natAdd] using hx

/-- Gate budget for `k` address bits, `d` data bits, and blocks of `s` rows.
The terms account for minterms, block-pattern pairs, and a final constant.
The block count allows a partial last block, or an empty extra block when `s ∣ 2 ^ k`. -/
def bound (k d s : ℕ) : ℕ :=
  (2 ^ k + 2 ^ d) * (2 * (k + d) + 1) +
    (2 ^ k / s + 1) * (2 ^ s * (2 * s + 4) + 2 ^ d) + 1

/-- Synthesize any Boolean function within Lupanov's finite gate budget. -/
theorem synthesis (f : BooleanFunction (k + d)) (hs : 0 < s) :
    Synthesis (inputs (k + d)) {f} (bound k d s) := by
  have hpair (pair : Fin (2 ^ k / s + 1) × Assignment s) :=
    (left_synthesis (d := d) pair.1.val pair.2).and (right_synthesis f pair.1.val pair.2)
  have h := Synthesis.exists_mem Finset.univ
    (fun pair : Fin (2 ^ k / s + 1) × Assignment s =>
      fun x => left pair.1.val pair.2 x && right f pair.1.val pair.2 x)
    (fun pair => (2 * s + 1) + ((support f pair.1.val pair.2).card + 1) + 1)
    (fun pair _ => hpair pair)
  have hsum : (∑ pair : Fin (2 ^ k / s + 1) × Assignment s,
      ((2 * s + 1) + ((support f pair.1.val pair.2).card + 1) + 1 + 1)) =
        (2 ^ k / s + 1) * (2 ^ s * (2 * s + 4) + 2 ^ d) := by
    simp_rw [show ∀ a : ℕ, (2 * s + 1) + (a + 1) + 1 + 1 = (2 * s + 4) + a by omega]
    simp [Fintype.sum_prod_type, Finset.sum_add_distrib, support_card_sum, Nat.mul_add,
      Nat.mul_assoc]
  simp only [Finset.mem_univ, true_and, hsum] at h
  change Synthesis _ {table f s} _ at h
  rw [table_eq f hs] at h
  simpa [bound, Nat.add_assoc] using minterms_synthesis.comp
    (h.mono Set.subset_union_right Set.Subset.rfl le_rfl)

end
end Cslib.Circuits.Boolean.Lupanov
