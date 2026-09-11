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

This file is the finite, parametrised core of Lupanov's upper bound. Its purpose is to give a
gate budget `bound k d s` that is valid for every Boolean function on `k + d` inputs and every
positive block size `s`, and to prove (`synthesis`) that the budget suffices. The asymptotic file
`Lupanov.lean` then chooses `k`, `d`, and `s` as functions of `n` and shows that the budget is
`(1 + ε) 2 ^ n / n`. No asymptotics happen here.

## Why not the disjunctive normal form?

Writing `f` as the disjunction of its true minterms uses up to `2 ^ n` minterms of `n`
literals each, so roughly `n 2 ^ n` gates. The waste is that nothing is shared between
minterms. Lupanov's construction shares almost everything.

## The picture

Split the `n = k + d` inputs into `k` *address* bits and `d` *data* bits, and view the truth
table of `f` as a `2 ^ k × 2 ^ d` matrix: row `a` is an address assignment, column `b` is a
data assignment, and the entry is `f (a ++ b)`. Cut the rows into blocks of `s` consecutive
rows. Inside one block every column is a bit string of length `s`, its *pattern* in that
block; there are only `2 ^ s` possible patterns, however many columns there are.

For each block `B` and pattern `v` define two functions:

* `left B v`, of the address bits only: true at `a` when row `a` lies in `B` and `v` has a
  `1` at the position of `a` within `B`;
* `right f B v`, of the data bits only: true at `b` when column `b` has pattern `v` in `B`.

Both are functions of the full input that ignore the other half of it. Then
`left B v a ∧ right f B v b` holds exactly when `a` lies in `B`, `v` is the pattern of
column `b` inside `B`, and the entry `f (a ++ b)` is `true`. So `f` is the disjunction over
all pairs `(B, v)` of `left B v ∧ right f B v` (`table_eq`).

## Counting gates

All `2 ^ k` address minterms and `2 ^ d` data minterms are built once and shared. Each
`left B v` is a disjunction of at most `s` address minterms, so it costs `O(s)` gates, and
there are `(2 ^ k / s + 1) · 2 ^ s` of them. Each `right f B v` is a disjunction of data
minterms, one per column with pattern `v`; the columns of a block are partitioned by their
patterns (`support_card_sum`), so all the `right f B v` of one block together cost about
`2 ^ d` gates. Summing over blocks, the dominant contribution is

  `(2 ^ k / s) · 2 ^ d = 2 ^ n / s`.

For the parameters chosen in `Lupanov.lean` the remaining terms are of lower order, and
`s ≈ n` makes this `2 ^ n / n`. The exact expression is `bound`.

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

/-! ### Minterms -/

/-- An assignment to `k` Boolean variables. Address assignments index the rows of the truth
table and data assignments index its columns. -/
private abbrev Assignment (k : ℕ) := Fin k → Bool

/-- Number the address assignments as rows `0, …, 2 ^ k - 1`. Any bijection will do, so we
take an arbitrary one; this is what makes the section noncomputable. -/
private def index (k : ℕ) : Assignment k ≃ Fin (2 ^ k) :=
  Fintype.equivOfCardEq (by simp)

/-- The minterm testing that the address bits equal `a` (`.inl a`) or that the data bits
equal `b` (`.inr b`). Both kinds are built once and shared by every block. -/
private def minterm : Assignment k ⊕ Assignment d → BooleanFunction (k + d)
  | .inl a => fun x => decide ((fun i => x (Fin.castAdd d i)) = a)
  | .inr b => fun x => decide ((fun i => x (Fin.natAdd k i)) = b)

/-- Build every address and data minterm from the inputs. Each costs `2 (k + d) + 1` gates
by `synthesis_minterm`. -/
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

/-- Once the minterms have been built, each of them is free. -/
private theorem minterm_available (a : Assignment k ⊕ Assignment d) :
    Synthesis (Set.range minterm) {minterm a} 0 :=
  Synthesis.of_subset (by rintro _ rfl; exact ⟨a, rfl⟩)

/-! ### The block decomposition

Rows `block * s, …, block * s + s - 1` form block number `block`. The final block may be
partial, and when `s ∣ 2 ^ k` there is an empty extra block; rows past `2 ^ k` are read as
`false` throughout. -/

/-- The pattern of column `data` inside block `block`: the `s` entries of the truth table in
the block's rows, read down the column. -/
private def column (f : BooleanFunction (k + d)) (block : ℕ) (data : Assignment d) :
    Assignment s :=
  fun offset => if h : block * s + offset.val < 2 ^ k then
    f (Fin.append ((index k).symm ⟨block * s + offset.val, h⟩) data) else false

/-- The contribution of the row at `offset` within `block` to `left`: the address minterm of
that row when `pattern` is `1` there, and the constant `false` otherwise. -/
private def leftRow (block : ℕ) (pattern : Assignment s) (offset : Fin s) :
    BooleanFunction (k + d) :=
  if pattern offset then
    if h : block * s + offset.val < 2 ^ k then
      minterm (.inl ((index k).symm ⟨block * s + offset.val, h⟩))
    else fun _ => false
  else fun _ => false

/-- The address-only function of a block and pattern: true when the address lies in the
block, at an offset where the pattern is `1`. -/
private def left (block : ℕ) (pattern : Assignment s) : BooleanFunction (k + d) :=
  fun x => decide (∃ offset, leftRow (d := d) block pattern offset x = true)

/-- `left` is true exactly at inputs whose address is a row of the block, at an offset where
the pattern is `1`. -/
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

/-- The columns whose pattern inside `block` is `pattern`. For a fixed block, these sets
partition the columns. -/
private def support (f : BooleanFunction (k + d)) (block : ℕ) (pattern : Assignment s) :
    Finset (Assignment d) := Finset.univ.filter fun data => column f block data = pattern

/-- The data-only function of a block and pattern: true when the data bits name a column
whose pattern inside the block is `pattern`. -/
private def right (f : BooleanFunction (k + d)) (block : ℕ) (pattern : Assignment s) :
    BooleanFunction (k + d) :=
  fun x => decide (∃ data ∈ support f block pattern, minterm (.inr data) x = true)

/-- `right` is true exactly at inputs whose data bits name a column with the given pattern
inside the block. -/
private theorem right_eq_true (f : BooleanFunction (k + d)) (block : ℕ) (pattern : Assignment s)
    (x : Assignment (k + d)) :
    right f block pattern x = true ↔ column f block (fun i => x (Fin.natAdd k i)) = pattern := by
  simp [right, support, minterm, eq_comm]

/-! ### Gate counts -/

/-- The supports of one block partition the `2 ^ d` columns. This is why all the `right`
parts of a block together cost only about `2 ^ d` gates. -/
private theorem support_card_sum (f : BooleanFunction (k + d)) (block : ℕ) :
    ∑ pattern : Assignment s, (support f block pattern).card = 2 ^ d := by
  simpa [support] using (Finset.card_eq_sum_card_fiberwise
    (s := Finset.univ) (t := Finset.univ) (f := column (s := s) f block) (by simp)).symm

/-- A `left` part costs `2 s + 1` gates once the minterms are available: at most one gate per
row (a shared minterm costs nothing, a padding row needs a constant), one OR per row, and one
constant for the empty disjunction. -/
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

/-- A `right` part costs one OR per column in its support, plus one constant for the empty
disjunction, once the minterms are available. -/
private theorem right_synthesis (f : BooleanFunction (k + d)) (block : ℕ)
    (pattern : Assignment s) :
    Synthesis (Set.range minterm) {right f block pattern} ((support f block pattern).card + 1) := by
  change Synthesis (Set.range (minterm (k := k) (d := d)))
    {fun x => decide (∃ data ∈ support f block pattern, minterm (.inr data) x = true)} _
  simpa using Synthesis.exists_mem (support f block pattern)
    (fun data => minterm (.inr data)) (fun _ => 0)
    (fun data _ => minterm_available (.inr data))

/-! ### Correctness -/

/-- The disjunction over all blocks and patterns of `left ∧ right`. Block numbers range over
`2 ^ k / s + 1` values to include a partial final block. -/
private def table (f : BooleanFunction (k + d)) (s : ℕ) : BooleanFunction (k + d) :=
  fun x => decide (∃ pair : Fin (2 ^ k / s + 1) × Assignment s,
    (left pair.1.val pair.2 x && right f pair.1.val pair.2 x) = true)

/-- The block decomposition reconstructs `f`. At an input `a ++ b` with `f (a ++ b) = true`,
the witnessing pair is the block containing row `a` and the pattern of column `b` in that
block. -/
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

/-! ### The bound -/

/-- Gate budget for `k` address bits, `d` data bits, and blocks of `s` rows, as spent by
`synthesis`. In order: the shared minterms; then for each of the `2 ^ k / s + 1` blocks
(a partial final block, or an empty extra block when `s ∣ 2 ^ k`), `2 s + 4` gates per
pattern, namely `2 s + 1` for its `left` part, the constant starting its `right` part, the
conjunction of the two, and the OR into the running disjunction, plus `2 ^ d` gates in total
for the ORs inside the `right` parts of the block, one per column; and one constant for the
empty outer disjunction. The leading term is `(2 ^ k / s) · 2 ^ d ≈ 2 ^ n / s`. -/
def bound (k d s : ℕ) : ℕ :=
  (2 ^ k + 2 ^ d) * (2 * (k + d) + 1) +
    (2 ^ k / s + 1) * (2 ^ s * (2 * s + 4) + 2 ^ d) + 1

/-- Every Boolean function on `k + d` inputs can be built from the input projections within
`bound k d s` gates: build all minterms, then the disjunction over block-pattern pairs of
`left ∧ right`, which equals `f` by `table_eq`. -/
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
