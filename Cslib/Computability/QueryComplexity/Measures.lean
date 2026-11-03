/-
Copyright (c) 2026 Vignesh Karri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vignesh Karri
-/

module

public import Cslib.Computability.QueryComplexity.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Boolean function complexity measures

Sensitivity `s(f)`, block sensitivity `bs(f)` and certificate complexity `C(f)`, together with
the chain `s(f) ≤ bs(f) ≤ C(f)`. Notation follows [AroraBarak09]; the pointwise measures
`s(f, x)`, `bs(f, x)`, `C(f, x)` are those of [Jukna, Section 14.3][Jukna2012].

## Main definitions

- `BitString.sensitivity`: `s(f)`, the maximum over inputs of the number of sensitive coordinates.
- `blockSensitivity`: `bs(f)`, the maximum over inputs of the maximum number of disjoint sensitive
  blocks.
- `IsCertificate`: a set of coordinates whose values at `x` pin down `f x`, as in
  [Jukna, Section 14.3][Jukna2012].
- `Forces`: a partial assignment forces the value `b`, as in [BuhrmanDeWolf2002]. At a fixed input
  an assignment consistent with `x` is determined by its support, so the pointwise measure needs no
  bit values.
- `certificateComplexity`: `C(f)`, the maximum over inputs of the smallest certificate size.

## Main results

- `sensitivity_le_blockSensitivity`: `s(f) ≤ bs(f)`.
- `blockSensitivity_le_certificateComplexity`: `bs(f) ≤ C(f)`.
- `isCertificate_iff_forces_restrict`, `forces_iff_isCertificate_support`: `IsCertificate` and
  `Forces` agree at a fixed input.
- `certificateComplexityAt_eq_inf'_size`: `C(f, x)` is the minimum size of a forcing assignment
  consistent with `x`.
- `|B| ≤ s(f)` for a minimal sensitive block `B`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09],
  Section 12.2 (Certificate Complexity) and Section 12.5.1 (Sensitivity).
* [H. Buhrman, R. de Wolf, *Complexity measures and decision tree complexity:
  a survey*][BuhrmanDeWolf2002]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012], Section 14.3.
-/

@[expose] public section

namespace Cslib

variable {n : ℕ}

namespace BitString

/-! ## Sensitivity -/

/-- Coordinate `i` is sensitive for `f` at `x` when flipping it flips `f`. -/
def IsSensitiveCoord (f : BooleanFunction n) (x : BitString n) (i : Fin n) : Prop :=
  f (Function.update x i (!x i)) ≠ f x

instance (f : BooleanFunction n) (x : BitString n) : DecidablePred (IsSensitiveCoord f x) :=
  fun i => inferInstanceAs (Decidable (f (Function.update x i (!x i)) ≠ f x))

/-- The set of coordinates sensitive for `f` at `x`. -/
def sensitiveCoords (f : BooleanFunction n) (x : BitString n) : Finset (Fin n) :=
  Finset.univ.filter (IsSensitiveCoord f x)

/-- The bridge between the predicate and the `Finset` it cuts out. -/
@[simp]
lemma mem_sensitiveCoords {f : BooleanFunction n} {x : BitString n} {i : Fin n} :
    i ∈ sensitiveCoords f x ↔ IsSensitiveCoord f x i := by
  simp [sensitiveCoords]

/-- The number of sensitive coordinates in input `x`, usually denoted `s(f, x)`. -/
def sensitivityAt (f : BooleanFunction n) (x : BitString n) : ℕ := (sensitiveCoords f x).card

/-- The maximum sensitivity over all inputs, denoted `s(f)`. -/
def sensitivity (f : BooleanFunction n) : ℕ := Finset.univ.sup (sensitivityAt f)

/-- Lower-bound rule for `s(f, x)`: exhibit a set of sensitive coordinates. -/
lemma card_le_sensitivityAt {f : BooleanFunction n} {x : BitString n} {S : Finset (Fin n)}
    (h : ∀ i ∈ S, IsSensitiveCoord f x i) : S.card ≤ sensitivityAt f x := by
  apply Finset.card_le_card
  simpa [Finset.subset_iff] using h

/-- The sensitivity at a single input is at most the sensitivity of `f`: `s(f, x) ≤ s(f)`. -/
lemma sensitivityAt_le_sensitivity (f : BooleanFunction n) (x : BitString n) :
    sensitivityAt f x ≤ sensitivity f :=
  Finset.le_sup (Finset.mem_univ x)

/-- Lower-bound rule for `s(f)`: sensitive coordinates at any input suffice. -/
lemma card_le_sensitivity_of_forall_isSensitiveCoord {f : BooleanFunction n} {x : BitString n}
    {S : Finset (Fin n)} (h : ∀ i ∈ S, IsSensitiveCoord f x i) : S.card ≤ sensitivity f :=
  (card_le_sensitivityAt h).trans (sensitivityAt_le_sensitivity f x)

/-- `s(f, x) ≤ n`: there are only `n` coordinates. -/
theorem sensitivityAt_le_card (f : BooleanFunction n) (x : BitString n) : sensitivityAt f x ≤ n :=
  (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)

/-- `s(f) ≤ n`. -/
theorem sensitivity_le_card (f : BooleanFunction n) : sensitivity f ≤ n :=
  Finset.sup_le fun x _ => sensitivityAt_le_card f x

end BitString

namespace QueryComplexity

open BitString

/-! ## Block sensitivity -/

/-- Block `B` is sensitive for `f` at `x` when flipping all bits of `B` flips `f`. -/
def IsSensitiveBlock (f : BooleanFunction n) (x : BitString n) (B : Block n) : Prop :=
  f (flipBlock B x) ≠ f x

instance (f : BooleanFunction n) (x : BitString n) (B : Block n) :
    Decidable (IsSensitiveBlock f x B) :=
  inferInstanceAs (Decidable (f (flipBlock B x) ≠ f x))

/-- Every member flips `f`, and the members are pairwise disjoint. -/
def IsSensitiveFamily (f : BooleanFunction n) (x : BitString n) (F : Finset (Block n)) : Prop :=
  (∀ B ∈ F, IsSensitiveBlock f x B) ∧ (F : Set (Block n)).PairwiseDisjoint id

instance (f : BooleanFunction n) (x : BitString n) (F : Finset (Block n)) :
    Decidable (IsSensitiveFamily f x F) :=
  decidable_of_iff ((∀ B ∈ F, IsSensitiveBlock f x B) ∧
    ∀ P ∈ F, ∀ Q ∈ F, P ≠ Q → Disjoint P Q) Iff.rfl

/-- All sensitive families. -/
def sensitiveFamilies (f : BooleanFunction n) (x : BitString n) : Finset (Finset (Block n)) :=
  Finset.univ.filter (IsSensitiveFamily f x)

@[simp]
lemma mem_sensitiveFamilies {f : BooleanFunction n} {x : BitString n} {F : Finset (Block n)} :
    F ∈ sensitiveFamilies f x ↔ IsSensitiveFamily f x F := by
  simp [sensitiveFamilies]

/-- The block sensitivity of `f` at `x`: the largest number of pairwise disjoint blocks of
coordinates such that flipping every coordinate of any one block flips `f`. Usually denoted
`bs(f, x)`. -/
def blockSensitivityAt (f : BooleanFunction n) (x : BitString n) : ℕ :=
  (sensitiveFamilies f x).sup Finset.card

/-- The maximum block sensitivity over all inputs, denoted `bs(f)`. -/
def blockSensitivity (f : BooleanFunction n) : ℕ := Finset.univ.sup (blockSensitivityAt f)

/-- Lower-bound rule for `bs(f, x)`: exhibit one sensitive family. -/
lemma card_le_blockSensitivityAt {f : BooleanFunction n} {x : BitString n} {F : Finset (Block n)}
    (h : IsSensitiveFamily f x F) : F.card ≤ blockSensitivityAt f x :=
  Finset.le_sup (mem_sensitiveFamilies.mpr h)

/-- The block sensitivity at a single input is at most that of `f`: `bs(f, x) ≤ bs(f)`. -/
lemma blockSensitivityAt_le_blockSensitivity (f : BooleanFunction n) (x : BitString n) :
    blockSensitivityAt f x ≤ blockSensitivity f :=
  Finset.le_sup (Finset.mem_univ x)

/-- Lower-bound rule for `bs(f)`. -/
lemma card_le_blockSensitivity {f : BooleanFunction n} {x : BitString n} {F : Finset (Block n)}
    (h : IsSensitiveFamily f x F) : F.card ≤ blockSensitivity f :=
  (card_le_blockSensitivityAt h).trans (blockSensitivityAt_le_blockSensitivity f x)

/-! ## Sensitive singletons -/

/-- A singleton block is sensitive if and only if its coordinate is. -/
@[simp]
lemma isSensitiveBlock_singleton {f : BooleanFunction n} {x : BitString n} {i : Fin n} :
    IsSensitiveBlock f x {i} ↔ IsSensitiveCoord f x i := by
  rw [IsSensitiveBlock, IsSensitiveCoord, flipBlock_singleton]

/-! ## `s(f) ≤ bs(f)` -/

/-- One block per sensitive coordinate. -/
def singletonFamily (f : BooleanFunction n) (x : BitString n) : Finset (Block n) :=
  (sensitiveCoords f x).image (fun i => ({i} : Block n))

/-- Membership in the singleton family: one block per sensitive coordinate. -/
@[simp]
lemma mem_singletonFamily {f : BooleanFunction n} {x : BitString n} {B : Block n} :
    B ∈ singletonFamily f x ↔ ∃ i, IsSensitiveCoord f x i ∧ {i} = B := by
  simp [singletonFamily]

/-- The singleton family has one block per sensitive coordinate, so `s(f, x)` of them. -/
@[simp]
lemma card_singletonFamily {f : BooleanFunction n} {x : BitString n} :
    (singletonFamily f x).card = sensitivityAt f x :=
  Finset.card_image_of_injective _ Finset.singleton_injective

/-- Singletons of distinct sensitive coordinates do form a sensitive family: each
flips `f`, and distinct singletons are disjoint. -/
lemma isSensitiveFamily_singletonFamily {f : BooleanFunction n} {x : BitString n} :
    IsSensitiveFamily f x (singletonFamily f x) := by
  constructor
  · rintro B hB
    obtain ⟨i, hi, rfl⟩ := mem_singletonFamily.mp hB
    exact isSensitiveBlock_singleton.mpr hi
  · rintro P hP Q hQ hPQ
    obtain ⟨i, -, rfl⟩ := mem_singletonFamily.mp hP
    obtain ⟨j, -, rfl⟩ := mem_singletonFamily.mp hQ
    exact Finset.disjoint_singleton.mpr fun h => hPQ (by rw [h])

/-- Pointwise: `s(f, x) ≤ bs(f, x)`. -/
theorem sensitivityAt_le_blockSensitivityAt (f : BooleanFunction n) (x : BitString n) :
    sensitivityAt f x ≤ blockSensitivityAt f x :=
  card_singletonFamily ▸ card_le_blockSensitivityAt isSensitiveFamily_singletonFamily

/-- Every sensitive coordinate is a sensitive block of size one, so `s(f) ≤ bs(f)`. -/
theorem sensitivity_le_blockSensitivity (f : BooleanFunction n) :
    sensitivity f ≤ blockSensitivity f :=
  Finset.sup_mono_fun fun x _ => sensitivityAt_le_blockSensitivityAt f x

/-! ## Minimal sensitive blocks -/

/-- `B` is sensitive, and no proper subset of `B` is sensitive. -/
def IsMinimalSensitiveBlock (f : BooleanFunction n) (x : BitString n) (B : Block n) : Prop :=
  IsSensitiveBlock f x B ∧ ∀ C ⊂ B, ¬ IsSensitiveBlock f x C

instance (f : BooleanFunction n) (x : BitString n) (B : Block n) :
    Decidable (IsMinimalSensitiveBlock f x B) :=
  inferInstanceAs (Decidable (IsSensitiveBlock f x B ∧ ∀ C ⊂ B, ¬ IsSensitiveBlock f x C))

namespace IsMinimalSensitiveBlock

variable {f : BooleanFunction n} {x : BitString n} {B : Block n} {i : Fin n}

/-- Dropping any coordinate from a minimal sensitive block breaks sensitivity. -/
lemma not_isSensitiveBlock_erase (hB : IsMinimalSensitiveBlock f x B) (hi : i ∈ B) :
    ¬ IsSensitiveBlock f x (B.erase i) :=
  hB.2 _ (Finset.erase_ssubset hi)

/-- Every coordinate of a minimal sensitive block is sensitive at the input which
has the minimal sensitive block flipped. -/
lemma isSensitiveCoord_flipBlock (hB : IsMinimalSensitiveBlock f x B) (hi : i ∈ B) :
    IsSensitiveCoord f (flipBlock B x) i := by
  unfold IsSensitiveCoord
  rw [flipBlock_apply_of_mem hi, Bool.not_not, ← flipBlock_erase hi,
    not_not.mp (hB.not_isSensitiveBlock_erase hi)]
  exact Ne.symm hB.1

/-- `|B| ≤ s(f)` for a minimal sensitive block `B`. -/
theorem card_le_sensitivity (hB : IsMinimalSensitiveBlock f x B) : B.card ≤ sensitivity f :=
  card_le_sensitivity_of_forall_isSensitiveCoord fun _ hi => hB.isSensitiveCoord_flipBlock hi

end IsMinimalSensitiveBlock

/-! ## Certificates

A certificate for `x` is a set of coordinates whose values at `x` already determine `f x`
[Jukna, Section 14.3][Jukna2012]. The survey [BuhrmanDeWolf2002] instead works with partial
assignments that force a value; `Forces` keeps that in general form, with the forced value `b` a
parameter, and the two views agree at a fixed input.
-/

/-- `S` is a certificate for `f` at `x`: every input agreeing with `x` on `S` takes the same
value, so `f x` can be read off from the bits of `x` in `S`. -/
def IsCertificate (f : BooleanFunction n) (x : BitString n) (S : Finset (Fin n)) : Prop :=
  ∀ y, (∀ i ∈ S, y i = x i) → f y = f x

instance (f : BooleanFunction n) (x : BitString n) (S : Finset (Fin n)) :
    Decidable (IsCertificate f x S) :=
  inferInstanceAs (Decidable (∀ y, (∀ i ∈ S, y i = x i) → f y = f x))

/-- `C` forces the value `b`: everything consistent with `C` has `f = b`. -/
def Forces (f : BooleanFunction n) (C : PartialAssignment n) (b : Bool) : Prop :=
  ∀ x, Agrees C x → f x = b

instance (f : BooleanFunction n) (C : PartialAssignment n) (b : Bool) :
    Decidable (Forces f C b) :=
  inferInstanceAs (Decidable (∀ x, Agrees C x → f x = b))

/-- `S` is a certificate for `x` if and only if `x` restricted to `S` forces `f x`. -/
theorem isCertificate_iff_forces_restrict {f : BooleanFunction n} {x : BitString n}
    {S : Finset (Fin n)} : IsCertificate f x S ↔ Forces f (restrict x S) (f x) := by
  simp only [IsCertificate, Forces, agrees_restrict_iff]

/-- A partial assignment consistent with `x` forces `f x` if and only if its support is a
certificate for `x`. -/
theorem forces_iff_isCertificate_support {f : BooleanFunction n} {x : BitString n}
    {C : PartialAssignment n} (hC : Agrees C x) :
    Forces f C (f x) ↔ IsCertificate f x (support C) := by
  rw [isCertificate_iff_forces_restrict, ← eq_restrict_support hC]

/-- Reading every coordinate of `x` is a certificate. -/
lemma isCertificate_univ (f : BooleanFunction n) (x : BitString n) :
    IsCertificate f x Finset.univ :=
  fun _ hy => congrArg f (funext fun i => hy i (Finset.mem_univ i))

/-- There is always a certificate, so `C(f, x)` is a minimum over a non-empty set. -/
lemma filter_isCertificate_nonempty (f : BooleanFunction n) (x : BitString n) :
    (Finset.univ.filter (IsCertificate f x)).Nonempty :=
  ⟨Finset.univ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, isCertificate_univ f x⟩⟩

/-- The fewest coordinates of `x` that pin down the value of `f`, denoted `C(f, x)`. -/
def certificateComplexityAt (f : BooleanFunction n) (x : BitString n) : ℕ :=
  (Finset.univ.filter (IsCertificate f x)).inf' (filter_isCertificate_nonempty f x) Finset.card

/-- Upper-bound rule for `C(f, x)`: exhibit one certificate. -/
lemma certificateComplexityAt_le {f : BooleanFunction n} {x : BitString n} {S : Finset (Fin n)}
    (h : IsCertificate f x S) : certificateComplexityAt f x ≤ S.card :=
  Finset.inf'_le _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)

/-- Lower-bound rule for `C(f, x)`: a bound that holds for every certificate. -/
lemma le_certificateComplexityAt {f : BooleanFunction n} {x : BitString n} {k : ℕ}
    (h : ∀ S, IsCertificate f x S → k ≤ S.card) : k ≤ certificateComplexityAt f x :=
  Finset.le_inf' _ _ fun _ hS => h _ (Finset.mem_filter.mp hS).2

/-- Some certificate for `x` has exactly `C(f, x)` coordinates. -/
theorem exists_isCertificate_card_eq (f : BooleanFunction n) (x : BitString n) :
    ∃ S, IsCertificate f x S ∧ S.card = certificateComplexityAt f x := by
  obtain ⟨S, hS, h⟩ := Finset.exists_mem_eq_inf' (filter_isCertificate_nonempty f x) Finset.card
  exact ⟨S, (Finset.mem_filter.mp hS).2, h.symm⟩

/-! ## Certificates as partial assignments

At a fixed input a forcing assignment carries no information beyond the coordinates it reads:
`Agrees C x` forces `C i = some (x i)` on the support and `none` elsewhere. So `C(f, x)` over
coordinate sets is also the minimum size of a forcing assignment consistent with `x`.
-/

/-- Partial assignments consistent with `x` that force `f x`. -/
def forcingAssignments (f : BooleanFunction n) (x : BitString n) :
    Finset (PartialAssignment n) :=
  Finset.univ.filter (fun C => Agrees C x ∧ Forces f C (f x))

@[simp]
lemma mem_forcingAssignments {f : BooleanFunction n} {x : BitString n}
    {C : PartialAssignment n} :
    C ∈ forcingAssignments f x ↔ Agrees C x ∧ Forces f C (f x) := by
  simp [forcingAssignments]

/-- Reading off all of `x` forces `f x`. -/
lemma ofBitString_mem_forcingAssignments (f : BooleanFunction n) (x : BitString n) :
    ofBitString x ∈ forcingAssignments f x :=
  mem_forcingAssignments.mpr ⟨agrees_ofBitString_iff.mpr rfl, fun _ hy => by
    rw [agrees_ofBitString_iff.mp hy]⟩

/-- There is always a forcing assignment consistent with `x`. -/
lemma forcingAssignments_nonempty (f : BooleanFunction n) (x : BitString n) :
    (forcingAssignments f x).Nonempty :=
  ⟨ofBitString x, ofBitString_mem_forcingAssignments f x⟩

/-- `C(f, x)` over coordinate sets is the minimum size of a forcing assignment consistent with
`x`, the definition of [BuhrmanDeWolf2002]. -/
theorem certificateComplexityAt_eq_inf'_size (f : BooleanFunction n) (x : BitString n) :
    certificateComplexityAt f x =
      (forcingAssignments f x).inf' (forcingAssignments_nonempty f x) size := by
  refine le_antisymm (Finset.le_inf' _ _ fun C hC => ?_)
    (le_certificateComplexityAt fun S hS => ?_)
  · obtain ⟨hA, hforce⟩ := mem_forcingAssignments.mp hC
    exact certificateComplexityAt_le ((forces_iff_isCertificate_support hA).mp hforce)
  · have hmem : restrict x S ∈ forcingAssignments f x :=
      mem_forcingAssignments.mpr ⟨agrees_restrict_iff.mpr fun _ _ => rfl,
        isCertificate_iff_forces_restrict.mp hS⟩
    exact (Finset.inf'_le size hmem).trans_eq (by simp [size])

/-- The maximum over all inputs of the smallest certificate size, denoted `C(f)`. -/
def certificateComplexity (f : BooleanFunction n) : ℕ :=
  Finset.univ.sup (certificateComplexityAt f)

/-- The certificate complexity at a single input is at most that of `f`: `C(f, x) ≤ C(f)`. -/
lemma certificateComplexityAt_le_certificateComplexity (f : BooleanFunction n)
    (x : BitString n) : certificateComplexityAt f x ≤ certificateComplexity f :=
  Finset.le_sup (Finset.mem_univ x)

/-- `C(f, x) ≤ n`: reading every coordinate pins down `f`. -/
theorem certificateComplexityAt_le_card (f : BooleanFunction n) (x : BitString n) :
    certificateComplexityAt f x ≤ n :=
  (certificateComplexityAt_le (isCertificate_univ f x)).trans_eq (by simp)

/-- `C(f) ≤ n`. -/
theorem certificateComplexity_le_card (f : BooleanFunction n) : certificateComplexity f ≤ n :=
  Finset.sup_le fun x _ => certificateComplexityAt_le_card f x

/-! ## `bs(f) ≤ C(f)`

A certificate for `x` must meet every block of a sensitive family. The blocks are pairwise
disjoint, so a family has at most `|S|` members.
-/

/-- A certificate must contain at least one coordinate of every sensitive block. -/
theorem sensitiveBlock_inter_nonempty {f : BooleanFunction n} {x : BitString n} {B : Block n}
    (hB : IsSensitiveBlock f x B) {S : Finset (Fin n)} (hS : IsCertificate f x S) :
    (B ∩ S).Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty, Finset.eq_empty_iff_forall_notMem] at h
  refine hB (hS _ fun i hi => ?_)
  exact flipBlock_apply_of_notMem fun hiB => h i (Finset.mem_inter.mpr ⟨hiB, hi⟩)

/-- A certificate is at least as large as any sensitive family. -/
lemma card_le_card_of_isSensitiveFamily {f : BooleanFunction n} {x : BitString n}
    {F : Finset (Block n)} {S : Finset (Fin n)}
    (hF : IsSensitiveFamily f x F) (hS : IsCertificate f x S) : F.card ≤ S.card :=
  (Finset.card_le_card_biUnion
      (fun _ hP _ hQ hPQ => Disjoint.mono Finset.inter_subset_left Finset.inter_subset_left
        (hF.2 hP hQ hPQ))
      (fun B hB => sensitiveBlock_inter_nonempty (hF.1 B hB) hS)).trans
    (Finset.card_le_card (Finset.biUnion_subset.mpr fun _ _ => Finset.inter_subset_right))

/-- Pointwise: `bs(f, x) ≤ C(f, x)`. -/
theorem blockSensitivityAt_le_certificateComplexityAt (f : BooleanFunction n)
    (x : BitString n) : blockSensitivityAt f x ≤ certificateComplexityAt f x :=
  Finset.sup_le fun _ hF => le_certificateComplexityAt fun _ hS =>
    card_le_card_of_isSensitiveFamily (mem_sensitiveFamilies.mp hF) hS

/-- Every block of a sensitive family meets every certificate, so `bs(f) ≤ C(f)`. -/
theorem blockSensitivity_le_certificateComplexity (f : BooleanFunction n) :
    blockSensitivity f ≤ certificateComplexity f :=
  Finset.sup_mono_fun fun x _ =>
    blockSensitivityAt_le_certificateComplexityAt f x

/-- `bs(f, x) ≤ n`. -/
theorem blockSensitivityAt_le_card (f : BooleanFunction n) (x : BitString n) :
    blockSensitivityAt f x ≤ n :=
  (blockSensitivityAt_le_certificateComplexityAt f x).trans (certificateComplexityAt_le_card f x)

/-- `bs(f) ≤ n`. -/
theorem blockSensitivity_le_card (f : BooleanFunction n) : blockSensitivity f ≤ n :=
  Finset.sup_le fun x _ => blockSensitivityAt_le_card f x

end QueryComplexity

end Cslib
