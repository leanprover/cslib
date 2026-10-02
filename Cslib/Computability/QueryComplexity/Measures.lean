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
the chain `s(f) ≤ bs(f) ≤ C(f)`. Notation follows [AroraBarak09].

## Main definitions

- `sensitivity`: `s(f)`, the maximum over inputs of the number of sensitive coordinates.
- `blockSensitivity`: `bs(f)`, the maximum over inputs of the maximum number of disjoint sensitive
  blocks.
- `IsCertificate`: a partial assignment forces the value `b`, as in [BuhrmanDeWolf2002].
- `Fixes`: a set of coordinates pins down `f` at `x`, as in [AroraBarak09]. At a fixed input an
  assignment consistent with `x` is determined by its support, so the pointwise measure needs no
  bit values.
- `certificateComplexity`: `C(f)`, the maximum over inputs of the smallest certificate size.

## Main results

- `sensitivity_le_blockSensitivity`: `s(f) ≤ bs(f)`.
- `blockSensitivity_le_certificateComplexity`: `bs(f) ≤ C(f)`.
- `|B| ≤ s(f)` for a minimal sensitive block `B`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09],
  Section 12.2 (Certificate Complexity) and Section 12.5.1 (Sensitivity).
* [H. Buhrman, R. de Wolf, *Complexity measures and decision tree complexity:
  a survey*][BuhrmanDeWolf2002]
-/

@[expose] public section

namespace Cslib.QueryComplexity

variable {n : ℕ}

/-! ## Sensitivity -/

/-- Coordinate `i` is sensitive for `f` at `x` when flipping it flips `f`. -/
def IsSensitiveCoord (f : BooleanFunction n) (x : Cube n) (i : Fin n) : Prop :=
  f (flipBit x i) ≠ f x

instance (f : BooleanFunction n) (x : Cube n) : DecidablePred (IsSensitiveCoord f x) :=
  fun i => inferInstanceAs (Decidable (f (flipBit x i) ≠ f x))

/-- The set of coordinates sensitive for `f` at `x`. -/
def sensitiveCoords (f : BooleanFunction n) (x : Cube n) : Finset (Fin n) :=
  Finset.univ.filter (IsSensitiveCoord f x)

/-- The bridge between the predicate and the `Finset` it cuts out. -/
@[simp]
lemma mem_sensitiveCoords {f : BooleanFunction n} {x : Cube n} {i : Fin n} :
    i ∈ sensitiveCoords f x ↔ IsSensitiveCoord f x i := by
  simp [sensitiveCoords]

/-- The number of sensitive coordinates in input `x`, usually denoted `sₓ(f)`. -/
def pointSensitivity (f : BooleanFunction n) (x : Cube n) : ℕ := (sensitiveCoords f x).card

/-- The maximum sensitivity over all inputs, denoted `s(f)`. -/
def sensitivity (f : BooleanFunction n) : ℕ := Finset.univ.sup (pointSensitivity f)

/-- Lower-bound rule for `sₓ(f)`: exhibit a set of sensitive coordinates. -/
lemma card_le_pointSensitivity {f : BooleanFunction n} {x : Cube n} {S : Finset (Fin n)}
    (h : ∀ i ∈ S, IsSensitiveCoord f x i) : S.card ≤ pointSensitivity f x := by
  apply Finset.card_le_card
  simpa [Finset.subset_iff] using h

/-- The sensitivity at a single input is at most the sensitivity of `f`: `sₓ(f) ≤ s(f)`. -/
lemma pointSensitivity_le_sensitivity (f : BooleanFunction n) (x : Cube n) :
    pointSensitivity f x ≤ sensitivity f :=
  Finset.le_sup (Finset.mem_univ x)

/-- Lower-bound rule for `s(f)`: sensitive coordinates at any input suffice. -/
lemma card_le_sensitivity {f : BooleanFunction n} {x : Cube n} {S : Finset (Fin n)}
    (h : ∀ i ∈ S, IsSensitiveCoord f x i) : S.card ≤ sensitivity f :=
  (card_le_pointSensitivity h).trans (pointSensitivity_le_sensitivity f x)

/-! ## Block sensitivity -/

/-- Block `B` is sensitive for `f` at `x` when flipping all bits of `B` flips `f`. -/
def IsSensitiveBlock (f : BooleanFunction n) (x : Cube n) (B : Block n) : Prop :=
  f (flipBlock x B) ≠ f x

instance (f : BooleanFunction n) (x : Cube n) (B : Block n) : Decidable (IsSensitiveBlock f x B) :=
  inferInstanceAs (Decidable (f (flipBlock x B) ≠ f x))

/-- Every member flips `f`, and the members are pairwise disjoint. -/
def IsSensitiveFamily (f : BooleanFunction n) (x : Cube n) (F : Finset (Block n)) : Prop :=
  (∀ B ∈ F, IsSensitiveBlock f x B) ∧ (F : Set (Block n)).PairwiseDisjoint id

instance (f : BooleanFunction n) (x : Cube n) (F : Finset (Block n)) :
    Decidable (IsSensitiveFamily f x F) :=
  decidable_of_iff ((∀ B ∈ F, IsSensitiveBlock f x B) ∧
    ∀ P ∈ F, ∀ Q ∈ F, P ≠ Q → Disjoint P Q) Iff.rfl

/-- All sensitive families. -/
def sensitiveFamilies (f : BooleanFunction n) (x : Cube n) : Finset (Finset (Block n)) :=
  Finset.univ.filter (IsSensitiveFamily f x)

@[simp]
lemma mem_sensitiveFamilies {f : BooleanFunction n} {x : Cube n} {F : Finset (Block n)} :
    F ∈ sensitiveFamilies f x ↔ IsSensitiveFamily f x F := by
  simp [sensitiveFamilies]

/-- The block sensitivity of `f` at `x`: the largest number of pairwise disjoint blocks of
coordinates such that flipping every coordinate of any one block flips `f`. Usually denoted
`bsₓ(f)`. -/
def pointBlockSensitivity (f : BooleanFunction n) (x : Cube n) : ℕ :=
  (sensitiveFamilies f x).sup Finset.card

/-- The maximum block sensitivity over all inputs, denoted `bs(f)`. -/
def blockSensitivity (f : BooleanFunction n) : ℕ := Finset.univ.sup (pointBlockSensitivity f)

/-- Lower-bound rule for `bsₓ(f)`: exhibit one sensitive family. -/
lemma card_le_pointBlockSensitivity {f : BooleanFunction n} {x : Cube n} {F : Finset (Block n)}
    (h : IsSensitiveFamily f x F) : F.card ≤ pointBlockSensitivity f x :=
  Finset.le_sup (mem_sensitiveFamilies.mpr h)

/-- The block sensitivity at a single input is at most that of `f`: `bsₓ(f) ≤ bs(f)`. -/
lemma pointBlockSensitivity_le_blockSensitivity (f : BooleanFunction n) (x : Cube n) :
    pointBlockSensitivity f x ≤ blockSensitivity f :=
  Finset.le_sup (Finset.mem_univ x)

/-- Lower-bound rule for `bs(f)`. -/
lemma card_le_blockSensitivity {f : BooleanFunction n} {x : Cube n} {F : Finset (Block n)}
    (h : IsSensitiveFamily f x F) : F.card ≤ blockSensitivity f :=
  (card_le_pointBlockSensitivity h).trans (pointBlockSensitivity_le_blockSensitivity f x)

/-! ## Sensitive singletons -/

/-- A singleton block is sensitive exactly when its coordinate is. -/
@[simp]
lemma isSensitiveBlock_singleton {f : BooleanFunction n} {x : Cube n} {i : Fin n} :
    IsSensitiveBlock f x {i} ↔ IsSensitiveCoord f x i := by
  rw [IsSensitiveBlock, IsSensitiveCoord, flipBlock_singleton]

/-! ## `s(f) ≤ bs(f)` -/

/-- One block per sensitive coordinate. -/
def singletonFamily (f : BooleanFunction n) (x : Cube n) : Finset (Block n) :=
  (sensitiveCoords f x).image (fun i => ({i} : Block n))

/-- Membership in the singleton family: one block per sensitive coordinate. -/
@[simp]
lemma mem_singletonFamily {f : BooleanFunction n} {x : Cube n} {B : Block n} :
    B ∈ singletonFamily f x ↔ ∃ i, IsSensitiveCoord f x i ∧ {i} = B := by
  simp [singletonFamily]

/-- The singleton family has one block per sensitive coordinate, so `sₓ(f)` of them. -/
@[simp]
lemma card_singletonFamily {f : BooleanFunction n} {x : Cube n} :
    (singletonFamily f x).card = pointSensitivity f x :=
  Finset.card_image_of_injective _ Finset.singleton_injective

/-- Singletons of distinct sensitive coordinates do form a sensitive family: each
flips `f`, and distinct singletons are disjoint. -/
lemma isSensitiveFamily_singletonFamily {f : BooleanFunction n} {x : Cube n} :
    IsSensitiveFamily f x (singletonFamily f x) := by
  constructor
  · rintro B hB
    obtain ⟨i, hi, rfl⟩ := mem_singletonFamily.mp hB
    exact isSensitiveBlock_singleton.mpr hi
  · rintro P hP Q hQ hPQ
    obtain ⟨i, -, rfl⟩ := mem_singletonFamily.mp hP
    obtain ⟨j, -, rfl⟩ := mem_singletonFamily.mp hQ
    exact Finset.disjoint_singleton.mpr fun h => hPQ (by rw [h])

/-- Pointwise: `sₓ(f) ≤ bsₓ(f)`. -/
theorem pointSensitivity_le_pointBlockSensitivity (f : BooleanFunction n) (x : Cube n) :
    pointSensitivity f x ≤ pointBlockSensitivity f x :=
  card_singletonFamily ▸ card_le_pointBlockSensitivity isSensitiveFamily_singletonFamily

/-- Every sensitive coordinate is a sensitive block of size one, so `s(f) ≤ bs(f)`. -/
theorem sensitivity_le_blockSensitivity (f : BooleanFunction n) :
    sensitivity f ≤ blockSensitivity f :=
  Finset.sup_mono_fun fun x _ => pointSensitivity_le_pointBlockSensitivity f x

/-! ## Minimal sensitive blocks -/

/-- `B` is sensitive, and no proper subset of `B` is sensitive. -/
def IsMinimalSensitiveBlock (f : BooleanFunction n) (x : Cube n) (B : Block n) : Prop :=
  IsSensitiveBlock f x B ∧ ∀ C ⊂ B, ¬ IsSensitiveBlock f x C

instance (f : BooleanFunction n) (x : Cube n) (B : Block n) :
    Decidable (IsMinimalSensitiveBlock f x B) :=
  inferInstanceAs (Decidable (IsSensitiveBlock f x B ∧ ∀ C ⊂ B, ¬ IsSensitiveBlock f x C))

namespace IsMinimalSensitiveBlock

variable {f : BooleanFunction n} {x : Cube n} {B : Block n} {i : Fin n}

/-- Dropping any coordinate from a minimal sensitive block breaks sensitivity. -/
lemma not_isSensitiveBlock_erase (hB : IsMinimalSensitiveBlock f x B) (hi : i ∈ B) :
    ¬ IsSensitiveBlock f x (B.erase i) :=
  hB.2 _ (Finset.erase_ssubset hi)

/-- Every coordinate of a minimal sensitive block is sensitive at the input which
has the minimal sensitive block flipped. -/
lemma isSensitiveCoord_flipBlock (hB : IsMinimalSensitiveBlock f x B) (hi : i ∈ B) :
    IsSensitiveCoord f (flipBlock x B) i := by
  unfold IsSensitiveCoord
  rw [← flipBlock_erase x B hi, not_not.mp (hB.not_isSensitiveBlock_erase hi)]
  exact Ne.symm hB.1

/-- `|B| ≤ s(f)` for a minimal sensitive block `B`. -/
theorem card_le_sensitivity (hB : IsMinimalSensitiveBlock f x B) : B.card ≤ sensitivity f :=
  _root_.Cslib.QueryComplexity.card_le_sensitivity fun _ hi => hB.isSensitiveCoord_flipBlock hi

end IsMinimalSensitiveBlock

/-! ## Certificates

A certificate for `x` is a partial assignment consistent with `x` that already forces the value
of `f`. `IsCertificate` keeps that in general form, with the forced value `b` a parameter.
-/

/-- `C` forces the value `b`: everything consistent with `C` has `f = b`. -/
def IsCertificate (f : BooleanFunction n) (C : PartialAssignment n) (b : Bool) : Prop :=
  ∀ x, Agrees C x → f x = b

instance (f : BooleanFunction n) (C : PartialAssignment n) (b : Bool) :
    Decidable (IsCertificate f C b) :=
  inferInstanceAs (Decidable (∀ x, Agrees C x → f x = b))

/-- Partial assignments consistent with `x` that already force `f x`. -/
def certificates (f : BooleanFunction n) (x : Cube n) : Finset (PartialAssignment n) :=
  Finset.univ.filter (fun C => Agrees C x ∧ IsCertificate f C (f x))

@[simp]
lemma mem_certificates {f : BooleanFunction n} {x : Cube n} {C : PartialAssignment n} :
    C ∈ certificates f x ↔ Agrees C x ∧ IsCertificate f C (f x) := by
  simp [certificates]

/-- Reading off all of `x` is always a certificate. -/
lemma ofCube_mem_certificates (f : BooleanFunction n) (x : Cube n) :
    ofCube x ∈ certificates f x :=
  mem_certificates.mpr ⟨agrees_ofCube_iff.mpr rfl, fun _ hy => by
    rw [agrees_ofCube_iff.mp hy]⟩

/-- There is always a certificate for `x`. -/
lemma certificates_nonempty (f : BooleanFunction n) (x : Cube n) : (certificates f x).Nonempty :=
  ⟨ofCube x, ofCube_mem_certificates f x⟩

/-! ## Pointwise certificates as sets of coordinates

At a fixed input a certificate carries no information beyond the coordinates it reads: `Agrees C x`
forces `C i = some (x i)` on the support and `none` elsewhere. So `Cₓ(f)` is defined over sets of
coordinates rather than over partial assignments.
-/

/-- `S` pins down `f` at `x`: every input agreeing with `x` on `S` takes the same value. This is
the pointwise form of `IsCertificate`, recording only which coordinates are read. -/
def Fixes (f : BooleanFunction n) (x : Cube n) (S : Finset (Fin n)) : Prop :=
  ∀ y, (∀ i ∈ S, y i = x i) → f y = f x

instance (f : BooleanFunction n) (x : Cube n) (S : Finset (Fin n)) : Decidable (Fixes f x S) :=
  inferInstanceAs (Decidable (∀ y, (∀ i ∈ S, y i = x i) → f y = f x))

/-- Reading every coordinate of `x` pins down `f`. -/
lemma fixes_univ (f : BooleanFunction n) (x : Cube n) : Fixes f x Finset.univ :=
  fun _ hy => congrArg f (funext fun i => hy i (Finset.mem_univ i))

/-- There is always a fixing set, so `Cₓ(f)` is a minimum over a non-empty set. -/
lemma fixes_nonempty (f : BooleanFunction n) (x : Cube n) :
    (Finset.univ.filter (Fixes f x)).Nonempty :=
  ⟨Finset.univ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fixes_univ f x⟩⟩

/-- The fewest coordinates of `x` that pin down the value of `f`, denoted `Cₓ(f)`. -/
def pointCertificateComplexity (f : BooleanFunction n) (x : Cube n) : ℕ :=
  (Finset.univ.filter (Fixes f x)).inf' (fixes_nonempty f x) Finset.card

/-- Upper-bound rule for `Cₓ(f)`: exhibit one fixing set. -/
lemma pointCertificateComplexity_le {f : BooleanFunction n} {x : Cube n} {S : Finset (Fin n)}
    (h : Fixes f x S) : pointCertificateComplexity f x ≤ S.card :=
  Finset.inf'_le _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)

/-- Lower-bound rule for `Cₓ(f)`: a bound that holds for every fixing set. -/
lemma le_pointCertificateComplexity {f : BooleanFunction n} {x : Cube n} {k : ℕ}
    (h : ∀ S, Fixes f x S → k ≤ S.card) : k ≤ pointCertificateComplexity f x :=
  Finset.le_inf' _ _ fun _ hS => h _ (Finset.mem_filter.mp hS).2

/-- The maximum over all inputs of the smallest certificate size, denoted `C(f)`. -/
def certificateComplexity (f : BooleanFunction n) : ℕ :=
  Finset.univ.sup (pointCertificateComplexity f)

/-- The certificate complexity at a single input is at most that of `f`: `Cₓ(f) ≤ C(f)`. -/
lemma pointCertificateComplexity_le_certificateComplexity (f : BooleanFunction n) (x : Cube n) :
    pointCertificateComplexity f x ≤ certificateComplexity f :=
  Finset.le_sup (Finset.mem_univ x)

/-- `Cₓ(f) ≤ n`: reading every coordinate pins down `f`. -/
theorem pointCertificateComplexity_le_card (f : BooleanFunction n) (x : Cube n) :
    pointCertificateComplexity f x ≤ n :=
  (pointCertificateComplexity_le (fixes_univ f x)).trans_eq (by simp)

/-! ## `bs(f) ≤ C(f)`

A set of coordinates pinning down `f` at `x` must meet every block of a sensitive family. The
blocks are pairwise disjoint, so a family has at most `|S|` members.
-/

/-- A fixing set must contain at least one coordinate of every sensitive block. -/
theorem sensitiveBlock_inter_nonempty {f : BooleanFunction n} (x : Cube n) (B : Block n)
    (hB : IsSensitiveBlock f x B) {S : Finset (Fin n)} (hS : Fixes f x S) :
    (B ∩ S).Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty, Finset.eq_empty_iff_forall_notMem] at h
  refine hB (hS _ fun i hi => ?_)
  have hiB : i ∉ B := fun hiB => h i (Finset.mem_inter.mpr ⟨hiB, hi⟩)
  simp [flipBlock, hiB]

/-- A fixing set is at least as large as any sensitive family. -/
lemma card_le_card_of_isSensitiveFamily {f : BooleanFunction n} {x : Cube n}
    {F : Finset (Block n)} {S : Finset (Fin n)}
    (hF : IsSensitiveFamily f x F) (hS : Fixes f x S) : F.card ≤ S.card :=
  (Finset.card_le_card_biUnion
      (fun _ hP _ hQ hPQ => Disjoint.mono Finset.inter_subset_left Finset.inter_subset_left
        (hF.2 hP hQ hPQ))
      (fun B hB => sensitiveBlock_inter_nonempty x B (hF.1 B hB) hS)).trans
    (Finset.card_le_card (Finset.biUnion_subset.mpr fun _ _ => Finset.inter_subset_right))

/-- Pointwise: `bsₓ(f) ≤ Cₓ(f)`. -/
theorem pointBlockSensitivity_le_pointCertificateComplexity (f : BooleanFunction n) (x : Cube n) :
    pointBlockSensitivity f x ≤ pointCertificateComplexity f x :=
  Finset.sup_le fun _ hF => le_pointCertificateComplexity fun _ hS =>
    card_le_card_of_isSensitiveFamily (mem_sensitiveFamilies.mp hF) hS

/-- Every block of a sensitive family meets every fixing set, so `bs(f) ≤ C(f)`. -/
theorem blockSensitivity_le_certificateComplexity (f : BooleanFunction n) :
    blockSensitivity f ≤ certificateComplexity f :=
  Finset.sup_mono_fun fun x _ =>
    pointBlockSensitivity_le_pointCertificateComplexity f x

end Cslib.QueryComplexity
