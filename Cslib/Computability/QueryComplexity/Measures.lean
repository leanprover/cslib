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
def IsSensitiveCoord (f : BoolFunc n) (x : Cube n) (i : Fin n) : Prop :=
  f (flipBit x i) ≠ f x

instance (f : BoolFunc n) (x : Cube n) : DecidablePred (IsSensitiveCoord f x) :=
  fun i => inferInstanceAs (Decidable (f (flipBit x i) ≠ f x))

/-- The set of coordinates sensitive for `f` at `x`. -/
def sensitiveCoords (f : BoolFunc n) (x : Cube n) : Finset (Fin n) :=
  Finset.univ.filter (IsSensitiveCoord f x)

/-- The bridge between the predicate and the `Finset` it cuts out. -/
@[simp]
lemma mem_sensitiveCoords {f : BoolFunc n} {x : Cube n} {i : Fin n} :
    i ∈ sensitiveCoords f x ↔ IsSensitiveCoord f x i := by
  simp [sensitiveCoords]

/-- The number of sensitive coordinates in input `x`, usually denoted `sₓ(f)`. -/
def pointSensitivity (f : BoolFunc n) (x : Cube n) : ℕ := (sensitiveCoords f x).card

/-- The maximum sensitivity over all inputs, denoted `s(f)`. -/
def sensitivity (f : BoolFunc n) : ℕ := Finset.univ.sup (pointSensitivity f)

/-- Lower-bound rule for `sₓ(f)`: exhibit a set of sensitive coordinates. -/
lemma card_le_pointSensitivity {f : BoolFunc n} {x : Cube n} {S : Finset (Fin n)}
    (h : ∀ i ∈ S, IsSensitiveCoord f x i) : S.card ≤ pointSensitivity f x := by
  apply Finset.card_le_card
  simpa [Finset.subset_iff] using h

/-- The sensitivity at a single input is at most the sensitivity of `f`: `sₓ(f) ≤ s(f)`. -/
lemma pointSensitivity_le_sensitivity (f : BoolFunc n) (x : Cube n) :
    pointSensitivity f x ≤ sensitivity f :=
  Finset.le_sup (Finset.mem_univ x)

/-- Lower-bound rule for `s(f)`: sensitive coordinates at any input suffice. -/
lemma card_le_sensitivity {f : BoolFunc n} {x : Cube n} {S : Finset (Fin n)}
    (h : ∀ i ∈ S, IsSensitiveCoord f x i) : S.card ≤ sensitivity f :=
  (card_le_pointSensitivity h).trans (pointSensitivity_le_sensitivity f x)

/-! ## Block sensitivity -/

/-- Block `B` is sensitive for `f` at `x` when flipping all bits of `B` flips `f`. -/
def IsSensitiveBlock (f : BoolFunc n) (x : Cube n) (B : Block n) : Prop :=
  f (flipBlock x B) ≠ f x

instance (f : BoolFunc n) (x : Cube n) (B : Block n) : Decidable (IsSensitiveBlock f x B) :=
  inferInstanceAs (Decidable (f (flipBlock x B) ≠ f x))

/-- Every member flips `f`, and the members are pairwise disjoint. -/
def IsSensitiveFamily (f : BoolFunc n) (x : Cube n) (F : Finset (Block n)) : Prop :=
  (∀ B ∈ F, IsSensitiveBlock f x B) ∧ (F : Set (Block n)).PairwiseDisjoint id

instance (f : BoolFunc n) (x : Cube n) (F : Finset (Block n)) :
    Decidable (IsSensitiveFamily f x F) :=
  decidable_of_iff ((∀ B ∈ F, IsSensitiveBlock f x B) ∧
    ∀ P ∈ F, ∀ Q ∈ F, P ≠ Q → Disjoint P Q) Iff.rfl

/-- All sensitive families. -/
def sensitiveFamilies (f : BoolFunc n) (x : Cube n) : Finset (Finset (Block n)) :=
  Finset.univ.filter (IsSensitiveFamily f x)

@[simp]
lemma mem_sensitiveFamilies {f : BoolFunc n} {x : Cube n} {F : Finset (Block n)} :
    F ∈ sensitiveFamilies f x ↔ IsSensitiveFamily f x F := by
  simp [sensitiveFamilies]

/-- The block sensitivity of `f` at `x`: the largest number of pairwise disjoint blocks of
coordinates such that flipping every coordinate of any one block flips `f`. Usually denoted
`bsₓ(f)`. -/
def pointBlockSensitivity (f : BoolFunc n) (x : Cube n) : ℕ :=
  (sensitiveFamilies f x).sup Finset.card

/-- The maximum block sensitivity over all inputs, denoted `bs(f)`. -/
def blockSensitivity (f : BoolFunc n) : ℕ := Finset.univ.sup (pointBlockSensitivity f)

/-- Lower-bound rule for `bsₓ(f)`: exhibit one sensitive family. -/
lemma card_le_pointBlockSensitivity {f : BoolFunc n} {x : Cube n} {F : Finset (Block n)}
    (h : IsSensitiveFamily f x F) : F.card ≤ pointBlockSensitivity f x :=
  Finset.le_sup (mem_sensitiveFamilies.mpr h)

/-- The block sensitivity at a single input is at most that of `f`: `bsₓ(f) ≤ bs(f)`. -/
lemma pointBlockSensitivity_le_blockSensitivity (f : BoolFunc n) (x : Cube n) :
    pointBlockSensitivity f x ≤ blockSensitivity f :=
  Finset.le_sup (Finset.mem_univ x)

/-- Lower-bound rule for `bs(f)`. -/
lemma card_le_blockSensitivity {f : BoolFunc n} {x : Cube n} {F : Finset (Block n)}
    (h : IsSensitiveFamily f x F) : F.card ≤ blockSensitivity f :=
  (card_le_pointBlockSensitivity h).trans (pointBlockSensitivity_le_blockSensitivity f x)

/-! ## Sensitive singletons -/

/-- A singleton block is sensitive exactly when its coordinate is. -/
@[simp]
lemma isSensitiveBlock_singleton {f : BoolFunc n} {x : Cube n} {i : Fin n} :
    IsSensitiveBlock f x {i} ↔ IsSensitiveCoord f x i := by
  rw [IsSensitiveBlock, IsSensitiveCoord, flipBlock_singleton]

/-! ## `s(f) ≤ bs(f)` -/

/-- One block per sensitive coordinate. -/
def singletonFamily (f : BoolFunc n) (x : Cube n) : Finset (Block n) :=
  (sensitiveCoords f x).image (fun i => ({i} : Block n))

/-- Membership in the singleton family: one block per sensitive coordinate. -/
@[simp]
lemma mem_singletonFamily {f : BoolFunc n} {x : Cube n} {B : Block n} :
    B ∈ singletonFamily f x ↔ ∃ i, IsSensitiveCoord f x i ∧ {i} = B := by
  simp [singletonFamily]

/-- The singleton family has one block per sensitive coordinate, so `sₓ(f)` of them. -/
@[simp]
lemma card_singletonFamily {f : BoolFunc n} {x : Cube n} :
    (singletonFamily f x).card = pointSensitivity f x :=
  Finset.card_image_of_injective _ Finset.singleton_injective

/-- Singletons of distinct sensitive coordinates do form a sensitive family: each
flips `f`, and distinct singletons are disjoint. -/
lemma isSensitiveFamily_singletonFamily {f : BoolFunc n} {x : Cube n} :
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
theorem pointSensitivity_le_pointBlockSensitivity (f : BoolFunc n) (x : Cube n) :
    pointSensitivity f x ≤ pointBlockSensitivity f x :=
  card_singletonFamily ▸ card_le_pointBlockSensitivity isSensitiveFamily_singletonFamily

/-- Every sensitive coordinate is a sensitive block of size one, so `s(f) ≤ bs(f)`. -/
theorem sensitivity_le_blockSensitivity (f : BoolFunc n) :
    sensitivity f ≤ blockSensitivity f :=
  Finset.sup_mono_fun fun x _ => pointSensitivity_le_pointBlockSensitivity f x

/-! ## Minimal sensitive blocks -/

/-- `B` is sensitive, and no proper subset of `B` is sensitive. -/
def IsMinimalSensitiveBlock (f : BoolFunc n) (x : Cube n) (B : Block n) : Prop :=
  IsSensitiveBlock f x B ∧ ∀ C ⊂ B, ¬ IsSensitiveBlock f x C

instance (f : BoolFunc n) (x : Cube n) (B : Block n) :
    Decidable (IsMinimalSensitiveBlock f x B) :=
  inferInstanceAs (Decidable (IsSensitiveBlock f x B ∧ ∀ C ⊂ B, ¬ IsSensitiveBlock f x C))

namespace IsMinimalSensitiveBlock

variable {f : BoolFunc n} {x : Cube n} {B : Block n} {i : Fin n}

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

/-! ## Certificates -/

/-- `C` forces the value `b`: everything consistent with `C` has `f = b`. -/
def IsCertificate (f : BoolFunc n) (C : PartialAssignment n) (b : Bool) : Prop :=
  ∀ x, Agrees C x → f x = b

instance (f : BoolFunc n) (C : PartialAssignment n) (b : Bool) : Decidable (IsCertificate f C b) :=
  inferInstanceAs (Decidable (∀ x, Agrees C x → f x = b))

/-- Assignments consistent with `x` that already force `f x`. -/
def certificates (f : BoolFunc n) (x : Cube n) : Finset (PartialAssignment n) :=
  Finset.univ.filter (fun C => Agrees C x ∧ IsCertificate f C (f x))

@[simp]
lemma mem_certificates {f : BoolFunc n} {x : Cube n} {C : PartialAssignment n} :
    C ∈ certificates f x ↔ Agrees C x ∧ IsCertificate f C (f x) := by
  simp [certificates]

/-- Reading off all of `x` is always a certificate. -/
lemma ofCube_mem_certificates (f : BoolFunc n) (x : Cube n) : ofCube x ∈ certificates f x :=
  mem_certificates.mpr ⟨agrees_ofCube_iff.mpr rfl, fun _ hy => by
    rw [agrees_ofCube_iff.mp hy]⟩

/-- There is always a certificate, so `Cₓ(f)` is a minimum over a non-empty set. -/
lemma certificates_nonempty (f : BoolFunc n) (x : Cube n) : (certificates f x).Nonempty :=
  ⟨ofCube x, ofCube_mem_certificates f x⟩

/-- The size of the smallest certificate for the input `x`, denoted `Cₓ(f)`. -/
def pointCertificateComplexity (f : BoolFunc n) (x : Cube n) : ℕ :=
  (certificates f x).inf' (certificates_nonempty f x) size

/-- Upper-bound rule for `Cₓ(f)`: exhibit one certificate. -/
lemma pointCertificateComplexity_le {f : BoolFunc n} {x : Cube n} {C : PartialAssignment n}
    (h : C ∈ certificates f x) : pointCertificateComplexity f x ≤ size C :=
  Finset.inf'_le _ h

/-- The maximum over all inputs of the smallest certificate size, denoted `C(f)`. -/
def certificateComplexity (f : BoolFunc n) : ℕ :=
  Finset.univ.sup (pointCertificateComplexity f)

/-- The certificate complexity at a single input is at most that of `f`: `Cₓ(f) ≤ C(f)`. -/
lemma pointCertificateComplexity_le_certificateComplexity (f : BoolFunc n) (x : Cube n) :
    pointCertificateComplexity f x ≤ certificateComplexity f :=
  Finset.le_sup (Finset.mem_univ x)

/-- `Cₓ(f) ≤ n`: reading off the whole input is a certificate. -/
theorem pointCertificateComplexity_le_card (f : BoolFunc n) (x : Cube n) :
    pointCertificateComplexity f x ≤ n :=
  (pointCertificateComplexity_le (ofCube_mem_certificates f x)).trans_eq (size_ofCube x)

/-! ## `bs(f) ≤ C(f)`

A valid certificate for x must contain at least one bit from every block in a
sensitive family.
-/

/-- A certificate must fix at least one coordinate of every sensitive block. -/
theorem sensitiveBlock_inter_support_nonempty {f : BoolFunc n} (x : Cube n) (B : Block n)
    (hB : IsSensitiveBlock f x B) (C : PartialAssignment n) (hC : C ∈ certificates f x) :
    (B ∩ support C).Nonempty := by
  obtain ⟨hAgr, hCert⟩ := mem_certificates.mp hC
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty, Finset.eq_empty_iff_forall_notMem] at h
  refine hB (hCert _ fun i b hb => ?_)
  have hi : i ∉ B := fun hiB =>
    h i (Finset.mem_inter.mpr ⟨hiB, mem_support.mpr (by simp [hb])⟩)
  simpa [flipBlock, hi] using hAgr i b hb

/-- A certificate is at least as large as any sensitive family. -/
lemma card_le_size_of_isSensitiveFamily {f : BoolFunc n} {x : Cube n}
    {F : Finset (Block n)} {C : PartialAssignment n}
    (hF : IsSensitiveFamily f x F) (hC : C ∈ certificates f x) : F.card ≤ size C :=
  (Finset.card_le_card_biUnion
      (fun _ hP _ hQ hPQ => Disjoint.mono Finset.inter_subset_left Finset.inter_subset_left
        (hF.2 hP hQ hPQ))
      (fun B hB => sensitiveBlock_inter_support_nonempty x B (hF.1 B hB) C hC)).trans
    (Finset.card_le_card (Finset.biUnion_subset.mpr fun _ _ => Finset.inter_subset_right))

/-- Pointwise: `bsₓ(f) ≤ Cₓ(f)`. -/
theorem pointBlockSensitivity_le_pointCertificateComplexity
    (f : BoolFunc n) (x : Cube n) :
    pointBlockSensitivity f x ≤ pointCertificateComplexity f x :=
  Finset.sup_le fun _ hF => Finset.le_inf' _ _ fun _ hC =>
    card_le_size_of_isSensitiveFamily (mem_sensitiveFamilies.mp hF) hC

/-- Every block of a sensitive family meets the support of any certificate, so
`bs(f) ≤ C(f)`. -/
theorem blockSensitivity_le_certificateComplexity (f : BoolFunc n) :
    blockSensitivity f ≤ certificateComplexity f :=
  Finset.sup_mono_fun fun x _ =>
    pointBlockSensitivity_le_pointCertificateComplexity f x

end Cslib.QueryComplexity
