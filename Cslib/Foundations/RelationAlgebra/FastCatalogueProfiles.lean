/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.FastCatalogue
public import Mathlib.Order.Fin.Basic

/-!
# Canonical cycle profiles for catalogue classifications

Atom renamings permute the Peircean cycle orbits, so their profiles can be computed by
permuting the bits of the original profile. Distinctness follows from a least profile for
each model and strictly increasing least profiles, avoiding pairwise model comparisons.
-/

@[expose] public section

namespace Cslib.RelationAlgebra

variable {j k r m p : ℕ}

/-- An explicitly defined table together with its verified cycle profile. -/
structure ProfiledCycleTable (reps : Fin r → Cycle j k) extends EncodedCycleTable j k where
  /-- The bits describing the selected Peircean cycle orbits. -/
  profile : ℕ
  /-- Correctness of the profile of the actual cycle table. -/
  profile_eq : choiceMask (fun i => decide (cycleClosure table.cycles
    (some (reps i).1) (some (reps i).2.1) (some (reps i).2.2))) = profile

namespace Code

/-- Read the basis-cycle bits from an encoded table. -/
def baseProfile (reps : Fin r → Cycle j k) (code : ℕ) : ℕ :=
  choiceMask fun i => bitAt code (index (atomCount j k)
    (Atom.code (some (reps i).1)) (Atom.code (some (reps i).2.1))
    (Atom.code (some (reps i).2.2)))

/-- Permute the orbit bits of a cycle profile. -/
def permuteProfile (mask : ℕ) (permutation : Fin r → Fin r) : ℕ :=
  choiceMask fun i => bitAt mask (permutation i)

/-- Check that the identity profile is least among all listed atom renamings. -/
def profileMinimumCheck (profiles : Fin m → Fin p → ℕ) (identity : Fin p) : Bool :=
  allFin fun i => allFin fun q => Nat.ble (profiles i identity) (profiles i q)

/-- Check strict increase by comparing only adjacent entries. -/
def increasingCheck (values : Fin m → ℕ) : Bool :=
  allBelow (fun i => if h : i + 1 < m then
    Nat.blt (values ⟨i, by omega⟩) (values ⟨i + 1, h⟩) else true) m

end Code

/-- Attach a profile to an encoded table by checking its basis-cycle bits. -/
def ProfiledCycleTable.ofEncoded (reps : Fin r → Cycle j k)
    (encoded : EncodedCycleTable j k) (profile : ℕ)
    (h : Code.baseProfile reps encoded.code = profile) : ProfiledCycleTable reps where
  toEncodedCycleTable := encoded
  profile := profile
  profile_eq := by
    simpa only [Code.baseProfile, cycleClosure_iff_bitAt encoded.encodes, Bool.decide_eq_true]
      using h

/-- The orbit action of a diversity-atom renaming determines its entire cycle profile. -/
theorem profileCode_eq_of_orbit_renaming (reps : Fin r → Cycle j k)
    (cycles : Finset (Cycle j k)) (rename : DiversityAtom j k → DiversityAtom j k)
    (permutation : Fin r → Fin r)
    (horbit : ∀ i, (some (rename (reps i).1), some (rename (reps i).2.1),
      some (rename (reps i).2.2)) ∈ cycleOrbit (reps (permutation i)))
    (mask : ℕ)
    (hmask : choiceMask (fun i => decide (cycleClosure cycles
      (some (reps i).1) (some (reps i).2.1) (some (reps i).2.2))) = mask) :
    choiceMask (fun i => decide (cycleClosure cycles
      (some (rename (reps i).1)) (some (rename (reps i).2.1))
      (some (rename (reps i).2.2)))) = Code.permuteProfile mask permutation := by
  rw [Code.permuteProfile, ← hmask]
  apply congrArg choiceMask
  funext i
  rw [bitAt_choiceMask, Bool.eq_iff_iff]
  simp only [decide_eq_true_eq]
  exact ⟨fun h => cycleClosure_of_mem_orbit h (cycleOrbit_symm
    (d := (rename (reps i).1, rename (reps i).2.1, rename (reps i).2.2)) (horbit i)),
    fun h => cycleClosure_of_mem_orbit h (horbit i)⟩

/-- A numeric minimum check gives all the required profile inequalities. -/
theorem profile_minimal_of_check (profiles : Fin m → Fin p → ℕ) (identity : Fin p)
    (h : Code.profileMinimumCheck profiles identity = true) :
    ∀ i q, profiles i identity ≤ profiles i q := by
  intro i q
  exact Nat.le_of_ble_eq_true (Code.allFin_eq_true.mp (Code.allFin_eq_true.mp h i) q)

/-- Adjacent comparisons certify strict increase of a finite vector. -/
theorem strictMono_of_increasingCheck (values : Fin m → ℕ)
    (h : Code.increasingCheck values = true) : StrictMono values := by
  cases m with
  | zero => intro i; exact Fin.elim0 i
  | succ n =>
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    have hi : i.val + 1 < n + 1 := Nat.succ_lt_succ i.isLt
    have hc := Code.allBelow_eq_true.mp h i.val (Nat.lt_succ_of_lt i.isLt)
    simp only [dite_eq_left hi, Nat.blt_eq] at hc
    exact hc

/-- Least identity profiles distinguish models without comparing every pair of models. -/
theorem cycles_distinct_of_minimal_profiles (reps : Fin r → Cycle j k)
    (models : Fin m → IntegralCycleTable j k) (renames : Fin p → Atom j k → Atom j k)
    (identity : Fin p) (hidentity : ∀ x, renames identity x = x)
    (exhaustive : ∀ f : Atom j k → Atom j k, Function.Injective f → f none = none →
      (∀ x, f x.converse = (f x).converse) → ∃ q, f = renames q)
    (profiles : Fin m → Fin p → ℕ)
    (hprofiles : ∀ i q, choiceMask (fun c => decide (cycleClosure (models i).cycles
      (renames q (some (reps c).1)) (renames q (some (reps c).2.1))
      (renames q (some (reps c).2.2)))) = profiles i q)
    (hminimum : ∀ i q, profiles i identity ≤ profiles i q)
    (hinjective : Function.Injective (fun i => profiles i identity)) :
    ∀ i l f, AtomRelabelling (models i).cycles (models l).cycles f → i = l := by
  have profiles_match (i l : Fin m) (f : Atom j k → Atom j k)
      (hf : AtomRelabelling (models i).cycles (models l).cycles f) :
      ∃ q, profiles i identity = profiles l q := by
    obtain ⟨q, rfl⟩ := exhaustive f hf.1 hf.2.1 hf.2.2.1
    refine ⟨q, ?_⟩
    rw [← hprofiles i identity, ← hprofiles l q]
    simp only [hidentity, hf.2.2.2]
  intro i l f hf
  obtain ⟨q, hq⟩ := profiles_match i l f hf
  obtain ⟨g, hg⟩ := Complex.exists_relabelling (models l) (models i)
    (Complex.equivOfRelabelling (models i) (models l) f hf).symm
  obtain ⟨q', hq'⟩ := profiles_match l i g hg
  apply hinjective
  apply le_antisymm
  · change profiles i identity ≤ profiles l identity
    rw [hq']
    exact hminimum i q'
  · change profiles l identity ≤ profiles i identity
    rw [hq]
    exact hminimum l q

/-- A finite-index property follows from certificates for consecutive blocks of 64 indices. -/
theorem forall_of_blocks {n : ℕ} {property : ℕ → Prop}
    (h : ∀ block : Fin ((n + 63) / 64),
      ∀ offset : Fin (min 64 (n - block.val * 64)),
        property (block.val * 64 + offset.val)) :
    ∀ i : Fin n, property i.val := by
  intro i
  have hblock : i.val / 64 < (n + 63) / 64 := by omega
  have hoffset : i.val % 64 < min 64 (n - i.val / 64 * 64) := by omega
  have hi := h ⟨i.val / 64, hblock⟩ ⟨i.val % 64, hoffset⟩
  change property (i.val / 64 * 64 + i.val % 64) at hi
  have he : i.val / 64 * 64 + i.val % 64 = i.val := by omega
  exact he ▸ hi

end Cslib.RelationAlgebra
