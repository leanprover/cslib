/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Foundations.Data.OmegaSequence.Init
public import Mathlib.Topology.Homeomorph.TransferInstance
public import Mathlib.Topology.MetricSpace.PiNat

/-!
# Topology on ω-sequences

The topology on ω-sequences is essentially the product topology when `ωSequence α` is
viewed as the product space `Π (n : ℕ), α`, where `α` is equipped with the discrete
topology.  The notion of "cylinders" are also ported from `Π (n : ℕ), α` and they form
a topological basis.
-/

@[expose] public section

namespace Cslib.ωSequence

open Set Homeomorph TopologicalSpace ωSequence

variable {α : Type*}

/-- Define the topology on `ωSequence α` using an equivalence from it to the product topology
`ℕ → WithDiscreteTopology α`. -/
instance : TopologicalSpace (ωSequence α) :=
  haveI eqv : ωSequence α ≃ (ℕ → WithDiscreteTopology α) := {
    toFun xs i := .toTopology ⊥ (xs.get i)
    invFun f := ωSequence.mk fun i => (f i).ofTopology
    left_inv _ := rfl
    right_inv _ := rfl
  }
  eqv.topologicalSpace

/-- The homeomorphisim from `ωSequence α` to `ℕ → WithDiscreteTopology α`. -/
def homeomorph : ωSequence α ≃ₜ (ℕ → WithDiscreteTopology α) := Equiv.homeomorph _

@[simp]
lemma homeomorph_apply (xs : ωSequence α) (i : Nat) :
    homeomorph xs i = .toTopology ⊥ (xs i) :=
  rfl

@[simp]
lemma homeomorph_symm_apply (f : ℕ → WithDiscreteTopology α) :
    homeomorph.symm f = ωSequence.mk fun i => (f i).ofTopology :=
  rfl

/-- Port the notion of "cylinders" from `ℕ → WithDiscreteTopology α` to `ωSequence α`. -/
def cylinder (xs : ωSequence α) (n : ℕ) : Set (ωSequence α) :=
  homeomorph ⁻¹' (PiNat.cylinder (homeomorph xs) n)

/-- An alternative characterization of cylinders in terms of `ωSequence α` alone. -/
theorem cylinder_def (xs : ωSequence α) (n : ℕ) :
    xs.cylinder n = { ys | ∀ k, k < n → ys k = xs k } := by
  simp [cylinder, PiNat.cylinder]

/-- Yet another alternative characterization of cylinders in terms of `ωSequence α` alone. -/
theorem cylinder_eq_prepend_range (xs : ωSequence α) (n : ℕ) :
    xs.cylinder n = range (xs.take n ++ω ·) := by
  ext ys
  simp only [cylinder_def, mem_ofPred_eq, mem_range]
  constructor
  · intro h
    use ys.drop n
    suffices xs.take n = ys.take n by grind
    apply List.ext_get <;> grind
  · grind [get_append_left]

/-- The cylinders form a topological basis. -/
theorem isTopologicalBasis_cylinders :
    IsTopologicalBasis { s | ∃ (xs : ωSequence α) (n : ℕ), s = xs.cylinder n } := by
  convert (PiNat.isTopologicalBasis_cylinders _).isInducing homeomorph.isInducing
  ext
  constructor
  · grind [cylinder]
  · rintro ⟨_, ⟨xs, n, rfl⟩, rfl⟩
    use (discharger := rfl) homeomorph.symm xs, n

/-- All cylinders are open sets. -/
theorem isOpen_cylinder (xs : ωSequence α) (n : ℕ) :
    IsOpen (xs.cylinder n) := homeomorph.continuous.isOpen_preimage _ (PiNat.isOpen_cylinder ..)

/-- Every ω-sequence in an open set belongs to a cylinder which is contained in the set. -/
theorem nhds_cylinders {xs : ωSequence α} {s : Set (ωSequence α)} (hx : xs ∈ s) (hs : IsOpen s) :
    ∃ (ys : ωSequence α) (n : ℕ), xs ∈ ys.cylinder n ∧ ys.cylinder n ⊆ s := by
  obtain ⟨_, ⟨ys, n, rfl⟩, hx', hy⟩:= isTopologicalBasis_cylinders.exists_subset_of_mem_open hx hs
  use ys, n

/-- A set is open iff any ω-sequence in the set has a finite prefix all of whose infinite
extensions are also in the set. -/
theorem isOpen_iff (s : Set (ωSequence α)) :
    IsOpen s ↔ ∀ xs, xs ∈ s → ∃ n, ∀ ys, (xs.take n) ++ω ys ∈ s := by
  simp only [IsTopologicalBasis.isOpen_iff isTopologicalBasis_cylinders,
    cylinder_eq_prepend_range, mem_ofPred_eq, ↓existsAndEq, mem_range, true_and]
  constructor <;> intro h xs hxs
  · obtain ⟨_, n, ⟨_, rfl⟩, _⟩ := h xs hxs
    use n
    grind [take_append_of_le_length]
  · obtain ⟨n, _⟩ := h xs hxs
    use xs, n, ⟨xs.drop n, ?_⟩ <;> grind

/-- A set is dense iff any finite sequence can be extended to an infinite sequence in the set. -/
theorem dense_iff (s : Set (ωSequence α)) :
    Dense s ↔ ∀ (xs : ωSequence α) (n : ℕ), ∃ ys, (xs.take n) ++ω ys ∈ s := by
  simp only [IsTopologicalBasis.dense_iff isTopologicalBasis_cylinders, cylinder_eq_prepend_range,
    mem_ofPred_eq, forall_exists_index]
  constructor
  · intro h xs n
    obtain ⟨ys, h1, _⟩ := h (xs.cylinder n) xs n
      (by simp [cylinder_eq_prepend_range]) (by use xs; simp [cylinder_def])
    use ys.drop n
    suffices xs.take n = ys.take n by grind
    grind [cylinder_eq_prepend_range, take_append_of_le_length]
  · rintro h c xs n rfl ⟨_, _, rfl⟩
    obtain ⟨ys, _⟩ := h xs n
    use xs.take n ++ω ys
    grind

end Cslib.ωSequence
