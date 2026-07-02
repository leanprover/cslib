/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Init
public import Cslib.Probability.PMF
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Data.FinEnum

/-!
# Monads with Uniform Selection

This file defines general typeclasses for asserting that a monad `m` supports uniform sampling
operations, along with companion `Lawful*` classes that, given an embedding into `PMF`, witness
that the operations lift to the corresponding uniform distributions.

Splitting the operation from its correctness proof keeps the sampling classes computable; only
the `Lawful*` classes (which mention `PMF`) need to be noncomputable.

## Main Definitions

- `Cslib.Probability.HasUniformBitVec` / `LawfulUniformBitVec`: monad supports uniform `BitVec n`
- `Cslib.Probability.HasUniformFinset` / `LawfulUniformFinset`: monad supports uniform selection
  from a non-empty finset
- `Cslib.Probability.HasUniformFintype` / `LawfulUniformFintype`: monad supports uniform selection
  from an inhabited finite type

-/

@[expose] public section

namespace Cslib.Probability

universe u v

section uniformBitvec

/-- The monad `m` has a way to model uniform selection over `BitVec n`. -/
class HasUniformBitVec (m : Type → Type*) where
  /-- Select a random bitvector of length `n`. -/
  uniformBitVec (n : ℕ) : m (BitVec n)

/-- `LawfulUniformBitVec` witnesses that `HasUniformBitVec.uniformBitVec` lifts to the uniform
distribution on `BitVec n`. -/
class LawfulUniformBitVec (m : Type → Type*) [MonadLiftT m PMF] [HasUniformBitVec m] : Prop where
  liftM_uniformBitVec (n : ℕ) :
    (liftM (HasUniformBitVec.uniformBitVec n : m (BitVec n)) : PMF (BitVec n)) =
      PMF.uniformOfFintype (BitVec n)

attribute [simp] LawfulUniformBitVec.liftM_uniformBitVec

/-- A uniform `Bool` derived from a single uniform bit. -/
def uniformBool {m : Type → Type*} [Monad m] [HasUniformBitVec m] : m Bool :=
  do return (← HasUniformBitVec.uniformBitVec 1) == 0

@[simp]
theorem liftM_uniformBool {m : Type → Type*} [Monad m] [MonadLiftT m PMF]
    [LawfulMonadLiftT m PMF] [HasUniformBitVec m] [LawfulUniformBitVec m] :
    (liftM (uniformBool : m Bool) : PMF Bool) = PMF.uniformOfFintype Bool := by
  simp only [uniformBool, liftM_bind, LawfulUniformBitVec.liftM_uniformBitVec, liftM_pure]
  let : BitVec 1 ≃ Bool := ⟨(· == 0), (bif · then 0 else 1), by decide, by decide⟩
  exact Cslib.Probability.PMF.uniformOfFintype_map_equiv this

end uniformBitvec

section uniformFinset

/-- The monad `m` has a way to model uniform selection over non-empty finsets. -/
class HasUniformFinset (m : Type u → Type*) where
  /-- Select a uniform element from the elements of `s : Finset α`. -/
  uniformFinset {α : Type u} (s : Finset α) (hs : s.Nonempty) : m α

/-- `LawfulUniformFinset` witnesses that `HasUniformFinset.uniformFinset` lifts to the uniform
distribution on the underlying finset. -/
class LawfulUniformFinset (m : Type u → Type*) [MonadLiftT m PMF] [HasUniformFinset m] : Prop where
  liftM_uniformFinset {α : Type u} (s : Finset α) (hs : s.Nonempty) :
    (liftM (HasUniformFinset.uniformFinset s hs : m α) : PMF α) = PMF.uniformOfFinset s hs

attribute [simp] LawfulUniformFinset.liftM_uniformFinset

instance {m} [HasUniformFinset m] : HasUniformBitVec m where
  uniformBitVec n :=
    HasUniformFinset.uniformFinset (Finset.univ : Finset (BitVec n)) Finset.univ_nonempty

instance {m} [MonadLiftT m PMF] [HasUniformFinset m] [LawfulUniformFinset m] :
    LawfulUniformBitVec m where
  liftM_uniformBitVec n := by
    change (liftM (HasUniformFinset.uniformFinset
      (Finset.univ : Finset (BitVec n)) Finset.univ_nonempty : m (BitVec n)) : PMF _) = _
    rw [LawfulUniformFinset.liftM_uniformFinset]; rfl

end uniformFinset

section uniformFintype

/-- The monad `m` has a way to model uniform selection over inhabited finite types. -/
class HasUniformFintype (m : Type u → Type*) where
  /-- Select a random element of the finite and nonempty type `α`. -/
  uniformFintype (α : Type u) [Fintype α] [Nonempty α] : m α

/-- `LawfulUniformFintype` witnesses that `HasUniformFintype.uniformFintype` lifts to the uniform
distribution on the underlying finite type. -/
class LawfulUniformFintype (m : Type u → Type*) [MonadLiftT m PMF]
    [HasUniformFintype m] : Prop where
  liftM_uniformFintype (α : Type u) [Fintype α] [Nonempty α] :
    (liftM (HasUniformFintype.uniformFintype α : m α) : PMF α) = PMF.uniformOfFintype α

attribute [simp] LawfulUniformFintype.liftM_uniformFintype

instance {m} [Monad m] [HasUniformFintype m] : HasUniformFinset m where
  uniformFinset {_} s hs :=
    letI : Nonempty {x // x ∈ s} := hs.coe_sort
    HasUniformFintype.uniformFintype {x // x ∈ s} >>= fun x => pure x.val

instance {m} [Monad m] [MonadLiftT m PMF] [LawfulMonadLiftT m PMF]
    [HasUniformFintype m] [LawfulUniformFintype m] : LawfulUniformFinset m where
  liftM_uniformFinset {α} s hs := by
    simp only [HasUniformFinset.uniformFinset, liftM_bind,
      LawfulUniformFintype.liftM_uniformFintype, liftM_pure, PMF.monad_pure_eq_pure]
    exact Cslib.Probability.PMF.map_subtypeVal_uniformOfFintype s hs

noncomputable instance : HasUniformFintype PMF where
  uniformFintype := PMF.uniformOfFintype

noncomputable instance : LawfulUniformFintype PMF where
  liftM_uniformFintype _ _ := rfl

end uniformFintype

end Cslib.Probability
