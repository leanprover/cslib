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

This file defines general typeclasses for asserting that a monad `m` with an embedding into `PMF`
can model computations that lift to uniform distributions in `PMF`.

## Main Definitions

- `Cslib.Probability.HasUniformBitVec`: monad supports uniform `BitVec n`
- `Cslib.Probability.HasUniformFinset`: monad supports uniform selection from a non-empty finset
- `Cslib.Probability.HasUniformFintype`: monad supports uniform selection from a finite type

-/

@[expose] public section

namespace Cslib.Probability

universe u v

/-- The monad `m` has a way to model uniform selection over `BitVec n`. -/
class HasUniformBitVec (m : Type → Type*) [MonadLiftT m PMF] where
  uniformBitVec (n : ℕ) : m (BitVec n)
  liftM_uniformBitVec (n : ℕ) : (uniformBitVec n : PMF _) = PMF.uniformOfFintype (BitVec n)

attribute [simp] HasUniformBitVec.liftM_uniformBitVec

/-- A uniform `Bool` derived from a single uniform bit. -/
def uniformBool {m : Type → Type*} [Monad m] [MonadLiftT m PMF]
    [HasUniformBitVec m] : m Bool :=
  do return (← HasUniformBitVec.uniformBitVec 1) == 0

/-- The monad `m` has a way to model uniform selection over non-empty finsets. -/
class HasUniformFinset (m : Type u → Type*) [MonadLiftT m PMF] where
  uniformFinset {α : Type u} (s : Finset α) (hs : s.Nonempty) : m α
  liftM_uniformFinset {α : Type u} (s : Finset α) (hs : s.Nonempty) :
    (uniformFinset s hs : PMF α) = PMF.uniformOfFinset s hs

attribute [simp] HasUniformFinset.liftM_uniformFinset

instance {m} [MonadLiftT m PMF] [HasUniformFinset m] : HasUniformBitVec m where
  uniformBitVec n :=
    HasUniformFinset.uniformFinset (Finset.univ : Finset (BitVec n)) Finset.univ_nonempty
  liftM_uniformBitVec _ := by
    rw [HasUniformFinset.liftM_uniformFinset]; rfl

/-- The monad `m` has a way to model uniform selection over inhabited finite types. -/
class HasUniformFintype (m : Type u → Type*) [MonadLiftT m PMF] where
  uniformFintype (α : Type u) [Fintype α] [Nonempty α] : m α
  liftM_uniformFintype (α : Type u) [Fintype α] [Nonempty α] :
    (uniformFintype α : PMF α) = PMF.uniformOfFintype α

attribute [simp] HasUniformFintype.liftM_uniformFintype

instance {m} [Monad m] [MonadLiftT m PMF] [LawfulMonadLiftT m PMF]
    [HasUniformFintype m] : HasUniformFinset m where
  uniformFinset {α} s hs :=
    letI : Nonempty {x // x ∈ s} := hs.coe_sort
    HasUniformFintype.uniformFintype {x // x ∈ s} >>= fun x => pure x.val
  liftM_uniformFinset {α} s hs := by
    letI : Nonempty {x // x ∈ s} := hs.coe_sort
    simp only [liftM_bind, liftM_pure, HasUniformFintype.liftM_uniformFintype]
    change (PMF.uniformOfFintype {x // x ∈ s}).bind (PMF.pure ∘ Subtype.val) = _
    rw [PMF.bind_pure_comp]
    exact Cslib.Probability.PMF.map_subtypeVal_uniformOfFintype s hs

noncomputable instance : HasUniformFintype PMF where
  uniformFintype := PMF.uniformOfFintype
  liftM_uniformFintype _ _ := rfl

/-- The equivalence between `BitVec 1` and `Bool` via the predicate `· == 0`. -/
private def bitVecOneEquivBool : BitVec 1 ≃ Bool where
  toFun bv := bv == 0
  invFun b := bif b then 0 else 1
  left_inv := by decide
  right_inv := by decide

/-- The PMF coercion of `uniformBool` is the uniform distribution on `Bool`. -/
@[simp]
theorem liftM_uniformBool {m : Type → Type*} [Monad m] [MonadLiftT m PMF]
    [LawfulMonadLiftT m PMF] [HasUniformBitVec m] :
    (liftM (uniformBool : m Bool) : PMF Bool) = PMF.uniformOfFintype Bool := by
  simp only [uniformBool, liftM_bind, liftM_pure, HasUniformBitVec.liftM_uniformBitVec]
  change (PMF.uniformOfFintype (BitVec 1)).bind (PMF.pure ∘ bitVecOneEquivBool) = _
  rw [PMF.bind_pure_comp]
  exact Cslib.Probability.PMF.uniformOfFintype_map_equiv bitVecOneEquivBool

end Cslib.Probability
