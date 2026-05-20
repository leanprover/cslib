/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Init
public import Mathlib.Probability.Distributions.Uniform

/-!
# Monads with Uniform Selection

This file defines general typeclasses for asserting that a monad `m` with an embedding into `PMF`
can model computations that lift to uniform distributions in `PMF`.

## Main Definitions

- `Cslib.Probability.HasUniformSelectFinset`: monad supports uniform finset selection
- `Cslib.Probability.HasUniformSelectFintype`: monad supports uniform finite types

-/

@[expose] public section

namespace Cslib.Probability

universe u v

/-- The monad `m` has a way to model uniform selection over non-empty finsets. -/
class HasUniformSelectFinset (m : Type u → Type*) [MonadLiftT m PMF] where
  uniformSelectFinset {α : Type u} (s : Finset α) (hs : s.Nonempty) : m α
  liftM_uniformSelectFinset {α : Type u} (s : Finset α) (hs : s.Nonempty) :
    (uniformSelectFinset s hs : PMF α) = PMF.uniformOfFinset s hs

attribute [simp] HasUniformSelectFinset.liftM_uniformSelectFinset

noncomputable instance : HasUniformSelectFinset PMF where
  uniformSelectFinset := PMF.uniformOfFinset
  liftM_uniformSelectFinset _ _ := rfl

/-- The monad `m` has a way to model uniform selection over non-empty finsets. -/
class HasUniformSelectFintype (m : Type u → Type*) [MonadLiftT m PMF] where
  uniformSelectFintype (α : Type u) [Fintype α] [Nonempty α] : m α
  liftM_uniformSelectFinset (α : Type u) [Fintype α] [Nonempty α] :
    (uniformSelectFintype α : PMF α) = PMF.uniformOfFintype α

attribute [simp] HasUniformSelectFinset.liftM_uniformSelectFinset

noncomputable instance : HasUniformSelectFintype PMF where
  uniformSelectFintype := PMF.uniformOfFintype
  liftM_uniformSelectFinset _ _ := rfl

end Cslib.Probability
