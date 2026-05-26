/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Init

/-! # Tensor connective (⊗) -/

@[expose] public section

namespace Cslib.Logic

/-- The type `α` has a tensor connective (⊗). -/
class HasTensor (α : Type*) where
  /-- `a ⊗ b` is the multiplicative conjunction of `a` and `b`. -/
  tensor (a b : α) : α

@[inherit_doc] scoped infixr:35 " ⊗ " => HasTensor.tensor

end Cslib.Logic
