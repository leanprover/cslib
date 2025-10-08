/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Mathlib.Data.Nat.Notation
import Cslib.Foundations.Data.OmegaSequence

/-! # ω-lists (placeholder) -/

/-- An `ωList α` is an infinite list of elements of type `α`.

This file is just a stub. It is currently not possible to construct and manipulate nicely an
`ωList`, due to the current lack of support for coinduction in Lean.
This file keeps track of what can be defined and the relation to `ωSequence`.

Conceptually, at the time of this writing, `ωList` shares the same design goal of `Stream'` in
Mathlib. However, `Stream' α` is defined as `ℕ → α` (which is kept hidden by the API), in order
to get a working implementation.
-/
structure ωList (α : Type _) where
  head : α
  tail : ωList α

namespace ωList

/-- The ω-list where the first element is `x` and the tail is the ω-list `xs`. -/
def cons (a : α) (as : ωList α) : ωList α where
  head := a
  tail := as

/-- Returns the `i`-th element of the ω-list `as`. -/
def get : (as : ωList α) → (i : ℕ) → α
  | ⟨a, _⟩, 0 => a
  | ⟨_, as⟩, i + 1 => as.get i

/-- Translates an ω-list into an ω-sequence. -/
def toωSequence (as : ωList α) : ωSequence α := as.get

end ωList
