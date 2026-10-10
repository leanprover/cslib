/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Init

/-!
# Fixed-length bit strings and Boolean functions

A bit string is indexed by its coordinates, so selecting or updating one bit uses the usual
functions on `Fin n → Bool`.
-/

@[expose] public section

namespace Cslib

/-- A string of `n` bits, indexed by its coordinates. -/
abbrev BitString (n : ℕ) : Type := Fin n → Bool

/-- A Boolean function of `n` input bits. -/
abbrev BooleanFunction (n : ℕ) : Type := BitString n → Bool

end Cslib
