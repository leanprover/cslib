/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Init

/-!
# Bit strings and Boolean functions

Bit strings are lists of bits. Boolean functions of a fixed number of input bits use
`Fin n → Bool`, with the usual coordinate selection and update operations.
-/

@[expose] public section

namespace Cslib

/-- A finite string of bits. -/
abbrev BitString : Type := List Bool

/-- A Boolean function of `n` input bits. -/
abbrev BooleanFunction (n : ℕ) : Type := (Fin n → Bool) → Bool

end Cslib
