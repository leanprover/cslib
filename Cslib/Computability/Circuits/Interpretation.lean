/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuits.Signature

/-!
# Interpretations

An interpretation of a signature over a carrier type `Carrier` assigns to
every operation symbol a function from argument tuples, indexed by `Fin` of
the symbol's arity, to `Carrier`. Interpretations are plain functions rather
than a structure, so they can be built pointwise and specialized without any
wrapping.
-/

@[expose] public section

namespace Cslib.Circuits

/-- An interpretation assigns an operation on `Carrier` to every symbol in `σ`. -/
abbrev Interpretation (σ : Signature) Carrier :=
  (op : σ.Op) → (Fin (σ.Arity op) → Carrier) → Carrier

end Cslib.Circuits
