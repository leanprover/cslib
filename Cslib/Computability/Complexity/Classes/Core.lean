/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.SingleTapeTuring.Basic

@[expose] public section

/-!
# Complexity Class Core Definitions

This file contains shared language-level definitions used by both
time and space complexity classes.

## Main Definitions

* `Decides f L` — `f` decides language `L` (non-empty output means accept)
* `Verifies verify L p` — `verify` verifies language `L` with polynomial witness bound `p`
-/

variable {Symbol : Type}

namespace Cslib.Complexity

/--
A function `f : List Symbol → List Symbol` **decides** a language `L` when
membership in `L` corresponds to `f` producing non-empty output.
-/
def Decides (f : List Symbol → List Symbol) (L : Set (List Symbol)) : Prop :=
  ∀ x, x ∈ L ↔ f x ≠ []

/--
A verifier `verify` **verifies** a language `L` with polynomial witness bound `p` when
membership in `L` is equivalent to the existence of a short witness `w` such that
`verify (x ++ w)` produces non-empty output.
-/
-- TODO: The verifier receives `x ++ w` as a bare concatenation, so it cannot
-- distinguish the input/witness boundary. A more robust formulation would use
-- a two-tape machine with a separate read-only witness tape.
def Verifies (verify : List Symbol → List Symbol) (L : Set (List Symbol))
    (p : Polynomial ℕ) : Prop :=
  ∀ x, x ∈ L ↔ ∃ w : List Symbol, w.length ≤ p.eval x.length ∧ verify (x ++ w) ≠ []

end Cslib.Complexity

end
