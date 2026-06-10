/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module
public import Cslib.Logics.Bimodal.ProofSystem.Derivation

/-! # Linearity Derived Facts

This module documents the linearity analysis for TM logic and provides
derived consequences of the `temp_linearity` axiom.

## Non-Derivability of Linearity from Original TM Axioms

**Theorem (informal)**: The linearity schema
  `F(phi) and F(psi) ->
     F(phi and psi) or F(phi and F(psi)) or F(F(phi) and psi)`
is NOT derivable from the base TM axioms.

**Counterexample**: Consider the frame with 3 points {0, 1a, 1b}
where:
- The temporal relation is: 0 R 1a, 0 R 1b (strict, irreflexive)
  (but NOT 1a R 1b or 1b R 1a)
- The S5 modal accessibility is universal

This frame satisfies all base TM axioms but is not linearly ordered:
1a and 1b are incomparable.

The linearity schema fails: at point 0, let phi be true only at 1a
and psi be true only at 1b. Then F(phi) and F(psi) hold at 0, but
none of the three disjuncts hold.

## Resolution: temp_linearity Axiom

The `temp_linearity` axiom was added to enforce linearity of the
temporal order. The past version is derivable via temporal duality.

## References

- Goldblatt 1992, *Logics of Time and Computation*
- Blackburn, de Rijke, Venema 2001, *Modal Logic*
-/

@[expose] public section

namespace Cslib.Logic.Bimodal

open Cslib.Logic.Bimodal
open DerivationTree

variable {Atom : Type u}

/--
The temporal linearity axiom as a derivation from the empty context.

This provides a convenient way to use the linearity axiom in proofs.
The `temp_linearity` axiom is a base axiom (valid on all linear
orders), so it is available at any frame class via `trivial`.
-/
noncomputable def tempLinearityDerivation
    (phi psi : Formula Atom) :
    ([] : Context Atom) ⊢
      (Formula.and (Formula.someFuture phi)
        (Formula.someFuture psi) |>.imp
      (Formula.or
        (Formula.someFuture (Formula.and phi psi))
        (Formula.or
          (Formula.someFuture
            (Formula.and phi (Formula.someFuture psi)))
          (Formula.someFuture
            (Formula.and
              (Formula.someFuture phi) psi))))) :=
  DerivationTree.axiom [] _
    (Axiom.temp_linearity phi psi) trivial

end Cslib.Logic.Bimodal
