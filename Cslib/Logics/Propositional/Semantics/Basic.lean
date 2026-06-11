/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Defs

/-! # Bivalent Truth-Value Semantics for Propositional Logic

This module defines bivalent truth-value semantics for classical propositional logic.

## Main Definitions

- `Valuation`: A (bivalent) propositional valuation assigns a truth value to each atom.
- `Evaluate`: Evaluate a proposition under a valuation (recursive, 3 cases: atom/bot/imp).
- `Tautology`: A proposition is a tautology iff it is true under every valuation.

## References

* [A. Chagrov, M. Zakharyaschev,
  *Modal Logic*][ChagrovZakharyaschev1997],
  Section 1.2, Definition 1.5
-/

@[expose] public section

namespace Cslib.Logic.PL

variable {Atom : Type*}

/-- A (bivalent) propositional valuation assigns a truth value to each atom. -/
abbrev Valuation (Atom : Type*) := Atom → Prop

/-- Evaluate a proposition under a valuation.

This is the propositional specialization of modal `Satisfies`, without the box case. -/
def Evaluate (v : Valuation Atom) : PL.Proposition Atom → Prop
  | .atom x => v x
  | .bot => False
  | .imp a b => Evaluate v a → Evaluate v b

/-- A proposition is a tautology iff it is true under every valuation. -/
def Tautology (φ : PL.Proposition Atom) : Prop :=
  ∀ (v : Valuation Atom), Evaluate v φ

end Cslib.Logic.PL
