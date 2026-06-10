/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Defs

/-! # Axiom Schemata for Propositional Logic

This module defines the axiom schemata for the propositional Hilbert-style proof system.

## Main Definition

- `PropositionalAxiom`: An inductive type enumerating the 4 axiom schemata of classical
  propositional logic: `implyK` (weakening), `implyS` (distribution), `efq` (ex falso),
  and `peirce` (Peirce's law / classical reasoning).

## References

* Cslib/Logics/Modal/Metalogic/DerivationTree.lean -- modal axiom pattern (first 4 constructors)
-/

@[expose] public section

namespace Cslib.Logic.PL

variable {Atom : Type*}

/-- Axiom schemata for classical propositional logic.

The 4 axiom constructors are:
- **implyK** (weakening): `φ → (ψ → φ)`
- **implyS** (distribution): `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`
- **efq** (ex falso quodlibet): `⊥ → φ`
- **peirce** (Peirce's law): `((φ → ψ) → φ) → φ`

Together with modus ponens, these axioms characterize classical propositional logic. -/
inductive PropositionalAxiom : PL.Proposition Atom → Prop where
  /-- Weakening: `φ → (ψ → φ)` -/
  | implyK (φ ψ : PL.Proposition Atom) :
      PropositionalAxiom (φ.imp (ψ.imp φ))
  /-- Distribution: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))` -/
  | implyS (φ ψ χ : PL.Proposition Atom) :
      PropositionalAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))
  /-- Ex falso quodlibet: `⊥ → φ` -/
  | efq (φ : PL.Proposition Atom) :
      PropositionalAxiom (Proposition.bot.imp φ)
  /-- Peirce's law / DNE: `((φ → ψ) → φ) → φ` -/
  | peirce (φ ψ : PL.Proposition Atom) :
      PropositionalAxiom (((φ.imp ψ).imp φ).imp φ)

end Cslib.Logic.PL
