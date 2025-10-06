/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
import Mathlib.Order.Notation

/-! # Propositions -/

universe u

variable {Atom : Type u} [DecidableEq Atom]

namespace PL

/-- Propositions. -/
inductive Proposition (Atom : Type u) : Type u where
  /-- Propositional atoms -/
  | atom (x : Atom)
  /-- Conjunction -/
  | conj (a b : Proposition Atom)
  /-- Disjunction -/
  | disj (a b : Proposition Atom)
  /-- Implication -/
  | impl (a b : Proposition Atom)
deriving DecidableEq, BEq

instance instBotProposition [Bot Atom] : Bot (Proposition Atom) := ⟨.atom ⊥⟩
instance instInhabitedOfBot [Bot Atom] : Inhabited Atom := ⟨⊥⟩

/-- We view negation as a defined connective ~A := A → ⊥ -/
abbrev Proposition.neg [Bot Atom] : Proposition Atom → Proposition Atom := (Proposition.impl · ⊥)

/-- A fixed choice of a derivable proposition (of course any two are equivalent). -/
def Proposition.top [Inhabited Atom] : Proposition Atom := impl (.atom default) (.atom default)

instance instTopProposition [Inhabited Atom] : Top (Proposition Atom) := ⟨.top⟩

example [Bot Atom] : (⊤ : Proposition Atom) = Proposition.impl ⊥ ⊥ := rfl

@[inherit_doc] scoped infix:35 " ⋏ " => Proposition.conj
@[inherit_doc] scoped infix:35 " ⋎ " => Proposition.disj
@[inherit_doc] scoped infix:30 " ⟶ " => Proposition.impl
@[inherit_doc] scoped prefix:40 " ~ " => Proposition.neg

end PL
