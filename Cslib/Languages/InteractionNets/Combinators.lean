/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

module

public import Cslib.Languages.InteractionNets.Defs
public import Mathlib.Data.Fin.VecNotation

/-!
# Interaction Combinators

This file defines the interaction combinators of [Lafont1997] as an interaction system, in the
textual calculus of `Cslib.Languages.InteractionNets.Defs`.

There are three symbols: the constructor `con` (Lafont's `γ`) and the duplicator `dup` (`δ`), of
arity 2, and the eraser `era` (`ε`), of arity 0. There is one rule for each ordered pair of
symbols. Names are strings.

## Main definitions

- `Combinator`: the three symbols, indexed by their arity.
- `combinators`: the first-order language of the interaction combinators.
- `conCon`, `dupDup`, `eraEra`: the annihilation rules.
- `conDup`, `dupCon`, `conEra`, `eraCon`, `dupEra`, `eraDup`: the commutation rules.
- `interactionCombinators`: the interaction system made of the nine rules.

## Main statements

- `conCon_linear`, …, `eraEra_linear`: each of the nine rules is linear.

## References

* [Y. Lafont, *Interaction Combinators*][Lafont1997]
-/

@[expose] public section

namespace Cslib.InteractionNets

open FirstOrder Language

/-- The symbols of the interaction combinators, indexed by their arity. -/
inductive Combinator : ℕ → Type where
  /-- The constructor, Lafont's `γ`. -/
  | con : Combinator 2
  /-- The duplicator, Lafont's `δ`. -/
  | dup : Combinator 2
  /-- The eraser, Lafont's `ε`. -/
  | era : Combinator 0
  deriving DecidableEq

/-- The language of the interaction combinators: `con` and `dup` have two auxiliary ports, `era`
has none. There are no relation symbols. -/
def combinators : Language where
  Functions := Combinator
  Relations := fun _ => Empty

instance (n : ℕ) : DecidableEq (combinators.Functions n) :=
  inferInstanceAs (DecidableEq (Combinator n))

/-! ### Annihilation rules -/

/-- Annihilation of two `con`: the wires cross.
```
con(x₁, x₂) = con(y₁, y₂) ⇒
  x₁ = y₂
  x₂ = y₁
```
-/
def conCon : Rule combinators String Combinator.con Combinator.con where
  xNames := !["x1", "x2"]
  yNames := !["y1", "y2"]
  Δ := {
    s(var "x1", var "y2"),
    s(var "x2", var "y1")
  }

/-- Annihilation of two `dup`: the wires do not cross.
```
dup(x₁, x₂) = dup(y₁, y₂) ⇒
  x₁ = y₁
  x₂ = y₂
```
-/
def dupDup : Rule combinators String Combinator.dup Combinator.dup where
  xNames := !["x1", "x2"]
  yNames := !["y1", "y2"]
  Δ := {
    s(var "x1", var "y1"),
    s(var "x2", var "y2")
  }

/-- Annihilation of two `era`: nothing is left.
```
era = era ⇒
  (nothing)
```
-/
def eraEra : Rule combinators String Combinator.era Combinator.era where
  xNames := ![]
  yNames := ![]
  Δ := {}

/-! ### Commutation rules -/

/-- Commutation of `con` and `dup`: each agent is copied by the other one.
```
con(x₁, x₂) = dup(y₁, y₂) ⇒
  x₁ = dup(a, b)
  x₂ = dup(c, d)
  y₁ = con(a, c)
  y₂ = con(b, d)
```
-/
def conDup : Rule combinators String Combinator.con Combinator.dup where
  xNames := !["x1", "x2"]
  yNames := !["y1", "y2"]
  Δ := {
    s(var "x1", func Combinator.dup ![var "a", var "b"]),
    s(var "x2", func Combinator.dup ![var "c", var "d"]),
    s(var "y1", func Combinator.con ![var "a", var "c"]),
    s(var "y2", func Combinator.con ![var "b", var "d"])
  }

/-- Commutation of `dup` and `con`: the rule `conDup` read from the other side.
```
dup(x₁, x₂) = con(y₁, y₂) ⇒
  x₁ = con(a, b)
  x₂ = con(c, d)
  y₁ = dup(a, c)
  y₂ = dup(b, d)
```
-/
def dupCon : Rule combinators String Combinator.dup Combinator.con where
  xNames := !["x1", "x2"]
  yNames := !["y1", "y2"]
  Δ := {
    s(var "x1", func Combinator.con ![var "a", var "b"]),
    s(var "x2", func Combinator.con ![var "c", var "d"]),
    s(var "y1", func Combinator.dup ![var "a", var "c"]),
    s(var "y2", func Combinator.dup ![var "b", var "d"])
  }

/-- Commutation of `con` and `era`: the `con` is erased.
```
con(x₁, x₂) = era ⇒
  x₁ = era
  x₂ = era
```
-/
def conEra : Rule combinators String Combinator.con Combinator.era where
  xNames := !["x1", "x2"]
  yNames := ![]
  Δ := {
    s(var "x1", func Combinator.era ![]),
    s(var "x2", func Combinator.era ![])
  }

/-- Commutation of `era` and `con`: the `con` is erased.
```
era = con(y₁, y₂) ⇒
  y₁ = era
  y₂ = era
```
-/
def eraCon : Rule combinators String Combinator.era Combinator.con where
  xNames := ![]
  yNames := !["y1", "y2"]
  Δ := {
    s(var "y1", func Combinator.era ![]),
    s(var "y2", func Combinator.era ![])
  }

/-- Commutation of `dup` and `era`: the `dup` is erased.
```
dup(x₁, x₂) = era ⇒
  x₁ = era
  x₂ = era
```
-/
def dupEra : Rule combinators String Combinator.dup Combinator.era where
  xNames := !["x1", "x2"]
  yNames := ![]
  Δ := {
    s(var "x1", func Combinator.era ![]),
    s(var "x2", func Combinator.era ![])
  }

/-- Commutation of `era` and `dup`: the `dup` is erased.
```
era = dup(y₁, y₂) ⇒
  y₁ = era
  y₂ = era
```
-/
def eraDup : Rule combinators String Combinator.era Combinator.dup where
  xNames := ![]
  yNames := !["y1", "y2"]
  Δ := {
    s(var "y1", func Combinator.era ![]),
    s(var "y2", func Combinator.era ![])
  }

/-! ### The interaction system -/

/-- The interaction system of the interaction combinators: one rule for each pair of symbols. -/
def interactionCombinators : System combinators String where
  rule
    | .con, .con => some conCon
    | .con, .dup => some conDup
    | .con, .era => some conEra
    | .dup, .con => some dupCon
    | .dup, .dup => some dupDup
    | .dup, .era => some dupEra
    | .era, .con => some eraCon
    | .era, .dup => some eraDup
    | .era, .era => some eraEra

/-! ### Linearity of the rules -/

theorem conCon_linear : conCon.Linear :=
  conCon.linear_of_forall_mem (by decide) (by decide)

theorem conDup_linear : conDup.Linear :=
  conDup.linear_of_forall_mem (by decide) (by decide)

theorem conEra_linear : conEra.Linear :=
  conEra.linear_of_forall_mem (by decide) (by decide)

theorem dupCon_linear : dupCon.Linear :=
  dupCon.linear_of_forall_mem (by decide) (by decide)

theorem dupDup_linear : dupDup.Linear :=
  dupDup.linear_of_forall_mem (by decide) (by decide)

theorem dupEra_linear : dupEra.Linear :=
  dupEra.linear_of_forall_mem (by decide) (by decide)

theorem eraCon_linear : eraCon.Linear :=
  eraCon.linear_of_forall_mem (by decide) (by decide)

theorem eraDup_linear : eraDup.Linear :=
  eraDup.linear_of_forall_mem (by decide) (by decide)

theorem eraEra_linear : eraEra.Linear :=
  eraEra.linear_of_forall_mem (by decide) (by decide)

end Cslib.InteractionNets
