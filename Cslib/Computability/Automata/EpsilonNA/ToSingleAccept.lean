/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Computability.Automata.EpsilonNA.Basic

/-! # Translation of εNA into εNA with a single accept state. -/

@[expose] public section

namespace Cslib.Automata.εNA.FinAcc

variable {State Symbol : Type*}

/-- Any `εNA.FinAcc` can be converted into an `εNA.FinAcc` with a single accept state `none`.
The original states are wrapped in `some`, and all original accept states have ε-transitions to
`none`. -/
@[scoped grind]
def toSingleAccept (a : εNA.FinAcc State Symbol) : εNA.FinAcc (Option State) Symbol where
  start := some '' a.start
  accept := {none}
  Tr
    | some s, x, some s' => a.Tr s x s'
    | some s, none, none => s ∈ a.accept
    | _, _, _ => False

open scoped LTS LTS.MTr LTS.STr LTS.SMTr

@[scoped grind →]
theorem toSingleAccept_tr_antiDerivative_isSome {a : εNA.FinAcc State Symbol}
    (h : a.toSingleAccept.Tr os x os') : os.isSome := by
  cases os with
  | none => simp only [toSingleAccept] at h
  | some _ => simp

@[scoped grind =]
theorem toSingleAccept_tr_tr {a : εNA.FinAcc State Symbol} :
    a.toSingleAccept.Tr (some s) x (some s') ↔ a.Tr s x s' := by
  simp [toSingleAccept]

@[scoped grind →]
theorem toSingleAccept_mTr_antiDerivative_isSome {a : εNA.FinAcc State Symbol}
    (hos' : os'.isSome) (h : a.toSingleAccept.MTr os x os') : os.isSome := by
  induction h
  case refl => grind only
  case stepL os x osb xs os' htr hmtr ih =>
    grind only [toSingleAccept_tr_antiDerivative_isSome htr]

@[scoped grind =]
theorem toSingleAccept_mTr_mTr {a : εNA.FinAcc State Symbol} :
    a.toSingleAccept.MTr (some s) xs (some s') ↔ a.MTr s xs s' := by
  induction xs generalizing s
  case nil => grind
  case cons x xs ih =>
    apply Iff.intro <;> intro h
    case mp =>
      cases h with
      | stepL => grind
    case mpr =>
      cases h
      case stepL sb htr hmtr =>
        apply LTS.MTr.stepL (s2 := some sb) <;> grind

@[scoped grind →]
theorem toSingleAccept_τSTr_antiDerivative_isSome {a : εNA.FinAcc State Symbol}
    (hos' : os'.isSome) (h : a.toSingleAccept.τSTr os os') : os.isSome := by
  induction h using Relation.ReflTransGen.head_induction_on
  case refl => exact hos'
  case head _ _ h₁ h₂ ih =>
    exact toSingleAccept_tr_antiDerivative_isSome h₁

@[scoped grind .]
theorem toSingleAccept_τSTr_τSTr {a : εNA.FinAcc State Symbol}
    (hos' : os' = some s') : a.toSingleAccept.τSTr (some s) os' ↔ a.τSTr s s' := by
  apply Iff.intro <;> intro h
  case mp =>
    induction h generalizing s'
    case refl =>
      cases hos'
      constructor
    case tail osb os' hτstr htr ih =>
      have hosb := toSingleAccept_τSTr_antiDerivative_isSome
        (os := osb) (os' := os') (by grind) (Relation.ReflTransGen.single htr)
      apply Option.isSome_iff_exists.mp at hosb
      rcases hosb with ⟨sb, hosb⟩
      apply Relation.ReflTransGen.trans (b := sb) (ih hosb)
      apply Relation.ReflTransGen.single
      rw [hosb, hos'] at htr
      apply htr
  case mpr =>
    induction h generalizing os'
    case refl =>
      cases hos'
      constructor
    case tail sb s' hτstr htr ih =>
      specialize ih (os' := some sb) rfl
      apply Relation.ReflTransGen.trans (b := some sb) ih
      apply Relation.ReflTransGen.single
      rw [hos']
      apply toSingleAccept_tr_tr.mpr htr

open Acceptor in
theorem toSingleAccept_language_eq {a : εNA.FinAcc State Symbol} :
    language a.toSingleAccept = language a := by sorry

end Cslib.Automata.εNA.FinAcc
