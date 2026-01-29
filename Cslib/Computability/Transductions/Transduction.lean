/-
Copyright (c) 2026 William (Liam) Schilling. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William (Liam) Schilling
-/

module

public import Cslib.Computability.Transductions.Algebra

@[expose] public section

/-! # Transductions

A `Transduction` is a function from strings to elements (sometimes called weights)
which are typically from a `Monoid` or a `Semiring`.
A *string-to-string* transduction has output strings as its weights.
-/

namespace Cslib

open Semigroup LeftGCDSetMonoid

/- A transduction is a function with string inputs. -/
def Transduction (α β) :=
  List α → β

namespace Transduction

open scoped Function

variable {α β : Type*} [LeftCancelMonoid β] [LeftGCDSetMonoid β]

instance : CoeFun (Transduction α β) (fun _ ↦ List α → β) := ⟨fun f => f⟩

/-- The residual function of a transduction `f` after an input prefix `xs`
is the transduction from remaining input suffixes to outputs of `f`. -/
def residual (xs : List α) (f : Transduction α β) : Transduction α β :=
  fun ys => f (xs ++ ys)

/-- The prefix function of a transduction `f`
is the transduction from input prefixes to
the greatest prefix/divisor guarenteed to be output by `f`. -/
def pref (f : Transduction α β) : Transduction α β :=
  fun xs => igcdl (residual xs f)

/-- The prefix function outputs prefixes/divisors of the residual function. -/
theorem pref_dvd (f : Transduction α β) (xs ys : List α) : pref f xs ∣ residual xs f ys := by
  apply igcdl_dvd

/-- The prefix function outputs greatest prefixes/divisors of the residual function. -/
theorem dvd_pref (f : Transduction α β) (xs : List α) {b : β} :
    (∀ ys, b ∣ residual xs f ys) → b ∣ pref f xs := by
  intro
  apply dvd_igcdl
  assumption

/-- The tail function of a transduction `f` after an input prefix `xs`
is the transduction from remaining input suffixes to new output suffixes of `f` given `xs`. -/
noncomputable def tail (xs : List α) (f : Transduction α β) : Transduction α β :=
  fun ys => divl (pref f xs) (residual xs f ys) (pref_dvd f xs ys)

/-- Strings are tail-congruent with respect to `f` if they yield the same tail function of `f`.
That is, `f` behaves the same given either string as an input prefix. -/
def tailCongr (f : Transduction α β) : List α → List α → Prop :=
  (· = ·) on (tail · f)

/-- Tail congruence is an equivalence relation. -/
theorem tailCongr_iseqv (f : Transduction α β) : Equivalence (tailCongr f) := by
  apply eq_equivalence.comap

end Transduction

end Cslib
