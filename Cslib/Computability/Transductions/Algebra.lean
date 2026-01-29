/-
Copyright (c) 2026 William (Liam) Schilling. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William (Liam) Schilling
-/

module

public import Cslib.Init
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

/-! ## Left GCD Monoids

A left GCD monoid is a generalization of `GCDMonoid` that relaxes commutativity.

A GCD will be necessary for defining the tail function of a transduction,
but commutativity is too strict to accommodate cases we care about
such as string-to-string transduction.
-/

namespace Semigroup

variable {α : Type*} [Semigroup α]

/-- Extract a witness of `a ∣ b`, that is, a result of left-dividing `b` by `a`. -/
noncomputable def divl (a b : α) (h : a ∣ b) : α :=
  Classical.choose h

/-- Multiplying `a` with a left-quotient of `b` by `a` yields `b`. -/
theorem divl_spec (a b : α) (h : a ∣ b) : b = a * divl a b h :=
  Classical.choose_spec h

end Semigroup

/-- Left GCD monoid:
a `Monoid` with a `gcdl` (greatest common left divisor) for pairs of elements. -/
class LeftGCDMonoid (α : Type*) [LeftCancelMonoid α] where
  /-- The greatest common divisor between two elements. -/
  gcdl : α → α → α
  /-- The GCD is a divisor of the first element. -/
  gcdl_dvd_left : ∀ a b, gcdl a b ∣ a
  /-- The GCD is a divisor of the second element. -/
  gcdl_dvd_right : ∀ a b, gcdl a b ∣ b
  /-- Any common divisor of both elements is a divisor of the GCD. -/
  dvd_gcdl : ∀ {a b c}, a ∣ c → a ∣ b → a ∣ gcdl c b
  /-- The GCD should be specified up to unordered pairs of element. -/
  gcdl_comm : ∀ a b, gcdl a b = gcdl b a

/-- Left GCD-of-set monoid:
a `Monoid` with `sgcdl` (greatest common left divisor) for sets of elements. -/
class LeftSetGCDMonoid (α : Type*) [LeftCancelMonoid α] extends LeftGCDMonoid α where
  /-- The greatest common divisor between a set of elements. -/
  sgcdl : Set α → α
  /-- The GCD is a divisor of any contained element. -/
  sgcdl_dvd : ∀ A, ∀ a ∈ A, sgcdl A ∣ a
  /-- Any common divisor of all elements is a divisor of the GCD. -/
  dvd_sgcdl : ∀ A {a}, (∀ b ∈ A, a ∣ b) → a ∣ sgcdl A
  /-- The set GCD agrees with the pair GCD. -/
  sgcdl_eq_gcdl : ∀ a b, sgcdl {a, b} = gcdl a b

namespace LeftSetGCDMonoid

variable {α ι : Type*} [LeftCancelMonoid α] [LeftSetGCDMonoid α]

/-- Indexed version of the set GCD function `sgcdl`. -/
def igcdl (s : ι → α) : α :=
  sgcdl (Set.range s)

/-- The GCD is a divisor of any contained element. -/
theorem igcdl_dvd (s : ι → α) : ∀ i, igcdl s ∣ s i := by
  intro
  apply sgcdl_dvd
  apply Set.mem_range_self

/-- Any common divisor of all elements is a divisor of the GCD. -/
theorem dvd_igcdl (s : ι → α) {a} : (∀ i, a ∣ s i) → a ∣ igcdl s := by
  intro h_dvd
  apply dvd_sgcdl
  intro _ h_mem
  rcases Set.mem_range.mp h_mem with ⟨_, h_mem⟩
  rw [←h_mem]
  apply h_dvd

end LeftSetGCDMonoid
