/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Foundations.Data.Polynomial.Growth

/-!
# Polynomial bounds relative to a size

`PolynomiallyBoundedIn t size` means that `t` is bounded by a polynomially bounded function of
`size`. Running times of machines are bounded this way in the length of their input. The
closure rules let `fun_prop` accept any polynomial expression in the size, as well as a
function already known to have polynomial growth applied to such an expression.

The bounded function comes first because `fun_prop` takes the first explicit function argument
of a predicate as the function it reasons about.
-/

@[expose] public section

namespace Cslib

variable {α : Type*} {size t u : α → ℕ}

/-- `t` is bounded by a polynomially bounded function of `size`. -/
@[fun_prop] def PolynomiallyBoundedIn (t size : α → ℕ) : Prop :=
  ∃ b : ℕ → ℕ, PolynomiallyBounded b ∧ ∀ x, t x ≤ b (size x)

namespace PolynomiallyBoundedIn

/-- Any pointwise smaller function has the same bound. -/
theorem mono (hu : PolynomiallyBoundedIn u size) (h : ∀ x, t x ≤ u x) :
    PolynomiallyBoundedIn t size :=
  let ⟨b, hb, hub⟩ := hu
  ⟨b, hb, fun x => (h x).trans (hub x)⟩

/-- The size is bounded by itself. -/
theorem self : PolynomiallyBoundedIn size size :=
  ⟨fun n => n, by fun_prop, fun _ => le_rfl⟩

/-- The length of a list is bounded in the length. Stated for `List.length` itself so that
`fun_prop` finds it while decomposing an expression. -/
@[fun_prop] theorem length {β : Type*} :
    PolynomiallyBoundedIn (List.length (α := β)) List.length := self

/-- Constants are bounded in any size. -/
@[fun_prop] theorem const (c : ℕ) : PolynomiallyBoundedIn (fun _ => c) size :=
  ⟨fun _ => c, by fun_prop, fun _ => le_rfl⟩

/-- Applying a function of polynomial growth to a bounded function. The outer hypothesis is
stated with `PolynomiallyBounded` directly, so that `fun_prop` can use a local hypothesis
without a further transition. -/
@[fun_prop] theorem comp {b : ℕ → ℕ} (hb : PolynomiallyBounded b)
    (ht : PolynomiallyBoundedIn t size) : PolynomiallyBoundedIn (fun x => b (t x)) size := by
  obtain ⟨c, hc, htc⟩ := ht
  obtain ⟨p, hp, hpb, hbp⟩ := hb.exists_monotone
  exact ⟨fun n => p (c n), by fun_prop, fun x => (hbp _).trans (hp (htc x))⟩

/-- Sums of bounded functions are bounded. -/
@[fun_prop] theorem add (ht : PolynomiallyBoundedIn t size) (hu : PolynomiallyBoundedIn u size) :
    PolynomiallyBoundedIn (fun x => t x + u x) size := by
  obtain ⟨b, hb, htb⟩ := ht
  obtain ⟨c, hc, huc⟩ := hu
  exact ⟨fun n => b n + c n, by fun_prop, fun x => Nat.add_le_add (htb x) (huc x)⟩

/-- Products of bounded functions are bounded. -/
@[fun_prop] theorem mul (ht : PolynomiallyBoundedIn t size) (hu : PolynomiallyBoundedIn u size) :
    PolynomiallyBoundedIn (fun x => t x * u x) size := by
  obtain ⟨b, hb, htb⟩ := ht
  obtain ⟨c, hc, huc⟩ := hu
  exact ⟨fun n => b n * c n, by fun_prop, fun x => Nat.mul_le_mul (htb x) (huc x)⟩

/-- Fixed powers of bounded functions are bounded. -/
@[fun_prop] theorem pow (ht : PolynomiallyBoundedIn t size) (k : ℕ) :
    PolynomiallyBoundedIn (fun x => t x ^ k) size := by
  obtain ⟨b, hb, htb⟩ := ht
  exact ⟨fun n => b n ^ k, by fun_prop, fun x => Nat.pow_le_pow_left (htb x) k⟩

end PolynomiallyBoundedIn
end Cslib
