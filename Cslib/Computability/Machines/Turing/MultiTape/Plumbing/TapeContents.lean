/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Init
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Data.Finset.Attr
public import Mathlib.Data.Nat.SuccPred

/-! # Contiguous work-tape contents -/

@[expose] public section

namespace Turing.MultiTapeTM

variable {Symbol : Type*}

/-- A tape containing exactly the symbols of `xs` at positions `0, ..., xs.length - 1`. -/
def listTape (xs : List Symbol) : ℤ → Option Symbol
  | .ofNat n => xs[n]?
  | .negSucc _ => none

@[simp]
lemma listTape_ofNat (xs : List Symbol) (n : ℕ) : listTape xs n = xs[n]? := rfl

@[simp]
lemma listTape_negSucc (xs : List Symbol) (n : ℕ) : listTape xs (.negSucc n) = none := rfl

/-- Appending one output symbol writes precisely the cell after the existing output. -/
lemma listTape_append_single (xs : List Symbol) (x : Symbol) :
    listTape (xs ++ [x]) = Function.update (listTape xs) (xs.length : ℤ) (some x) := by
  funext z
  cases z with
  | negSucc n => simp [listTape]
  | ofNat n =>
      by_cases h : n = xs.length
      · subst n; simp
      · by_cases hn : n < xs.length
        · simp [List.getElem?_append, hn, h]
        · simp [List.getElem?_append, hn, h, show n - xs.length ≠ 0 by omega]

/-- Every position strictly inside a list tape is nonblank. -/
lemma listTape_isSome (xs : List Symbol) {p : ℤ} (hp : 0 ≤ p) (hlt : p < xs.length) :
    (listTape xs p).isSome := by
  lift p to ℕ using hp
  simp [listTape]
  omega

end Turing.MultiTapeTM
