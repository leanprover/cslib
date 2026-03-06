/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Basic

namespace Turing

/-- Dyadic encoding of natural numbers. -/
public def dyadic (n : ℕ) : List Char :=
  if n = 0 then []
  else if Even n then
    dyadic (n / 2 - 1) ++ ['2']
  else
    dyadic ((n - 1) / 2) ++ ['1']

/-- Dyadic decoding of natural numbers. -/
public def dyadic_inv : List Char → Option ℕ := sorry

@[simp, grind =]
public lemma dyadic_inv_zero : dyadic_inv [] = .some 0 := by
  sorry

@[simp, grind =]
public lemma dyadic_inv_dyadic (n : ℕ) : dyadic_inv (dyadic n) = n := by sorry

--- Parenthesis nesting depth
public def parenDepth (s : List Char) : ℕ :=
  (s.foldl
    (fun (cur, maxDepth) c =>
      if c = '(' then (cur + 1, max maxDepth (cur + 1))
      else if c = ')' then (cur - 1, maxDepth)
      else (cur, maxDepth))
    (0, 0)).2

@[simp]
lemma parenDepth_of_no_parens {s : List Char} (h : '(' ∉ s ∧ '(' ∉ s) :
    parenDepth s = 0 := by
  unfold parenDepth
  induction s with
  | nil => simp
  | cons c s ih => grind

--- Encoding of a type into a parenthesized structure of limited nesting depth.
public class StrEnc (α : Type*) where
  encInner : α → List Char
  maxDepth : ℕ
  /-- For non-recursive inductive types: `fieldDepths[i][j] = StrEnc.depth` of the `j`-th field
      of the `i`-th constructor. -/
  fieldDepths : Array (Array ℕ)
  hDepth : ∀ w, parenDepth (encInner w) ≤ depth
  hInj : encInner.Injective

/-- Encoding of a value of type α. -/
public def StrEnc.enc {α : Type*} [StrEnc α] (w : α) : List Char :=
  ['('] ++ (encInner w) ++ [')']

/-- Convenience accessor: depth bound of the `j`-th field of the `i`-th constructor of `α`.
    Returns 0 if the indices are out of range. -/
def StrEnc.fieldDepth (α : Type*) [StrEnc α] (ctorIdx fieldIdx : ℕ) : ℕ :=
  ((StrEnc.fieldDepths (α := α))[ctorIdx]? |>.getD #[])[fieldIdx]? |>.getD 0

public instance (α : Type*) [StrEnc α] : StrEnc (List α) where
  encInner l := List.flatten (l.map StrEnc.enc)
  maxDepth := (StrEnc.maxDepth α) + 1
  fieldDepths := [].toArray
  hDepth := sorry
  hInj := sorry

public instance : StrEnc ℕ where
  encInner := dyadic
  maxDepth := 0
  fieldDepths := [].toArray
  hDepth := by sorry -- TODO use parenDepth_of_no_parens
  hInj := sorry

-- TODO create a derive method for all non-recursive types.

end Turing
