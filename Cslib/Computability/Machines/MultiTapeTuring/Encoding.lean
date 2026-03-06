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
  /-- Maps a value to the index of the constructor used to build it.
      For non-inductive types (e.g. `ℕ`, `List`), this is `fun _ => 0`. -/
  ctorIndex : α → ℕ
  /-- For inductive types, the inner encoding starts with the encoded
      constructor index: `encInner x = enc (ctorIndex x) ++ encFields x`.
      This is trivially true for types with `fieldDepths = #[]`. -/
  encFields : α → List Char
  hEncInner : ∀ w, fieldDepths.size > 0 →
    encInner w =
      (['('] ++ dyadic (ctorIndex w) ++ [')']) ++ encFields w
  hDepth : ∀ w, parenDepth (encInner w) ≤ depth
  hInj : encInner.Injective

/-- Encoding of a value of type α. -/
public def StrEnc.enc {α : Type*} [StrEnc α] (w : α) : List Char :=
  ['('] ++ (encInner w) ++ [')']

/-- Convenience accessor: depth bound of the `j`-th field of the `i`-th constructor of `α`.
    Returns 0 if the indices are out of range. -/
public def StrEnc.fieldDepth (α : Type*) [StrEnc α] (ctorIdx fieldIdx : ℕ) : ℕ :=
  ((StrEnc.fieldDepths (α := α))[ctorIdx]? |>.getD #[])[fieldIdx]? |>.getD 0

public instance (α : Type*) [StrEnc α] : StrEnc (List α) where
  encInner l := List.flatten (l.map StrEnc.enc)
  maxDepth := (StrEnc.maxDepth α) + 1
  fieldDepths := [].toArray
  ctorIndex := fun _ => 0
  encFields := fun _ => []
  hEncInner := by simp [Array.size]
  hDepth := sorry
  hInj := sorry

public instance : StrEnc ℕ where
  encInner := dyadic
  maxDepth := 0
  fieldDepths := [].toArray
  ctorIndex := fun _ => 0
  encFields := fun _ => []
  hEncInner := by simp [Array.size]
  hDepth := by sorry -- TODO use parenDepth_of_no_parens
  hInj := sorry

public instance : StrEnc Bool where
  encInner
    | false => StrEnc.enc 0
    | true => StrEnc.enc 1
  maxDepth := 1
  fieldDepths := #[#[], #[]]
  ctorIndex
    | false => 0
    | true => 1
  encFields := fun _ => []
  hEncInner := by sorry
  hDepth := sorry
  hInj := sorry

-- TODO create a derive method for all non-recursive types.

end Turing
