/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Basic

namespace Turing

public instance : Fintype Char := by
  have h_zero_valid : Nat.isValidChar 0 := by decide
  exact Fintype.ofSurjective
    (fun n : Fin 0x110000 =>
      if h : Nat.isValidChar n.val
      then (⟨⟨⟨n.val, by omega⟩⟩, h⟩ : Char)
      else (⟨⟨⟨0, by omega⟩⟩, h_zero_valid⟩ : Char))
    (fun c => by
      refine ⟨⟨c.val.toNat, ?_⟩, ?_⟩
      · have := c.valid; simp at this; omega
      · simp only [dif_pos c.valid]; ext; simp)

/-- Dyadic encoding of natural numbers. -/
public def dyadic (n : ℕ) : List Char :=
  if n = 0 then []
  else if Even n then
    dyadic (n / 2 - 1) ++ ['2']
  else
    dyadic ((n - 1) / 2) ++ ['1']

/-- Dyadic decoding of natural numbers. -/
public def dyadic_inv (l : List Char) : Option ℕ :=
  l.foldlM (fun acc c =>
    if c = '1' then some (2 * acc + 1)
    else if c = '2' then some (2 * acc + 2)
    else none) 0

@[simp, grind =]
public lemma dyadic_inv_zero : dyadic_inv [] = .some 0 := by
  unfold dyadic_inv; rfl

@[simp, grind =]
public lemma dyadic_inv_dyadic (n : ℕ) : dyadic_inv (dyadic n) = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    unfold dyadic
    split
    · subst_vars; simp [dyadic_inv]
    · next h_nz =>
      split <;> rename_i h_parity <;>
        simp only [dyadic_inv, List.foldlM_append, Option.bind_eq_bind] <;>
        rw [show List.foldlM _ 0 _ = dyadic_inv (dyadic _) from rfl,
            ih _ (by omega)] <;>
        simp
      · obtain ⟨m, hm⟩ := h_parity; omega
      · obtain ⟨m, hm⟩ := Nat.not_even_iff_odd.mp h_parity; omega

end Turing
