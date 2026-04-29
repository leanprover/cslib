/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Basic
public import Mathlib.Data.FinEnum

namespace Turing

public instance : Fintype Char where
  elems := (Finset.range 0x110000).attach.image fun ⟨n, _⟩ =>
    if h : n.isValidChar then Char.ofNatAux n h else default
  complete c := by
    have hN : c.val.toNat < 0x110000 := by
      rcases c.valid with h | ⟨_, h⟩
      · exact Nat.lt_trans h (by decide)
      · exact h
    rw [Finset.mem_image]
    refine ⟨⟨c.val.toNat, Finset.mem_range.mpr hN⟩, Finset.mem_attach _ _, ?_⟩
    have hv : c.val.toNat.isValidChar := c.valid
    simp only [hv, ↓reduceDIte]
    apply Char.ext
    change (Char.ofNatAux c.val.toNat hv).val = c.val
    cases c with | _ val _ => cases val with | _ bv => simp [Char.ofNatAux]

/-- Dyadic encoding of natural numbers. -/
@[expose]
public def dyadic (n : ℕ) : List Char :=
  if n = 0 then []
  else if Even n then
    dyadic (n / 2 - 1) ++ ['2']
  else
    dyadic ((n - 1) / 2) ++ ['1']

/-- Dyadic decoding of natural numbers. -/
@[expose]
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

public lemma dyadic_mem_chars {c : Char} {n : ℕ} (h : c ∈ dyadic n) :
    c = '1' ∨ c = '2' := by
  induction n using Nat.strongRecOn with
  | _ n ih => grind [dyadic]

end Turing
