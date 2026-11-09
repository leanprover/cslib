/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Init
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Data.Multiset.AddSub

/-! # Multiset utilities -/

@[expose] public section

namespace Multiset

variable {α : Type*}

instance : Std.Associative (α := Multiset α) (· + ·) := ⟨Multiset.add_assoc⟩

instance : Std.Commutative (α := Multiset α) (· + ·) := ⟨Multiset.add_comm⟩

instance : Std.LawfulIdentity (α := Multiset α) (· + ·) 0 where
  left_id := Multiset.zero_add
  right_id := Multiset.add_zero

/-- Compute a list representative of a submultiset by scanning a supplied list.
The resulting list preserves the order of the selected occurrences in the supplied list. -/
def scanToList [DecidableEq α] (l : List α) (s : Multiset α)
    (h : s ≤ (l : Multiset α)) : {l' : List α // (l' : Multiset α) = s} :=
  match l with
  | [] =>
    ⟨[], by
      have hs : s = 0 := Multiset.le_zero.mp (by simpa using h)
      simpa using hs.symm⟩
  | a :: l =>
    if ha : a ∈ s then
      have h' : s.erase a ≤ (l : Multiset α) := by
        apply Multiset.erase_le_iff_le_cons.mpr
        simpa using h
      let l' := scanToList l (s.erase a) h'
      ⟨a :: l'.1, by
        change a ::ₘ (l'.1 : Multiset α) = s
        rw [l'.2]
        exact Multiset.cons_erase ha⟩
    else
      have h' : s ≤ (l : Multiset α) := by
        have he : s.erase a ≤ (l : Multiset α) := by
          apply Multiset.erase_le_iff_le_cons.mpr
          simpa using h
        simpa [Multiset.erase_of_notMem ha] using he
      scanToList l s h'

end Multiset
