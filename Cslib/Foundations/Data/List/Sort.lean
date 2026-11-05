/-
Copyright (c) 2026 Robert Joseph George. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/
module

public import Cslib.Init
public import Mathlib.Data.List.Sort

/-! # Sorted permutations without antisymmetry

`List.Perm.eq_of_pairwise'` identifies two sorted lists that are permutations of each other
when the order is antisymmetric. Under a total preorder, two such lists can still order
equivalent elements differently. They are equal as soon as they list every equivalence class
in the same order; only reflexivity is needed for this.

## Main results

* `List.Perm.eq_of_pairwise_of_filter_eq`: two sorted permutations of each other are equal if,
  for every `k`, they list the elements mutually related to `k` in the same order.
-/

public section

namespace List

variable {α : Type*} {r : α → α → Prop} [DecidableRel r] [Std.Refl r]

/-- Two lists that are permutations of each other and both sorted for a reflexive relation `r`
are equal if, for every `k`, they list the elements mutually related to `k` in the same order.
For a total preorder these are the equivalence classes.

The two heads are mutually related, since each list is sorted and contains the other head; the
elements related to the first head then begin with both heads, so they coincide, and the tails
are handled by induction. -/
theorem Perm.eq_of_pairwise_of_filter_eq {l₁ l₂ : List α} (hp : l₁ ~ l₂)
    (h₁ : l₁.Pairwise r) (h₂ : l₂.Pairwise r)
    (hf : ∀ k, l₁.filter (fun x => decide (r x k ∧ r k x)) =
      l₂.filter (fun x => decide (r x k ∧ r k x))) :
    l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil => exact (nil_perm.mp hp).symm
  | cons a t ih =>
    obtain _ | ⟨b, u⟩ := l₂
    · exact absurd (perm_nil.mp hp) (cons_ne_nil a t)
    have hrefl : ∀ x, r x x := Std.Refl.refl
    have hab : r a b := by
      rcases mem_cons.mp (hp.mem_iff.mpr mem_cons_self) with rfl | hb
      · exact hrefl _
      · exact rel_of_pairwise_cons h₁ hb
    have hba : r b a := by
      rcases mem_cons.mp (hp.mem_iff.mp mem_cons_self) with rfl | ha
      · exact hrefl _
      · exact rel_of_pairwise_cons h₂ ha
    have hhead := hf a
    rw [filter_cons_of_pos (p := fun x => decide (r x a ∧ r a x))
        (decide_eq_true ⟨hrefl a, hrefl a⟩),
      filter_cons_of_pos (p := fun x => decide (r x a ∧ r a x)) (decide_eq_true ⟨hba, hab⟩)]
      at hhead
    obtain rfl := (cons.inj hhead).1
    refine congrArg (a :: ·) (ih (l₂ := u) ((perm_cons a).mp hp) h₁.of_cons h₂.of_cons
      fun k => ?_)
    have h := hf k
    by_cases hk : decide (r a k ∧ r k a) = true
    · rw [filter_cons_of_pos (p := fun x => decide (r x k ∧ r k x)) hk,
        filter_cons_of_pos (p := fun x => decide (r x k ∧ r k x)) hk] at h
      exact (cons.inj h).2
    · rw [filter_cons_of_neg (p := fun x => decide (r x k ∧ r k x)) hk,
        filter_cons_of_neg (p := fun x => decide (r x k ∧ r k x)) hk] at h
      exact h

end List
