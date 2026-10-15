/-
Copyright (c) 2026 Yusuf Demir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yusuf Demir
-/

module

public import Cslib.Foundations.Data.List.Repeat

/-! # Extendable prefixes of right-maximal repeats

If every occurrence of a repeat `u` of `w` is followed by the same letter, appending that letter
to `u` does not change where it occurs. Doing this until two occurrences are followed by different
letters yields a right-maximal repeat `v`, the right extension of `u`. Following
[NogamiTerauchi2025], `u` is then called an extendable prefix of `v`.

## Main definitions

* `List.IsExtendablePrefix u v w`: `v` is a right-maximal repeat of `w` that starts with `u` and
  occurs wherever `u` occurs.

## Main statements

* `List.IsRepeat.exists_isExtendablePrefix`: every repeat is an extendable prefix of some
  right-maximal repeat.

## References

* [T. Nogami and T. Terauchi, *Efficient Matching of Some Fundamental Regular Expressions with
  Backreferences*][NogamiTerauchi2025]
-/

@[expose] public section

namespace List

variable {α : Type*} {u v w : List α} {i : ℕ}

/-- `u` is an extendable prefix of `v` in `w` if `v` is a right-maximal repeat of `w` that starts
with `u` and occurs wherever `u` occurs. In the notation of [NogamiTerauchi2025], this says that
the right extension of `u` is `v`. -/
structure IsExtendablePrefix (u v w : List α) : Prop where
  isPrefix : u <+: v
  isRightMaximalRepeat : v.IsRightMaximalRepeat w
  occursAt : ∀ i, u.OccursAt w i → v.OccursAt w i

/-- An extendable prefix occurs exactly where its right-maximal repeat occurs. -/
theorem IsExtendablePrefix.occursAt_iff (h : u.IsExtendablePrefix v w) :
    u.OccursAt w i ↔ v.OccursAt w i :=
  ⟨h.occursAt i, fun hv => hv.of_prefix h.isPrefix⟩

/-- A right-maximal repeat is an extendable prefix of itself. -/
theorem IsRightMaximalRepeat.isExtendablePrefix (h : v.IsRightMaximalRepeat w) :
    v.IsExtendablePrefix v w :=
  ⟨prefix_refl v, h, fun _ hi => hi⟩

/-- Every repeat is an extendable prefix of some right-maximal repeat. -/
theorem IsRepeat.exists_isExtendablePrefix (h : u.IsRepeat w) :
    ∃ v, u.IsExtendablePrefix v w := by
  generalize hk : w.length - u.length = k
  induction k using Nat.strong_induction_on generalizing u with
  | _ k ih =>
    by_cases hrm : u.IsRightMaximalRepeat w
    · exact ⟨u, hrm.isExtendablePrefix⟩
    obtain ⟨hu, i, j, hij, hi, hj⟩ := h
    have hsame : ∀ i' j', u.OccursAt w i' → u.OccursAt w j' →
        w[i' + u.length]? = w[j' + u.length]? := by
      intro i' j' hi' hj'
      by_contra hne
      exact hrm ⟨hu, i', j', hi', hj', hne⟩
    obtain ⟨c, hc⟩ : ∃ c, w[i + u.length]? = some c := by
      have := hi.add_length_le hu
      have := hj.add_length_le hu
      rcases Nat.lt_or_ge (i + u.length) w.length with h' | h'
      · exact ⟨_, getElem?_eq_getElem h'⟩
      · exact ⟨_, (hsame i j hi hj).trans (getElem?_eq_getElem (by omega))⟩
    have hext : ∀ i', u.OccursAt w i' → (u ++ [c]).OccursAt w i' := fun i' hi' =>
      occursAt_append_singleton_iff.mpr ⟨hi', (hsame i' i hi' hi).trans hc⟩
    have hne : u ++ [c] ≠ [] := by simp
    have hlt : w.length - (u ++ [c]).length < k := by
      have := (hext i hi).add_length_le hne
      simp only [length_append, length_singleton] at this ⊢
      omega
    obtain ⟨v, hv⟩ := ih _ hlt (u := u ++ [c]) ⟨hne, i, j, hij, hext i hi, hext j hj⟩ rfl
    exact ⟨v, ⟨(prefix_append u [c]).trans hv.isPrefix, hv.isRightMaximalRepeat,
      fun i' hi' => hv.occursAt i' (hext i' hi')⟩⟩

end List
