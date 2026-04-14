/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module

public import Cslib.Init
public import Mathlib.Data.Part

@[expose] public section

/-!
# Auxiliary lemmas for `Part`

Convenience lemmas for working with partial values from `Mathlib.Data.Part`.

Note: this file may go away entirely if leanprover-community/mathlib4#37521 gets merged.
-/

namespace Part

/-- Extract witnesses from a bind that equals `Part.some`. -/
theorem eq_some_of_bind_eq_some {a : Part α} {g : α → Part β} {m : β}
    (h : (a >>= g) = Part.some m) :
    ∃ x, a = Part.some x ∧ g x = Part.some m := by
  have hm := Part.mem_bind_iff.mp (h ▸ Part.mem_some m)
  exact hm.imp fun x ⟨hx, hm⟩ => ⟨Part.eq_some_iff.mpr hx, Part.eq_some_iff.mpr hm⟩

end Part
