/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module

public import Cslib.Init
public import Mathlib.Data.Part

/-!
# Auxiliary lemmas for `Part`

Convenience lemmas for working with partial values from `Mathlib.Data.Part`.

Note: this file can go away once CSLib's Mathlib pin includes leanprover-community/mathlib4#37521
(merged 2026-06-09), which adds the equivalent `Part.bind_eq_some_iff`.
-/

@[expose] public section

namespace Part

/-- `Part.bind` produces `some b` iff the input is `some a` and the continuation maps `a` to
`some b`. This is the `Part` analogue of `Option.bind_eq_some_iff`. -/
theorem bind_eq_some_iff {b : β} {x : Part α} {f : α → Part β} :
    x.bind f = some b ↔ ∃ a, x = some a ∧ f a = some b := by
  simp only [eq_some_iff, mem_bind_iff]

end Part
