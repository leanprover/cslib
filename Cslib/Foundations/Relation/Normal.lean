/-
Copyright (c) 2026 Fabrizio Montesi and Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Relation.Defs

/-! # Relations: properties of normalisation -/

@[expose] public section

namespace Relation

/-- Strong normalisation implies reachability of a normal form. -/
theorem sn_reaches_normal (h : SN r a) : ∃ b, ReflTransGen r a b ∧ Normal r b := by
  induction h with
  | intro a _ ih =>
    by_cases hstep : ∃ b, r a b
    · rcases hstep with ⟨b, hab⟩
      rcases ih b hab with ⟨c, hbc, hnormal⟩
      exact ⟨c, Relation.ReflTransGen.head hab hbc, hnormal⟩
    · exact ⟨a, .refl, hstep⟩

end Relation
