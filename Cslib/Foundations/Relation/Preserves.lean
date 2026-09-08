/-
Copyright (c) 2026 Fabrizio Montesi and Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Relation.Defs
public import Mathlib.Logic.Function.Defs

/-! # Relations: preservation of properties -/

@[expose] public section

namespace Relation

open scoped Function

/-- A predicate preserved by a relation is also preserved by its reflexive closure. -/
@[simp, scoped grind =]
theorem preserves_reflGen_iff : Preserves (ReflGen r) P  ↔ Preserves r P := by grind [Preserves]

/-- A predicate preserved by a relation is also preserved by its transitive closure. -/
@[simp, scoped grind =]
theorem preserves_transGen_iff : Preserves (TransGen r) P ↔ Preserves r P := by
  constructor <;> intro h
  · grind [Preserves]
  · intro _ _ hxy
    induction hxy <;> grind [Preserves]

/-- A predicate is preserved by a relation iff it is preserves by its reflexive and transitive
closure. -/
@[simp, scoped grind =]
theorem preserves_reflTransGen_iff : Preserves (ReflTransGen r) P ↔ Preserves r P := by
  constructor <;> intro h
  · intro _ _ hab
    exact h (ReflTransGen.single hab)
  · change ReflTransGen r ≤ ((· ≤ ·) on P)
    exact reflTransGen_le_of_le h

end Relation
