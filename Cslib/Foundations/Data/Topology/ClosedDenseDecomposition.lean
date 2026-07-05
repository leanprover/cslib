/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Mathlib.Topology.Closure

/-!
# Closed-dense decomposition

Every set in a topological space is the intersection of a closed set and a dense set.
-/

@[expose] public section

namespace Cslib

open Set

variable {X : Type*} [TopologicalSpace X]

/-- `ClosedDenseDecomposition s sc sd` means that `sc` is a closed set, `sd` is a dense set,
and `sc ∩ sd = s`. -/
def ClosedDenseDecomposition (s sc sd : Set X) : Prop :=
  IsClosed sc ∧ Dense sd ∧ sc ∩ sd = s

/-- Every set `s` in a topological space is the intersection of the closed set `closure s`
and the dense set `s ∪ (closure)ᶜ`. -/
theorem ClosedDenseDecomposition_exists (s : Set X) :
    ClosedDenseDecomposition s (closure s) (s ∪ (closure s)ᶜ) := by
  split_ands
  · exact isClosed_closure
  · simp only [dense_iff_closure_eq, closure_union, ← compl_subset_iff_union, subset_closure]
  · simp [inter_union_distrib_left, subset_closure]

end Cslib
