/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Circuits.Formula.Basic

@[expose] public section

/-! # Formula Measures

Structural measures on Boolean formulas: size, depth, leaf count, and gate count.
These are purely structural — they depend only on the tree shape, not on the `Basis`
or evaluation semantics, so they require no typeclass constraints.

## Main definitions

- `Formula.size` — total number of nodes (leaves + gates)
- `Formula.depth` — longest root-to-leaf path length
- `Formula.leafCount` — number of variable leaves
- `Formula.gateCount` — number of gate nodes

## Main results

- `size_pos` — every formula has at least one node
- `size_map`, `depth_map` — variable renaming preserves size and depth
- `size_eq_leafCount_add_gateCount` — size decomposes as leaves + gates

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraB2009]
-/

namespace Cslib.Circuits

namespace Formula

variable {Var Var' : Type*} {Op : Type*}

/-- Total number of nodes in a formula. Each variable leaf and each gate contributes 1.
Equivalently, `size = leafCount + gateCount` (see `size_eq_leafCount_add_gateCount`). -/
@[simp, scoped grind =]
def size : Formula Var Op → Nat
  | .var _ => 1
  | .gate _ children => 1 + (children.map size).sum

/-- The depth of a formula: longest root-to-leaf path length. Variables have depth 0;
a gate's depth is one more than the maximum depth of its children. -/
@[simp, scoped grind =]
def depth : Formula Var Op → Nat
  | .var _ => 0
  | .gate _ children => 1 + (children.map depth).foldl max 0

/-- Number of variable leaves in a formula. Gates contribute 0; each `var` contributes 1. -/
@[simp, scoped grind =]
def leafCount : Formula Var Op → Nat
  | .var _ => 1
  | .gate _ children => (children.map leafCount).sum

/-- Number of gate nodes in a formula. Variables contribute 0; each `gate` contributes 1. -/
@[simp, scoped grind =]
def gateCount : Formula Var Op → Nat
  | .var _ => 0
  | .gate _ children => 1 + (children.map gateCount).sum

/-! ### Base case lemmas -/

@[scoped grind =]
theorem size_var (v : Var) : (.var v : Formula Var Op).size = 1 := by simp [size]

@[scoped grind =]
theorem depth_var (v : Var) : (.var v : Formula Var Op).depth = 0 := by simp [depth]

@[scoped grind =]
theorem leafCount_var (v : Var) : (.var v : Formula Var Op).leafCount = 1 := by simp [leafCount]

@[scoped grind =]
theorem gateCount_var (v : Var) : (.var v : Formula Var Op).gateCount = 0 := by simp [gateCount]

/-! ### Size is always positive -/

theorem size_pos (f : Formula Var Op) : 0 < f.size := by
  cases f with
  | var _ => simp [size]
  | gate _ _ => simp [size]; omega

/-! ### Mapping preserves measures -/

@[scoped grind =]
theorem size_map (g : Var → Var') (f : Formula Var Op) : (f.map g).size = f.size := by
  induction f using Formula.ind with
  | hvar _ => simp [map, size]
  | hgate op children ih =>
    simp only [map, size, List.map_map, Function.comp_def]
    rw [List.map_congr_left ih]

@[scoped grind =]
theorem depth_map (g : Var → Var') (f : Formula Var Op) : (f.map g).depth = f.depth := by
  induction f using Formula.ind with
  | hvar _ => simp [map, depth]
  | hgate op children ih =>
    simp only [map, depth, List.map_map, Function.comp_def]
    rw [List.map_congr_left ih]

/-! ### Size decomposition -/

private theorem list_sum_map_add {l : List α} {f g : α → Nat} :
    (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons _ _ ih => simp [List.sum_cons]; omega

@[scoped grind =]
theorem size_eq_leafCount_add_gateCount (f : Formula Var Op) :
    f.size = f.leafCount + f.gateCount := by
  induction f using Formula.ind with
  | hvar _ => simp [size, leafCount, gateCount]
  | hgate _ children ih =>
    simp only [size, leafCount, gateCount]
    rw [List.map_congr_left ih, list_sum_map_add]
    omega

end Formula

end Cslib.Circuits
