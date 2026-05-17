/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Init
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice

@[expose] public section

/-! # Ramsey theorem for infinite graphs

This result really should be in Mathlib, but currently it is not. We do expect
the Ramsey theorem for infinite hypergraphs to appear in Mathlib eventually and
this result to be derived as a corollary of the more general result.
-/

namespace Cslib

open Function Set

/-- An infinite pigeonhole principle. -/
theorem infinite_pigeonhole_principle {X Y : Type*} [Finite Y] (f : X → Y) {s : Set X}
    (h_inf : s.Infinite) : ∃ y, ∃ t, t.Infinite ∧ t ⊆ s ∧ ∀ x ∈ t, f x = y := by
  have := h_inf.to_subtype
  obtain ⟨y, h_inf'⟩ := Finite.exists_infinite_fiber (s.restrict f)
  have h_inf_iff := Equiv.infinite_iff <|
    Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ s) (fun x ↦ f x = y)
  simp only [coe_eq_subtype, mem_preimage, restrict_apply, mem_singleton_iff, h_inf_iff] at h_inf'
  have h_inf'' := (infinite_coe_iff (s := { x | x ∈ s ∧ f x = y })).mp h_inf'
  use y, {x | x ∈ s ∧ f x = y}
  grind

/-- An `InfVSet` consists of a set of vertices and a proof that the set is infinite. -/
private structure InfVSet (Vertex : Type*) where
  /-- A set of vertices. -/
  set : Set Vertex
  /-- A proof that `set` is infinite. -/
  inf : set.Infinite

/-- A `Selection` consists of an `InfVSet`, a vertex, and a color. -/
private structure Selection (Vertex Color : Type*) where
  /-- An infinite set of vertices. -/
  vs : InfVSet Vertex
  /-- A vertex. -/
  v : Vertex
  /-- A color. -/
  c : Color

variable {Vertex Color : Type*} [Finite Color] (color : Finset Vertex → Color)

open scoped Classical in
/-- A "good selection" `S` selects an infinite subset `S.vs` of an infinite vertex set `ivs` and
a distinguished vertex `S.v` in `ivs` but not in `S.vs`, and makes sure that the edges between
`S.v` and all vertices in `S.vs` have the same color `S.c`. -/
private def GoodSelection (ivs : InfVSet Vertex) (S : Selection Vertex Color) : Prop :=
  S.vs.set ⊆ ivs.set ∧ S.v ∈ ivs.set \ S.vs.set ∧ ∀ u ∈ S.vs.set, color {S.v, u} = S.c

/-- Given any infinite vertex set, a good selection from it always exists. -/
private lemma goodSelection_exists (ivs : InfVSet Vertex) :
    ∃ S : Selection Vertex Color, GoodSelection color ivs S := by
  classical
  obtain ⟨v, h_v⟩ := Set.Infinite.nonempty ivs.inf
  let f u := color {v, u}
  obtain ⟨c, vs, h_inf, h_vs, h_col⟩ := infinite_pigeonhole_principle f <|
    Set.Infinite.diff ivs.inf (finite_singleton v)
  simp only [subset_diff] at h_vs
  let ivs' := InfVSet.mk vs h_inf
  use {vs := ivs', v := v, c := c}
  grind [GoodSelection]

variable [Infinite Vertex]

/-- Starting from the infinite set of all vertices, inductively make an infinite sequence
of good selections. -/
private noncomputable def goodSelection_seq : ℕ → Selection Vertex Color
  | 0 => Classical.choose (goodSelection_exists color (InfVSet.mk univ infinite_univ))
  | n + 1 => Classical.choose (goodSelection_exists color (goodSelection_seq n).vs)

/-- At every step, the `goodSelection_seq` makes a good selection and there are always
infinitely many vertices remaining to be selected. -/
private lemma goodSelection_seq_prop (n : ℕ) :
    ∃ ivs : InfVSet Vertex, GoodSelection color ivs (goodSelection_seq color n) ∧
      (ivs.set = ⋂ m < n, (goodSelection_seq color m).vs.set) := by
  induction n
  case zero =>
    use (InfVSet.mk univ infinite_univ)
    simp
    grind [goodSelection_seq]
  case succ n h_ind =>
    obtain ⟨_, _, h_eq⟩ := h_ind
    use (goodSelection_seq color n).vs
    constructor
    · grind [goodSelection_seq]
    · have h1 (m : ℕ) : m < n + 1 ↔ m < n ∨ m = n := by grind
      simp [h1, iInter_or, iInter_inter_distrib, ← h_eq]
      grind [GoodSelection]

open scoped Classical in
/-- There exist an infinite sequence `vs` of vertex sets, an infinite sequence `v` of vertices,
and an infinite sequence `c` of colors such that each `vs n` is a subset of the intersection of
all previous `vs m`s, each `v n` belongs to the intersection of all previous `vs m`s but not
to `vs n`, and the edges between `v n` and all vertices in `vs n` has the same color `c n`. -/
private lemma good_selections_exist :
    ∃ vs : ℕ → Set Vertex, ∃ v : ℕ → Vertex, ∃ c : ℕ → Color,
    ∀ n, vs n ⊆ (⋂ m < n, vs m) ∧ v n ∈ (⋂ m < n, vs m) \ (vs n) ∧
      ∀ u ∈ vs n, color {v n, u} = c n := by
  use (fun k ↦ (goodSelection_seq color k).vs.set)
  use (fun k ↦ (goodSelection_seq color k).v)
  use (fun k ↦ (goodSelection_seq color k).c)
  intro n
  obtain ⟨ivs, h_ivs, h_eq⟩ := goodSelection_seq_prop color n
  rw [← h_eq]
  exact h_ivs

/-- If the edges of an infinite complete graph is assigned a finite number of colors,
then there must exist a color `c` and an infinite set `s` of vertices such that the edge
beteen any two vertices of `s` is assigned the same color `c`. -/
theorem infinite_graph_ramsey :
    ∃ c : Color, ∃ s : Set Vertex, s.Infinite ∧
      ∀ e : Finset Vertex, e.card = 2 → ↑e ⊆ s → color e = c := by
  classical
  obtain ⟨vs, v, c, h_sel⟩ := good_selections_exist color
  simp only [forall_and] at h_sel
  obtain ⟨h_vs, h_v, h_c⟩ := h_sel
  have : ∀ m n, m < n → v n ∈ vs m := by
    intro m n h_mn
    suffices h1 : (⋂ m < n, vs m) ⊆ vs m by grind
    exact biInter_subset_of_mem h_mn
  obtain ⟨c', s', h_s'_inf, h_s'_col⟩ :
      ∃ c' : Color, ∃ s' : Set ℕ, s'.Infinite ∧ ∀ n ∈ s', c n = c' := by
    obtain ⟨c', s', h_s'_inf, _, h_s'col⟩ := infinite_pigeonhole_principle c infinite_univ
    use c', s'
  use c', (v '' s')
  have h_v_inj : Injective v := by
    intro _ _
    grind
  split_ands
  · exact Infinite.image (injOn_of_injective h_v_inj (s := s')) h_s'_inf
  · simp only [Finset.card_eq_two]
    grind [Finset.pair_comm, Finset.coe_insert, Finset.coe_singleton]

end Cslib
