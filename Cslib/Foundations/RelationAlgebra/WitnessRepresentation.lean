/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.FiniteRepresentation

/-!
# Representations by successive composition witnesses

A finite policy for extending consistent atomic networks yields a representation on a
countable base. At each stage all composition requests from the preceding finite network
are supplied with witnesses.
-/

@[expose] public section

namespace Cslib.RelationAlgebra

variable {j k : ℕ} {T : IntegralCycleTable j k}

/-- A finite choice of labels for adding a missing composition witness. -/
structure WitnessPolicy (T : IntegralCycleTable j k) where
  /-- The edge from an old vertex to the new witness, determined by its relative type. -/
  label : Atom j k → Atom j k → Atom j k → Atom j k → Atom j k → Atom j k
  /-- Fresh witnesses receive diversity labels on their edges to old vertices. -/
  diversity {a b c d e} (ha : a ≠ none) (hb : b ≠ none)
      (hc : cycleClosure T.cycles a b c)
      (hp : cycleClosure T.cycles d (Atom.converse e) c)
      (hne : (d, e) ≠ (a, Atom.converse b)) : label a b c d e ≠ none
  /-- The first endpoint has the requested first label. -/
  left {a b c} (ha : a ≠ none) (hb : b ≠ none)
      (hc : cycleClosure T.cycles a b c) : label a b c none (Atom.converse c) = a
  /-- The second endpoint has the converse of the requested second label. -/
  right {a b c} (ha : a ≠ none) (hb : b ≠ none)
      (hc : cycleClosure T.cycles a b c) : label a b c c none = Atom.converse b
  /-- Every old edge forms a permitted triangle with its two new edges. -/
  triangle {a b c d e d' e' h} (ha : a ≠ none) (hb : b ≠ none)
      (hc : cycleClosure T.cycles a b c)
      (hp : cycleClosure T.cycles d (Atom.converse e) c)
      (hp' : cycleClosure T.cycles d' (Atom.converse e') c)
      (hne : (d, e) ≠ (a, Atom.converse b))
      (hne' : (d', e') ≠ (a, Atom.converse b))
      (hd : cycleClosure T.cycles d h d')
      (he : cycleClosure T.cycles e h e') :
      cycleClosure T.cycles h (label a b c d' e') (label a b c d e)

/-- A finite consistent complete atomic network, with vertices below `size`. -/
structure FiniteAtomNetwork (T : IntegralCycleTable j k) where
  /-- The number of vertices. -/
  size : ℕ
  /-- Every network has a vertex. -/
  positive : 0 < size
  /-- Labels outside the vertex set are immaterial. -/
  label : ℕ → ℕ → Atom j k
  /-- Only diagonal edges carry the identity label. -/
  identity {x y} (hx : x < size) (hy : y < size) : label x y = none ↔ x = y
  /-- Reversed edges have converse labels. -/
  converse {x y} (hx : x < size) (hy : y < size) :
    label y x = Atom.converse (label x y)
  /-- Every triangle respects the atomic multiplication table. -/
  triangle {x y z} (hx : x < size) (hy : y < size) (hz : z < size) :
    cycleClosure T.cycles (label x y) (label y z) (label x z)

namespace FiniteAtomNetwork

/-- An extension retains the vertices and all labels of its original network. -/
def Extends (N M : FiniteAtomNetwork T) : Prop :=
  N.size ≤ M.size ∧ ∀ x y, x < N.size → y < N.size → M.label x y = N.label x y

theorem Extends.refl (N : FiniteAtomNetwork T) : N.Extends N := ⟨le_rfl, by simp⟩

theorem Extends.trans {N M P : FiniteAtomNetwork T} (h : N.Extends M)
    (h' : M.Extends P) : N.Extends P := by
  refine ⟨h.1.trans h'.1, fun x y hx hy => ?_⟩
  rw [h'.2 x y (hx.trans_le h.1) (hy.trans_le h.1), h.2 x y hx hy]

/-- A network already contains a specified composition witness. -/
def Witness (N : FiniteAtomNetwork T) (x y : ℕ) (a b : Atom j k) : Prop :=
  ∃ z < N.size, N.label x z = a ∧ N.label z y = b

theorem Witness.mono {N M : FiniteAtomNetwork T} (h : N.Extends M)
    {x y a b} (hx : x < N.size) (hy : y < N.size) (hw : N.Witness x y a b) :
    M.Witness x y a b := by
  obtain ⟨z, hz, ha, hb⟩ := hw
  exact ⟨z, hz.trans_le h.1, (h.2 x z hx hz).trans ha, (h.2 z y hz hy).trans hb⟩

/-- The initial network consists of one vertex. -/
def singleton (T : IntegralCycleTable j k) : FiniteAtomNetwork T where
  size := 1
  positive := by decide
  label _ _ := none
  identity hx hy := by simp only [true_iff]; omega
  converse _ _ := rfl
  triangle _ _ _ := Or.inl ⟨rfl, rfl⟩

private theorem cycle_rotate {x y z : Atom j k}
    (h : cycleClosure T.cycles x y z) :
    cycleClosure T.cycles z (Atom.converse y) x := by
  simpa only [Atom.converse_converse] using
    cycleClosure_converse (cycleClosure_peirce (cycleClosure_converse h))

/-- Extend the labelling by an edge from each old vertex to a new vertex. -/
def addLabel (N : FiniteAtomNetwork T) (f : ℕ → Atom j k) (x y : ℕ) : Atom j k :=
  if x < N.size then if y < N.size then N.label x y else f x
  else if y < N.size then Atom.converse (f y) else none

/-- Add a fresh vertex when its incident labels satisfy all triangle constraints. -/
def add (N : FiniteAtomNetwork T) (f : ℕ → Atom j k)
    (hf : ∀ x < N.size, f x ≠ none)
    (ht : ∀ x y, x < N.size → y < N.size →
      cycleClosure T.cycles (N.label x y) (f y) (f x)) : FiniteAtomNetwork T where
  size := N.size + 1
  positive := Nat.zero_lt_succ _
  label := N.addLabel f
  identity {x y} hx hy := by
    by_cases hx' : x < N.size <;> by_cases hy' : y < N.size
    · simpa only [addLabel, ite_eq_left hx', ite_eq_left hy'] using N.identity hx' hy'
    · simp only [addLabel, ite_eq_left hx', ite_eq_right hy']
      exact iff_of_false (hf x hx') (by omega)
    · simp only [addLabel, ite_eq_right hx', ite_eq_left hy']
      refine iff_of_false (fun h => hf y hy' ?_) (by omega)
      simpa only [Atom.converse_converse, Atom.converse_none] using
        congrArg Atom.converse h
    · simp only [addLabel, ite_eq_right hx', ite_eq_right hy', true_iff]
      omega
  converse {x y} hx hy := by
    by_cases hx' : x < N.size <;> by_cases hy' : y < N.size
    · simpa only [addLabel, ite_eq_left hx', ite_eq_left hy'] using N.converse hx' hy'
    all_goals simp [addLabel, hx', hy']
  triangle {x y z} hx hy hz := by
    by_cases hx' : x < N.size <;> by_cases hy' : y < N.size <;>
      by_cases hz' : z < N.size
    · simpa only [addLabel, ite_eq_left hx', ite_eq_left hy', ite_eq_left hz'] using
        N.triangle hx' hy' hz'
    · simpa only [addLabel, ite_eq_left hx', ite_eq_left hy', ite_eq_right hz'] using ht x y hx' hy'
    · simpa only [addLabel, ite_eq_left hx', ite_eq_right hy', ite_eq_left hz'] using
        cycle_rotate (ht x z hx' hz')
    · simp [addLabel, hx', hy', hz']
    · simpa only [addLabel, ite_eq_right hx', ite_eq_left hy', ite_eq_left hz',
        ← N.converse hz' hy'] using cycleClosure_converse (ht z y hz' hy')
    · simp only [addLabel, ite_eq_right hx', ite_eq_left hy', ite_eq_right hz']
      exact Or.inr (Or.inr (Or.inl ⟨rfl, (Atom.converse_converse _).symm⟩))
    · simp [addLabel, hx', hy', hz']
    · simp [addLabel, hx', hy', hz']

theorem extends_add (N : FiniteAtomNetwork T) (f : ℕ → Atom j k) hf ht :
    N.Extends (N.add f hf ht) := by
  exact ⟨Nat.le_succ _, fun x y hx hy => by simp [add, addLabel, hx, hy]⟩

/-- Every permitted composition request has a witness in a finite extension. -/
theorem exists_witness_extension (P : WitnessPolicy T) (N : FiniteAtomNetwork T)
    {x y : ℕ} (hx : x < N.size) (hy : y < N.size) {a b : Atom j k}
    (hc : cycleClosure T.cycles a b (N.label x y)) :
    ∃ M, N.Extends M ∧ M.Witness x y a b := by
  classical
  by_cases hw : N.Witness x y a b
  · exact ⟨N, Extends.refl N, hw⟩
  have ha : a ≠ none := by
    intro h
    subst a
    have hb := (cycleClosure_none_left _ _ _).mp hc
    exact hw ⟨x, hx, (N.identity hx hx).mpr rfl, hb.symm⟩
  have hb : b ≠ none := by
    intro h
    subst b
    have ha := (cycleClosure_none_right _ _ _).mp hc
    exact hw ⟨y, hy, ha.symm, (N.identity hy hy).mpr rfl⟩
  have hp (v) (hv : v < N.size) :
      cycleClosure T.cycles (N.label x v) (Atom.converse (N.label y v)) (N.label x y) := by
    rw [← N.converse hy hv]
    exact N.triangle hx hv hy
  have hne (v) (hv : v < N.size) :
      (N.label x v, N.label y v) ≠ (a, Atom.converse b) := by
    intro h
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    dsimp only at h₁ h₂
    apply hw
    refine ⟨v, hv, h₁, ?_⟩
    rw [N.converse hy hv, h₂, Atom.converse_converse]
  let f v := P.label a b (N.label x y) (N.label x v) (N.label y v)
  have hf v hv : f v ≠ none := P.diversity ha hb hc (hp v hv) (hne v hv)
  have ht v w hv hw : cycleClosure T.cycles (N.label v w) (f w) (f v) :=
    P.triangle ha hb hc (hp v hv) (hp w hw) (hne v hv) (hne w hw)
      (N.triangle hx hv hw) (N.triangle hy hv hw)
  refine ⟨N.add f hf ht, N.extends_add f hf ht, N.size, Nat.lt_succ_self _, ?_, ?_⟩
  · simp only [add, addLabel, hx, ite_true, lt_self_iff_false, ite_false]
    dsimp only [f]
    rw [(N.identity hx hx).mpr rfl, N.converse hx hy]
    exact P.left ha hb hc
  · simp only [add, addLabel, hy, ite_true, lt_self_iff_false, ite_false]
    dsimp only [f]
    rw [(N.identity hy hy).mpr rfl, P.right ha hb hc, Atom.converse_converse]

/-- A finite extension supplies every composition witness requested by the original network. -/
theorem exists_full_extension (P : WitnessPolicy T) (N : FiniteAtomNetwork T) :
    ∃ M, N.Extends M ∧ ∀ x y, x < N.size → y < N.size → ∀ a b,
      cycleClosure T.cycles a b (N.label x y) → M.Witness x y a b := by
  classical
  let Request := Fin N.size × Fin N.size × Atom j k × Atom j k
  have go (s : Finset Request) : ∃ M, N.Extends M ∧ ∀ q ∈ s,
      cycleClosure T.cycles q.2.2.1 q.2.2.2 (N.label q.1 q.2.1) →
        M.Witness q.1 q.2.1 q.2.2.1 q.2.2.2 := by
    induction s using Finset.induction_on with
    | empty => exact ⟨N, Extends.refl N, by simp⟩
    | @insert q s hq ih =>
      obtain ⟨M, hNM, hM⟩ := ih
      by_cases hc : cycleClosure T.cycles q.2.2.1 q.2.2.2 (N.label q.1 q.2.1)
      · have hc' : cycleClosure T.cycles q.2.2.1 q.2.2.2 (M.label q.1 q.2.1) := by
          rw [hNM.2 _ _ q.1.isLt q.2.1.isLt]
          exact hc
        obtain ⟨M', hMM', hw⟩ := exists_witness_extension P M
          (q.1.isLt.trans_le hNM.1) (q.2.1.isLt.trans_le hNM.1) hc'
        refine ⟨M', hNM.trans hMM', fun r hr hr' => ?_⟩
        rcases Finset.mem_insert.mp hr with rfl | hr
        · exact hw
        · exact (hM r hr hr').mono hMM'
            (r.1.isLt.trans_le hNM.1) (r.2.1.isLt.trans_le hNM.1)
      · refine ⟨M, hNM, fun r hr hr' => ?_⟩
        rcases Finset.mem_insert.mp hr with rfl | hr
        · exact (hc hr').elim
        · exact hM r hr hr'
  obtain ⟨M, hNM, hM⟩ := go Finset.univ
  exact ⟨M, hNM, fun x y hx hy a b hc => hM (⟨x, hx⟩, ⟨y, hy⟩, a, b)
    (Finset.mem_univ _) hc⟩

end FiniteAtomNetwork

namespace WitnessPolicy

variable (P : WitnessPolicy T)

/-- Choose a finite extension supplying all current requests. -/
noncomputable def fullExtension (N : FiniteAtomNetwork T) : FiniteAtomNetwork T :=
  Classical.choose (N.exists_full_extension P)

theorem extends_fullExtension (N : FiniteAtomNetwork T) : N.Extends (P.fullExtension N) :=
  (Classical.choose_spec (N.exists_full_extension P)).1

theorem fullExtension_witness (N : FiniteAtomNetwork T) {x y}
    (hx : x < N.size) (hy : y < N.size) {a b}
    (hc : cycleClosure T.cycles a b (N.label x y)) :
    (P.fullExtension N).Witness x y a b :=
  (Classical.choose_spec (N.exists_full_extension P)).2 x y hx hy a b hc

/-- The successive finite stages of the representation. -/
noncomputable def stage (P : WitnessPolicy T) : ℕ → FiniteAtomNetwork T
  | 0 => FiniteAtomNetwork.singleton T
  | n + 1 => P.fullExtension (stage P n)

theorem stage_extends {m n : ℕ} (h : m ≤ n) : (P.stage m).Extends (P.stage n) := by
  induction n, h using Nat.le_induction with
  | base => exact FiniteAtomNetwork.Extends.refl _
  | succ n hn ih => exact ih.trans (P.extends_fullExtension (P.stage n))

/-- The countable union of the finite vertex sets. -/
def Base := {x : ℕ // ∃ n, x < (P.stage n).size}

/-- A stage at which a vertex first appears. -/
noncomputable def level (x : P.Base) : ℕ := Nat.find x.property

theorem lt_stage_level (x : P.Base) : x.val < (P.stage (P.level x)).size :=
  Nat.find_spec x.property

theorem lt_stage {x : P.Base} {n : ℕ} (h : P.level x ≤ n) :
    x.val < (P.stage n).size :=
  (P.lt_stage_level x).trans_le (P.stage_extends h).1

/-- The label on the union is the stable label once both endpoints have appeared. -/
noncomputable def unionLabel (x y : P.Base) : Atom j k :=
  (P.stage (max (P.level x) (P.level y))).label x.val y.val

theorem unionLabel_eq {x y : P.Base} {n : ℕ}
    (hx : x.val < (P.stage n).size) (hy : y.val < (P.stage n).size) :
    P.unionLabel x y = (P.stage n).label x.val y.val := by
  let m := max (P.level x) (P.level y)
  have hx' : x.val < (P.stage m).size := P.lt_stage (le_max_left _ _)
  have hy' : y.val < (P.stage m).size := P.lt_stage (le_max_right _ _)
  exact ((P.stage_extends (le_max_left m n)).2 _ _ hx' hy').symm.trans
    ((P.stage_extends (le_max_right m n)).2 _ _ hx hy)

theorem unionLabel_identity (x y : P.Base) : P.unionLabel x y = none ↔ x = y := by
  rw [P.unionLabel_eq (P.lt_stage (le_max_left (P.level x) (P.level y)))
    (P.lt_stage (le_max_right (P.level x) (P.level y)))]
  rw [(P.stage _).identity (P.lt_stage (le_max_left _ _))
    (P.lt_stage (le_max_right _ _))]
  exact Subtype.val_injective.eq_iff

theorem unionLabel_converse (x y : P.Base) :
    P.unionLabel y x = Atom.converse (P.unionLabel x y) := by
  have hx := P.lt_stage (le_max_left (P.level x) (P.level y))
  have hy := P.lt_stage (le_max_right (P.level x) (P.level y))
  rw [P.unionLabel_eq hx hy, P.unionLabel_eq hy hx]
  exact (P.stage _).converse hx hy

theorem unionLabel_triangle (x y z : P.Base) :
    cycleClosure T.cycles (P.unionLabel x y) (P.unionLabel y z) (P.unionLabel x z) := by
  let n := max (max (P.level x) (P.level y)) (P.level z)
  have hx : x.val < (P.stage n).size :=
    P.lt_stage ((le_max_left _ _).trans (le_max_left _ _))
  have hy : y.val < (P.stage n).size :=
    P.lt_stage ((le_max_right _ _).trans (le_max_left _ _))
  have hz : z.val < (P.stage n).size := P.lt_stage (le_max_right _ _)
  rw [P.unionLabel_eq hx hy, P.unionLabel_eq hy hz, P.unionLabel_eq hx hz]
  exact (P.stage n).triangle hx hy hz

theorem unionLabel_composition (a b : Atom j k) (x y : P.Base) :
    cycleClosure T.cycles a b (P.unionLabel x y) ↔
      ∃ z, P.unionLabel x z = a ∧ P.unionLabel z y = b := by
  constructor
  · intro hc
    let n := max (P.level x) (P.level y)
    have hx : x.val < (P.stage n).size := P.lt_stage (le_max_left _ _)
    have hy : y.val < (P.stage n).size := P.lt_stage (le_max_right _ _)
    rw [P.unionLabel_eq hx hy] at hc
    obtain ⟨z, hz, ha, hb⟩ := P.fullExtension_witness (P.stage n) hx hy hc
    have hz' : z < (P.stage (n + 1)).size := hz
    let z' : P.Base := ⟨z, n + 1, hz'⟩
    have hx' := hx.trans_le (P.stage_extends (Nat.le_succ n)).1
    have hy' := hy.trans_le (P.stage_extends (Nat.le_succ n)).1
    refine ⟨z', ?_, ?_⟩
    · exact (P.unionLabel_eq hx' hz').trans ha
    · exact (P.unionLabel_eq hz' hy').trans hb
  · rintro ⟨z, ha, hb⟩
    simpa only [ha, hb] using P.unionLabel_triangle x z y

/-- The representation obtained by repeatedly adding all missing witnesses. -/
noncomputable def toAtomRepresentation : AtomRepresentation T P.Base where
  label := P.unionLabel
  surjective a := by
    let x : P.Base := ⟨0, 0, (P.stage 0).positive⟩
    have hc : cycleClosure T.cycles a (Atom.converse a) (P.unionLabel x x) := by
      rw [(P.unionLabel_identity x x).mpr rfl]
      exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    obtain ⟨z, hz, _⟩ := (P.unionLabel_composition a (Atom.converse a) x x).mp hc
    exact ⟨(x, z), hz⟩
  identity := P.unionLabel_identity
  converse := P.unionLabel_converse
  composition := P.unionLabel_composition

/-- A finite witness policy proves representability of its integral cycle table. -/
theorem representable (P : WitnessPolicy T) : Representable (Complex T) :=
  AtomRepresentation.representable P.toAtomRepresentation

end WitnessPolicy

end Cslib.RelationAlgebra
