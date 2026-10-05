/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S0N1.Ra01
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S0N1.Ra02
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S0N1.Ra03
public import Cslib.Foundations.RelationAlgebra.Signature

/-!
# Classification of the ⟨1, 0, 1⟩ catalogue row

This row contains 3 isomorphism classes, of which 3 are representable and
0 are nonrepresentable. See
[Jipsen’s catalogue](https://www1.chapman.edu/~jipsen/gap/ramaddux.html).
`Model` uses zero-based indices: index `n` denotes source entry `n + 1`.
The unique-index classification expresses both exhaustiveness and absence of duplicates.
The two possible diversity cycle orbits distinguish the three algebras.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S0N1

/-- The certified cycle tables, in the source's order. -/
def table : Fin 3 → IntegralCycleTable 0 1
  | ⟨0, _⟩ => Ra01.table
  | ⟨1, _⟩ => Ra02.table
  | ⟨2, _⟩ => Ra03.table

/-- The explicitly listed algebras, indexed in the source's order. -/
abbrev Model (idx : Fin 3) : Type := Complex (table idx)

private abbrev forward : Atom 0 1 := some (.inr (0, false))

private abbrev backward : Atom 0 1 := some (.inr (0, true))

private theorem closure_none (cycles : Finset (Cycle 0 1)) (x y : Atom 0 1) :
    cycleClosure cycles x y none ↔ y = x.converse := by
  cases x <;> cases y <;> simp [cycleClosure, cycleOrbit]

private theorem closure_converse_iff (cycles : Finset (Cycle 0 1)) (x y z : Atom 0 1) :
    cycleClosure cycles y.converse x.converse z.converse ↔ cycleClosure cycles x y z := by
  constructor
  · intro h
    simpa only [Atom.converse_converse] using cycleClosure_converse h
  · exact cycleClosure_converse

private theorem closure_peirce_iff (cycles : Finset (Cycle 0 1)) (x y z : Atom 0 1) :
    cycleClosure cycles x.converse z y ↔ cycleClosure cycles x y z := by
  constructor
  · intro h
    simpa only [Atom.converse_converse] using cycleClosure_peirce h
  · exact cycleClosure_peirce

private theorem closure_determined_by_two_cycles (c d : Finset (Cycle 0 1))
    (hp : cycleClosure c forward forward forward ↔ cycleClosure d forward forward forward)
    (hq : cycleClosure c forward forward backward ↔ cycleClosure d forward forward backward)
    (x y z : Atom 0 1) : cycleClosure c x y z ↔ cycleClosure d x y z := by
  have hb (s : Finset (Cycle 0 1)) :
      cycleClosure s backward backward backward ↔ cycleClosure s forward forward forward :=
    closure_converse_iff s forward forward forward
  have hba (s : Finset (Cycle 0 1)) :
      cycleClosure s backward forward forward ↔ cycleClosure s forward forward forward :=
    closure_peirce_iff s forward forward forward
  have hab (s : Finset (Cycle 0 1)) :
      cycleClosure s forward backward backward ↔ cycleClosure s forward forward forward :=
    (closure_peirce_iff s backward backward backward).trans (hb s)
  have haba (s : Finset (Cycle 0 1)) :
      cycleClosure s forward backward forward ↔ cycleClosure s forward forward forward :=
    (closure_converse_iff s forward backward backward).trans (hab s)
  have hbab (s : Finset (Cycle 0 1)) :
      cycleClosure s backward forward backward ↔ cycleClosure s forward forward forward :=
    (closure_converse_iff s backward forward forward).trans (hba s)
  have hbba (s : Finset (Cycle 0 1)) :
      cycleClosure s backward backward forward ↔ cycleClosure s forward forward backward :=
    closure_converse_iff s forward forward backward
  rcases atom_zero_one_cases x with rfl | rfl | rfl <;>
    rcases atom_zero_one_cases y with rfl | rfl | rfl <;>
    rcases atom_zero_one_cases z with rfl | rfl | rfl <;>
    simp only [cycleClosure_none_left, cycleClosure_none_right, closure_none,
      hb, hba, hab, haba, hbab, hbba, hp, hq]

private theorem table_has_diversity_cycle (T : IntegralCycleTable 0 1) :
    cycleClosure T.cycles forward forward forward ∨
      cycleClosure T.cycles forward forward backward := by
  by_contra h
  obtain ⟨hp, hq⟩ := not_or.mp h
  have hr : ∃ t, cycleClosure T.cycles forward backward t ∧
      cycleClosure T.cycles forward t forward := by
    refine ⟨none, ?_, by simp⟩
    simp [closure_none, forward, backward, Atom.converse, DiversityAtom.converse]
  obtain ⟨t, ht, _⟩ := (T.associative forward forward backward forward).mpr hr
  rcases atom_zero_one_cases t with rfl | rfl | rfl
  · simp [closure_none, forward, Atom.converse, DiversityAtom.converse] at ht
  · exact hp ht
  · exact hq ht

private theorem table_classification (T : IntegralCycleTable 0 1) :
    ∃ idx : Fin 3, ∀ x y z, cycleClosure (table idx).cycles x y z ↔
      cycleClosure T.cycles x y z := by
  classical
  by_cases hp : cycleClosure T.cycles forward forward forward
  · by_cases hq : cycleClosure T.cycles forward forward backward
    · exact ⟨2, closure_determined_by_two_cycles _ _
        (iff_of_true (by decide +kernel) hp) (iff_of_true (by decide +kernel) hq)⟩
    · exact ⟨1, closure_determined_by_two_cycles _ _
        (iff_of_true (by decide +kernel) hp) (iff_of_false (by decide +kernel) hq)⟩
  · have hq := (table_has_diversity_cycle T).resolve_left hp
    exact ⟨0, closure_determined_by_two_cycles _ _
      (iff_of_false (by decide +kernel) hp) (iff_of_true (by decide +kernel) hq)⟩

private def HasDiversityCycle (reverse : Bool) (A : Type*) [RelationAlgebra A] : Prop :=
  ∃ a : A, IsAtom a ∧ a ≤ (1 : A)ᶜ ∧ (if reverse then star a else a) ≤ a * a

private theorem map_diversity_cycle {A B : Type*} [RelationAlgebra A] [RelationAlgebra B]
    (e : RelationAlgebraEquiv A B) (reverse : Bool) :
    HasDiversityCycle reverse A → HasDiversityCycle reverse B := by
  rintro ⟨a, ha, had, hac⟩
  let f : A ≃o B := e.toOrderIso
  refine ⟨e a, (f.isAtom_iff a).mpr ha, ?_, ?_⟩
  · have hd : e a ≤ e (1 : A)ᶜ := f.monotone had
    simpa only [map_compl', map_one] using hd
  · have hc : e (if reverse then star a else a) ≤ e (a * a) := f.monotone hac
    cases reverse <;>
      simpa only [Bool.false_eq_true, ite_false, ite_true, map_star, map_mul] using hc

private theorem diversity_cycle_iff {A B : Type*} [RelationAlgebra A] [RelationAlgebra B]
    (e : RelationAlgebraEquiv A B) (reverse : Bool) :
    HasDiversityCycle reverse A ↔ HasDiversityCycle reverse B :=
  ⟨map_diversity_cycle e reverse, map_diversity_cycle e.symm reverse⟩

private instance (reverse : Bool) (idx : Fin 3) :
    Decidable (HasDiversityCycle reverse (Model idx)) := by
  unfold HasDiversityCycle IsAtom
  simp only [lt_iff_le_not_ge]
  infer_instance

private theorem distinct_cycle_profiles : ∀ i j : Fin 3, i ≠ j →
    ¬ ((HasDiversityCycle false (Model i) ↔ HasDiversityCycle false (Model j)) ∧
      (HasDiversityCycle true (Model i) ↔ HasDiversityCycle true (Model j))) := by
  decide +kernel

private theorem iso_index_eq (i j : Fin 3) (e : RelationAlgebraEquiv (Model i) (Model j)) :
    i = j := by
  by_contra h
  exact distinct_cycle_profiles i j h ⟨diversity_cycle_iff e false, diversity_cycle_iff e true⟩

private theorem model_representable (idx : Fin 3) : Representable (Model idx) := by
  rcases (show idx = 0 ∨ idx = 1 ∨ idx = 2 by omega) with rfl | rfl | rfl
  · exact Ra01.representable
  · exact Ra02.representable
  · exact Ra03.representable

/-- Every algebra of this signature is isomorphic to exactly one listed model. -/
theorem classification (A : Type*) [RelationAlgebra A] (h : HasSignature A 1 0 1) :
    ∃! idx : Fin 3, Nonempty (RelationAlgebraEquiv A (Model idx)) := by
  classical
  let : Finite A := h.1
  let e := AtomLabelling.ofHasSignature h
  obtain ⟨idx, hi⟩ := table_classification e.table
  let iso : RelationAlgebraEquiv A (Model idx) :=
    e.relationAlgebraEquivTo (table idx)
      (fun x y z => (hi x y z).trans (e.cycleClosure_iff x y z))
  refine ⟨idx, ⟨iso⟩, ?_⟩
  rintro j ⟨f⟩
  exact (iso_index_eq idx j (iso.symm.trans f)).symm

/-- The number of representable isomorphism classes in this row. -/
theorem count_representable :
    Nat.card {idx : Fin 3 // Representable (Model idx)} = 3 := by
  have he : {idx : Fin 3 // Representable (Model idx)} ≃ Fin 3 :=
    { toFun := Subtype.val
      invFun := fun idx => ⟨idx, model_representable idx⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simpa using Nat.card_congr he

/-- The number of nonrepresentable isomorphism classes in this row. -/
theorem count_nonrepresentable :
    Nat.card {idx : Fin 3 // ¬ Representable (Model idx)} = 0 := by
  have : IsEmpty {idx : Fin 3 // ¬ Representable (Model idx)} :=
    ⟨fun idx => idx.property (model_representable idx.val)⟩
  simp

end Cslib.RelationAlgebra.Catalogue.I1S0N1
