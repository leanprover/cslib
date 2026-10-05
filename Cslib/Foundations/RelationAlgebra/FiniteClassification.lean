/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Signature

/-!
# Finite enumeration of atom cycle tables

A finite list meeting every Peircean orbit reduces classification to one Boolean choice per orbit.
The reduction preserves the entire composition table, including its associativity certificate.
-/

@[expose] public section

namespace Cslib.RelationAlgebra

variable {j k n : ℕ}

/-- A cycle and any of its Peircean transforms have the same closure truth value. -/
theorem cycleClosure_of_mem_orbit {cycles : Finset (Cycle j k)} {c : Cycle j k}
    (hc : cycleClosure cycles (some c.1) (some c.2.1) (some c.2.2))
    {x y z : Atom j k} (h : (x, y, z) ∈ cycleOrbit c) : cycleClosure cycles x y z := by
  have h1 := cycleClosure_peirce hc
  have h3 := cycleClosure_converse hc
  have h4 := cycleClosure_peirce h3
  have h2 := cycleClosure_converse h4
  have h5 := cycleClosure_converse h1
  simp only [cycleOrbit, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact hc
  · exact h1
  · simpa only [Atom.converse_converse] using h2
  · exact h3
  · simpa only [Atom.converse_converse] using h4
  · simpa only [Atom.converse_converse] using h5

/-- Peircean orbit membership is symmetric. -/
theorem cycleOrbit_symm {c d : Cycle j k}
    (h : (some d.1, some d.2.1, some d.2.2) ∈ cycleOrbit c) :
    (some c.1, some c.2.1, some c.2.2) ∈ cycleOrbit d := by
  rcases c with ⟨x, y, z⟩
  rcases d with ⟨a, b, c⟩
  simp only [cycleOrbit, Atom.converse_some, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq, Option.some.injEq] at h
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    simp [cycleOrbit]

/-- Choose the listed diversity cycles according to a finite vector of Boolean choices. -/
def selectedCycles (reps : Fin n → Cycle j k) (bits : Fin n → Bool) : Finset (Cycle j k) :=
  (Finset.univ.filter fun i => bits i).image reps

/-- Every cycle table is equivalent to choices among a list meeting all diversity-cycle orbits. -/
theorem exists_selectedCycles (reps : Fin n → Cycle j k)
    (cover : ∀ c : Cycle j k, ∃ i, (some c.1, some c.2.1, some c.2.2) ∈ cycleOrbit (reps i))
    (cycles : Finset (Cycle j k)) :
    ∃ bits : Fin n → Bool, ∀ x y z,
      cycleClosure (selectedCycles reps bits) x y z ↔ cycleClosure cycles x y z := by
  let bits := fun i => decide (cycleClosure cycles
    (some (reps i).1) (some (reps i).2.1) (some (reps i).2.2))
  refine ⟨bits, fun x y z => ?_⟩
  constructor
  · rintro (h | h | h | ⟨c, hc, h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hc
      have hb : bits i = true := (Finset.mem_filter.mp hi).2
      exact cycleClosure_of_mem_orbit (of_decide_eq_true hb) h
  · rintro (h | h | h | ⟨c, hc, h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · obtain ⟨i, hi⟩ := cover c
      have hrep : cycleClosure cycles (some (reps i).1)
          (some (reps i).2.1) (some (reps i).2.2) :=
        cycleClosure_of_mem_orbit
          (Or.inr (Or.inr (Or.inr ⟨c, hc, by simp [cycleOrbit]⟩))) (cycleOrbit_symm hi)
      have hm : reps i ∈ selectedCycles reps bits := by
        apply Finset.mem_image.mpr
        exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, decide_eq_true hrep⟩, rfl⟩
      have hbase : cycleClosure (selectedCycles reps bits)
          (some c.1) (some c.2.1) (some c.2.2) :=
        Or.inr (Or.inr (Or.inr ⟨reps i, hm, hi⟩))
      exact cycleClosure_of_mem_orbit hbase h

/-- Equivalent closures share the associativity condition. -/
theorem atomCompositionAssociative_congr {c d : Finset (Cycle j k)}
    (h : ∀ x y z, cycleClosure c x y z ↔ cycleClosure d x y z) :
    AtomCompositionAssociative c ↔ AtomCompositionAssociative d := by
  unfold AtomCompositionAssociative
  simp only [h]

/-- An injective renaming preserving identity, converse, and the full atom composition table. -/
def AtomRelabelling (c d : Finset (Cycle j k)) (f : Atom j k → Atom j k) : Prop :=
  Function.Injective f ∧ f none = none ∧
    (∀ x, f x.converse = (f x).converse) ∧
      ∀ x y z, cycleClosure c x y z ↔ cycleClosure d (f x) (f y) (f z)

instance (c d : Finset (Cycle j k)) (f : Atom j k → Atom j k) :
    Decidable (AtomRelabelling c d f) := by
  unfold AtomRelabelling Function.Injective
  infer_instance

/-- A converse-preserving map transports every Peircean transform of a cycle. -/
theorem cycleClosure_map_of_mem_orbit {cycles : Finset (Cycle j k)}
    {f : Atom j k → Atom j k} (hf : ∀ x, f x.converse = (f x).converse)
    {c : Cycle j k}
    (hc : cycleClosure cycles (f (some c.1)) (f (some c.2.1)) (f (some c.2.2)))
    {x y z : Atom j k} (h : (x, y, z) ∈ cycleOrbit c) :
    cycleClosure cycles (f x) (f y) (f z) := by
  have h1 := cycleClosure_peirce hc
  have h3 := cycleClosure_converse hc
  have h4 := cycleClosure_peirce h3
  have h2 := cycleClosure_converse h4
  have h5 := cycleClosure_converse h1
  simp only [cycleOrbit, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact hc
  · simpa only [hf] using h1
  · simpa only [hf, Atom.converse_converse] using h2
  · simpa only [hf] using h3
  · simpa only [hf, Atom.converse_converse] using h4
  · simpa only [hf, Atom.converse_converse] using h5

/-- An atom product contains the identity exactly when the factors are converses. -/
theorem cycleClosure_none_result (cycles : Finset (Cycle j k)) (x y : Atom j k) :
    cycleClosure cycles x y none ↔ y = x.converse := by
  cases x <;> cases y <;> simp [cycleClosure, cycleOrbit]

/-- A renaming preserves all cycles if it preserves a list meeting every Peircean orbit. -/
theorem atomRelabelling_of_cycle_basis (reps : Fin n → Cycle j k)
    (cover : ∀ c : Cycle j k, ∃ i, (some c.1, some c.2.1, some c.2.2) ∈ cycleOrbit (reps i))
    {S T : Finset (Cycle j k)} {f : Atom j k → Atom j k}
    (hf : Function.Injective f) (hn : f none = none)
    (hc : ∀ x, f x.converse = (f x).converse)
    (hp : ∀ i, cycleClosure S (some (reps i).1) (some (reps i).2.1) (some (reps i).2.2) ↔
      cycleClosure T (f (some (reps i).1)) (f (some (reps i).2.1)) (f (some (reps i).2.2))) :
    AtomRelabelling S T f := by
  refine ⟨hf, hn, hc, ?_⟩
  intro x y z
  rcases x with _ | x
  · simp only [hn, cycleClosure_none_left, hf.eq_iff]
  rcases y with _ | y
  · simp only [hn, cycleClosure_none_right, hf.eq_iff]
  rcases z with _ | z
  · simp only [hn, cycleClosure_none_result, ← hc, hf.eq_iff]
  obtain ⟨i, hi⟩ := cover (x, y, z)
  constructor
  · intro h
    have hs := cycleClosure_of_mem_orbit h (cycleOrbit_symm hi)
    exact cycleClosure_map_of_mem_orbit hc ((hp i).mp hs) hi
  · intro h
    have ht := cycleClosure_map_of_mem_orbit hc h (cycleOrbit_symm hi)
    exact cycleClosure_of_mem_orbit ((hp i).mpr ht) hi

/-- Evaluate selected cycles from their Boolean choices, without constructing a finset. -/
theorem cycleClosure_selectedCycles (reps : Fin n → Cycle j k) (bits : Fin n → Bool)
    (x y z : Atom j k) :
    cycleClosure (selectedCycles reps bits) x y z ↔
      (x = none ∧ y = z) ∨ (y = none ∧ x = z) ∨
        (z = none ∧ y = x.converse) ∨
          ∃ i : Fin n, bits i = true ∧ (x, y, z) ∈ cycleOrbit (reps i) := by
  constructor
  · rintro (h | h | h | ⟨c, hc, h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hc
      exact Or.inr (Or.inr (Or.inr ⟨i, (Finset.mem_filter.mp hi).2, h⟩))
  · rintro (h | h | h | ⟨i, hi, h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · refine Or.inr (Or.inr (Or.inr ⟨reps i, ?_, h⟩))
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩

/-- For distinct Peircean orbits, a representative is selected exactly when its bit is true. -/
theorem cycleClosure_selectedCycles_rep (reps : Fin n → Cycle j k)
    (distinct : ∀ i l, (some (reps i).1, some (reps i).2.1, some (reps i).2.2) ∈
      cycleOrbit (reps l) ↔ i = l) (bits : Fin n → Bool) (i : Fin n) :
    cycleClosure (selectedCycles reps bits)
      (some (reps i).1) (some (reps i).2.1) (some (reps i).2.2) ↔ bits i = true := by
  rw [cycleClosure_selectedCycles]
  simp only [Option.some_ne_none, false_and, false_or, distinct]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact hl
  · intro hi
    exact ⟨i, hi, rfl⟩

/-- Singletons identify the atom indices with the Boolean atoms of a complex algebra. -/
noncomputable def Complex.atomLabelling (T : IntegralCycleTable j k) :
    AtomLabelling (Complex T) j k where
  equiv := Equiv.ofBijective (fun x => ⟨Complex.atom T x, Complex.isAtom_atom T x⟩) (by
    constructor
    · intro x y h
      exact (Complex.atom_inj T x y).mp (congrArg Subtype.val h)
    · rintro ⟨a, ha⟩
      obtain ⟨x, rfl⟩ := (Complex.isAtom_iff T a).mp ha
      exact ⟨x, rfl⟩)
  map_one := rfl
  map_converse x := (Complex.star_atom T x).symm

/-- A renaming of the atom table extends to an isomorphism of the complex algebras. -/
noncomputable def Complex.equivOfRelabelling (T U : IntegralCycleTable j k)
    (f : Atom j k → Atom j k) (hf : AtomRelabelling T.cycles U.cycles f) :
    RelationAlgebraEquiv (Complex T) (Complex U) := by
  let p : Atom j k ≃ Atom j k :=
    Equiv.ofBijective f ⟨hf.1, Finite.surjective_of_injective hf.1⟩
  let e : AtomLabelling (Complex U) j k :=
    { equiv := p.trans (Complex.atomLabelling U).equiv
      map_one := by change Complex.atom U (f none) = 1; rw [hf.2.1]; rfl
      map_converse := fun x => by
        change Complex.atom U (f x.converse) = star (Complex.atom U (f x))
        rw [hf.2.2.1, Complex.star_atom] }
  exact (e.relationAlgebraEquivTo T fun x y z =>
    (hf.2.2.2 x y z).trans (Complex.atom_le_mul_iff U (f x) (f y) (f z)).symm).symm

/-- Every isomorphism between complex algebras induces a renaming of their atom tables. -/
theorem Complex.exists_relabelling (T U : IntegralCycleTable j k)
    (e : RelationAlgebraEquiv (Complex T) (Complex U)) :
    ∃ f : Atom j k → Atom j k, AtomRelabelling T.cycles U.cycles f := by
  classical
  let o : Complex T ≃o Complex U := e.toOrderIso
  have h (x : Atom j k) : ∃ y, e (Complex.atom T x) = Complex.atom U y :=
    (Complex.isAtom_iff U _).mp ((o.isAtom_iff _).mpr (Complex.isAtom_atom T x))
  choose f hf using h
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    apply (Complex.atom_inj T x y).mp
    apply e.injective
    change e (Complex.atom T x) = e (Complex.atom T y)
    rw [hf, hf, hxy]
  · apply (Complex.atom_inj U _ _).mp
    rw [← hf]
    exact map_one e
  · intro x
    apply (Complex.atom_inj U _ _).mp
    rw [← Complex.star_atom, ← hf, ← hf, ← map_star, Complex.star_atom]
  · intro x y z
    rw [← Complex.atom_le_mul_iff, ← Complex.atom_le_mul_iff, ← hf, ← hf, ← hf,
      ← map_mul]
    exact o.le_iff_le.symm

/-- Classification reduces to a finite check of the possible cycle choices and atom renamings. -/
theorem classification_of_cycle_basis {m : ℕ} (reps : Fin n → Cycle j k)
    (cover : ∀ c : Cycle j k, ∃ i, (some c.1, some c.2.1, some c.2.2) ∈ cycleOrbit (reps i))
    (models : Fin m → IntegralCycleTable j k)
    (exhaustive : ∀ bits : Fin n → Bool, AtomCompositionAssociative (selectedCycles reps bits) →
      ∃ idx : Fin m, ∃ f, AtomRelabelling (selectedCycles reps bits) (models idx).cycles f)
    (distinct : ∀ i j : Fin m, ∀ f,
      AtomRelabelling (models i).cycles (models j).cycles f → i = j)
    (A : Type*) [RelationAlgebra A] (h : HasSignature A 1 j k) :
    ∃! idx : Fin m, Nonempty (RelationAlgebraEquiv A (Complex (models idx))) := by
  classical
  let : Finite A := h.1
  let e := AtomLabelling.ofHasSignature h
  obtain ⟨bits, hb⟩ := exists_selectedCycles reps cover e.table.cycles
  have ha := (atomCompositionAssociative_congr hb).mpr e.table.associative
  let T : IntegralCycleTable j k := ⟨selectedCycles reps bits, ha⟩
  obtain ⟨idx, f, hf⟩ := exhaustive bits ha
  let iso := (e.relationAlgebraEquivTo T fun x y z =>
    (hb x y z).trans (e.cycleClosure_iff x y z)).trans
      (Complex.equivOfRelabelling T (models idx) f hf)
  refine ⟨idx, ⟨iso⟩, ?_⟩
  rintro idx' ⟨iso'⟩
  obtain ⟨f', hf'⟩ := Complex.exists_relabelling (models idx') (models idx) (iso'.symm.trans iso)
  exact distinct idx' idx f' hf'

end Cslib.RelationAlgebra
