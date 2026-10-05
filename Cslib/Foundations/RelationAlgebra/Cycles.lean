/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/
module

public import Cslib.Foundations.RelationAlgebra.Representation
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Data.Finset.Grade

/-!
# Integral relation algebras from cycles

A finite integral relation algebra has one identity atom, `j` symmetric diversity atoms, and
`k` pairs of nonsymmetric atoms. Its diversity cycles specify which atoms occur in products:
the triple `(x, y, z)` means `z ≤ x * y`. We close the supplied triples under the six Peircean
transforms and add the identity cycles. Associativity is a separate certificate: an arbitrary
list of cycles need not define a relation algebra.

The operations of the complex algebra are concrete and computable. The cycle symmetries and
associativity certificate supply its relation algebra laws and its atom counts.

The convention follows Peter Jipsen's catalogue of small integral relation algebras:
<https://www1.chapman.edu/~jipsen/gap/ramaddux.html>.
-/

@[expose] public section

namespace Cslib.RelationAlgebra

/-- The diversity atoms: symmetric atoms and pairs exchanged by converse. -/
abbrev DiversityAtom (j k : ℕ) := Fin j ⊕ (Fin k × Bool)

/-- The atoms of an integral algebra; `none` is the identity atom. -/
abbrev Atom (j k : ℕ) := Option (DiversityAtom j k)

/-- A diversity-cycle representative, with the third atom below the product of the first two. -/
abbrev Cycle (j k : ℕ) := DiversityAtom j k × DiversityAtom j k × DiversityAtom j k

variable {j k : ℕ}

instance : DecidableEq (DiversityAtom j k) :=
  inferInstanceAs (DecidableEq (Fin j ⊕ (Fin k × Bool)))

instance : DecidableEq (Atom j k) :=
  inferInstanceAs (DecidableEq (Option (DiversityAtom j k)))

/-- Converse fixes symmetric atoms and exchanges the two atoms in each nonsymmetric pair. -/
def DiversityAtom.converse : DiversityAtom j k → DiversityAtom j k
  | .inl a => .inl a
  | .inr (a, b) => .inr (a, !b)

/-- Converse on atoms fixes the identity atom. -/
def Atom.converse : Atom j k → Atom j k := Option.map DiversityAtom.converse

@[simp]
theorem DiversityAtom.converse_converse (a : DiversityAtom j k) :
    a.converse.converse = a := by
  rcases a with a | ⟨a, b⟩ <;> simp [DiversityAtom.converse]

@[simp]
theorem Atom.converse_converse (a : Atom j k) : a.converse.converse = a := by
  cases a <;> simp [Atom.converse]

@[simp]
theorem Atom.converse_none : Atom.converse (none : Atom j k) = none := rfl

@[simp]
theorem Atom.converse_some (a : DiversityAtom j k) :
    Atom.converse (some a : Atom j k) = some a.converse := rfl

/-- The six Peircean transforms of a diversity cycle. -/
def cycleOrbit (c : Cycle j k) : Finset (Atom j k × Atom j k × Atom j k) :=
  let x := some c.1
  let y := some c.2.1
  let z := some c.2.2
  let conv := Atom.converse
  {(x, y, z), (conv x, z, y), (z, conv y, x),
    (conv y, conv x, conv z), (y, conv z, conv x), (conv z, x, conv y)}

/-- The full cycle relation, including all and only the obligatory identity cycles. -/
def cycleClosure (cycles : Finset (Cycle j k)) (x y z : Atom j k) : Prop :=
  (x = none ∧ y = z) ∨ (y = none ∧ x = z) ∨ (z = none ∧ y = Atom.converse x) ∨
    ∃ c ∈ cycles, (x, y, z) ∈ cycleOrbit c

theorem cycleOrbit_converse {c : Cycle j k} {x y z : Atom j k}
    (h : (x, y, z) ∈ cycleOrbit c) :
    (y.converse, x.converse, z.converse) ∈ cycleOrbit c := by
  simp only [cycleOrbit, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    simp [cycleOrbit]

theorem cycleOrbit_peirce {c : Cycle j k} {x y z : Atom j k}
    (h : (x, y, z) ∈ cycleOrbit c) : (x.converse, z, y) ∈ cycleOrbit c := by
  simp only [cycleOrbit, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    simp [cycleOrbit]

@[simp]
theorem cycleClosure_none_left (cycles : Finset (Cycle j k)) (y z : Atom j k) :
    cycleClosure cycles none y z ↔ y = z := by
  cases y <;> cases z <;> simp [cycleClosure, cycleOrbit]

@[simp]
theorem cycleClosure_none_right (cycles : Finset (Cycle j k)) (x z : Atom j k) :
    cycleClosure cycles x none z ↔ x = z := by
  cases x <;> cases z <;> simp [cycleClosure, cycleOrbit]

theorem cycleClosure_converse {cycles : Finset (Cycle j k)} {x y z : Atom j k}
    (h : cycleClosure cycles x y z) : cycleClosure cycles y.converse x.converse z.converse := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨c, hc, h⟩
  · simp
  · simp
  · simp [cycleClosure]
  · exact Or.inr (Or.inr (Or.inr ⟨c, hc, cycleOrbit_converse h⟩))

theorem cycleClosure_peirce {cycles : Finset (Cycle j k)} {x y z : Atom j k}
    (h : cycleClosure cycles x y z) : cycleClosure cycles x.converse z y := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨c, hc, h⟩
  · simp
  · simp [cycleClosure]
  · simp
  · exact Or.inr (Or.inr (Or.inr ⟨c, hc, cycleOrbit_peirce h⟩))

instance (cycles : Finset (Cycle j k)) (x y z : Atom j k) :
    Decidable (cycleClosure cycles x y z) := by
  unfold cycleClosure
  infer_instance

/-- Associativity expressed entirely in the finite atom composition table. -/
def AtomCompositionAssociative (cycles : Finset (Cycle j k)) : Prop :=
  ∀ a b c d : Atom j k,
    (∃ t, cycleClosure cycles a b t ∧ cycleClosure cycles t c d) ↔
      (∃ t, cycleClosure cycles b c t ∧ cycleClosure cycles a t d)

instance (cycles : Finset (Cycle j k)) : Decidable (AtomCompositionAssociative cycles) := by
  unfold AtomCompositionAssociative
  infer_instance

/-- An integral cycle table certified to have associative composition. -/
structure IntegralCycleTable (j k : ℕ) where
  /-- Representatives of the diversity cycles. -/
  cycles : Finset (Cycle j k)
  /-- The finite atom composition table is associative. -/
  associative : AtomCompositionAssociative cycles

/-- The Boolean powerset of the atoms of a certified table, with its own algebra instances. -/
structure Complex (T : IntegralCycleTable j k) where
  /-- The atoms below this element. -/
  atoms : Finset (Atom j k)
  deriving DecidableEq

namespace Complex

variable (T : IntegralCycleTable j k)

/-- The underlying finite powerset of atoms. -/
def equivFinset : Complex T ≃ Finset (Atom j k) where
  toFun := Complex.atoms
  invFun := Complex.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype (Complex T) := Fintype.ofEquiv _ (equivFinset T).symm

instance : BooleanAlgebra (Complex T) := (equivFinset T).booleanAlgebra

instance : DecidableLE (Complex T) := inferInstanceAs (DecidableRel fun a b : Complex T =>
  a.atoms ⊆ b.atoms)

/-- The algebra element corresponding to a single atom. -/
def atom (x : Atom j k) : Complex T := ⟨{x}⟩

instance : One (Complex T) := ⟨atom T none⟩

instance : Mul (Complex T) where
  mul a b := ⟨Finset.univ.filter fun z =>
    ∃ x ∈ a.atoms, ∃ y ∈ b.atoms, cycleClosure T.cycles x y z⟩

instance : Star (Complex T) where
  star a := ⟨a.atoms.image Atom.converse⟩

@[ext]
theorem ext {a b : Complex T} (h : a.atoms = b.atoms) : a = b :=
  (equivFinset T).injective h

@[simp]
theorem atoms_sup (a b : Complex T) : (a ⊔ b).atoms = a.atoms ∪ b.atoms := rfl

@[simp]
theorem atoms_inf (a b : Complex T) : (a ⊓ b).atoms = a.atoms ∩ b.atoms := rfl

@[simp]
theorem atoms_top : (⊤ : Complex T).atoms = Finset.univ := rfl

@[simp]
theorem atoms_bot : (⊥ : Complex T).atoms = ∅ := rfl

theorem le_iff (a b : Complex T) : a ≤ b ↔ a.atoms ⊆ b.atoms := Iff.rfl

theorem mem_sup (a b : Complex T) (z : Atom j k) :
    z ∈ (a ⊔ b).atoms ↔ z ∈ a.atoms ∨ z ∈ b.atoms := Finset.mem_union

@[simp]
theorem mem_compl (a : Complex T) (z : Atom j k) :
    z ∈ aᶜ.atoms ↔ z ∉ a.atoms := Finset.mem_compl

@[simp]
theorem mem_mul (a b : Complex T) (z : Atom j k) :
    z ∈ (a * b).atoms ↔ ∃ x ∈ a.atoms, ∃ y ∈ b.atoms, cycleClosure T.cycles x y z := by
  change z ∈ Finset.univ.filter _ ↔ _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

@[simp]
theorem mem_one (z : Atom j k) : z ∈ (1 : Complex T).atoms ↔ z = none :=
  Finset.mem_singleton

@[simp]
theorem mem_star (a : Complex T) (z : Atom j k) :
    z ∈ (star a).atoms ↔ z.converse ∈ a.atoms := by
  change z ∈ a.atoms.image Atom.converse ↔ _
  rw [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨z.converse, h, by simp⟩

instance : Monoid (Complex T) where
  mul_assoc a b c := by
    apply ext
    apply Finset.ext
    intro z
    simp only [mem_mul]
    constructor
    · rintro ⟨u, ⟨x, hx, y, hy, hxy⟩, w, hw, huw⟩
      obtain ⟨t, hyt, hxt⟩ := (T.associative x y w z).mp ⟨u, hxy, huw⟩
      exact ⟨x, hx, t, ⟨y, hy, w, hw, hyt⟩, hxt⟩
    · rintro ⟨x, hx, t, ⟨y, hy, w, hw, hyt⟩, hxt⟩
      obtain ⟨u, hxy, huw⟩ := (T.associative x y w z).mpr ⟨t, hyt, hxt⟩
      exact ⟨u, ⟨x, hx, y, hy, hxy⟩, w, hw, huw⟩
  one_mul a := by
    apply ext
    apply Finset.ext
    intro z
    simp [mem_mul]
  mul_one a := by
    apply ext
    apply Finset.ext
    intro z
    simp [mem_mul]

instance : StarMul (Complex T) where
  star_involutive a := by
    apply ext
    apply Finset.ext
    intro z
    simp
  star_mul a b := by
    apply ext
    apply Finset.ext
    intro z
    simp only [mem_star, mem_mul]
    constructor
    · rintro ⟨x, hx, y, hy, h⟩
      exact ⟨y.converse, by simpa using hy, x.converse, by simpa using hx,
        by simpa using cycleClosure_converse h⟩
    · rintro ⟨x, hx, y, hy, h⟩
      exact ⟨y.converse, hy, x.converse, hx, cycleClosure_converse h⟩

instance : RelationAlgebra (Complex T) where
  sup_mul a b c := by
    apply ext
    apply Finset.ext
    intro z
    simp only [mem_mul, mem_sup]
    aesop
  star_sup a b := by
    apply ext
    apply Finset.ext
    intro z
    simp only [mem_star, mem_sup]
  tarski a b := by
    rw [le_iff]
    intro z hz
    rw [mem_compl]
    obtain ⟨x, hx, y, hy, h⟩ := (mem_mul T _ _ _).mp hz
    rw [mem_star] at hx
    rw [mem_compl] at hy
    intro hz
    apply hy
    exact (mem_mul T _ _ _).mpr ⟨x.converse, hx, z, hz, cycleClosure_peirce h⟩

/-- The singleton generators are precisely the Boolean atoms. -/
theorem isAtom_iff (a : Complex T) : IsAtom a ↔ ∃ x, a = atom T x := by
  let e : Complex T ≃o Finset (Atom j k) :=
    { equivFinset T with map_rel_iff' := Iff.rfl }
  rw [← e.isAtom_iff, Finset.isAtom_iff]
  constructor
  · rintro ⟨x, h⟩
    exact ⟨x, ext T h⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩

@[simp]
theorem isAtom_atom (x : Atom j k) : IsAtom (atom T x) :=
  (isAtom_iff T _).mpr ⟨x, rfl⟩

@[simp]
theorem atom_inj (x y : Atom j k) : atom T x = atom T y ↔ x = y := by
  constructor
  · intro h
    exact Finset.singleton_injective (congrArg Complex.atoms h)
  · rintro rfl
    rfl

@[simp]
theorem atom_le_one (x : Atom j k) : atom T x ≤ 1 ↔ x = none := by
  rw [le_iff]
  exact Finset.singleton_subset_iff.trans (mem_one T x)

@[simp]
theorem atom_le_compl_one (x : Atom j k) : atom T x ≤ (1 : Complex T)ᶜ ↔ x ≠ none := by
  rw [le_iff]
  exact Finset.singleton_subset_iff.trans ((mem_compl T 1 x).trans (not_congr (mem_one T x)))

@[simp]
theorem star_atom (x : Atom j k) : star (atom T x) = atom T x.converse := by
  apply ext
  change Finset.image Atom.converse {x} = {Atom.converse x}
  simp only [Finset.image_singleton]

/-- The concrete composition table is exactly the closure of the supplied cycles. -/
theorem atom_le_mul_iff (x y z : Atom j k) :
    atom T z ≤ atom T x * atom T y ↔ cycleClosure T.cycles x y z := by
  rw [le_iff]
  simp only [atom, Finset.singleton_subset_iff, mem_mul, Finset.mem_singleton,
    exists_eq_left]

/-- The identity and converse operations give the specified atom counts. -/
theorem hasSignature : HasSignature (Complex T) 1 j k := by
  classical
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · let _ : Unique {a : Complex T // IsAtom a ∧ a ≤ 1} := {
      default := ⟨atom T none, isAtom_atom T none, le_rfl⟩
      uniq a := by
        apply Subtype.ext
        obtain ⟨x, hx⟩ := (isAtom_iff T a.val).mp a.property.1
        have h := a.property.2
        rw [hx, atom_le_one] at h
        simpa [h] using hx }
    exact Nat.card_unique
  · let f : Fin j → {a : Complex T // IsAtom a ∧ a ≤ (1 : Complex T)ᶜ ∧ star a = a} :=
      fun x => ⟨atom T (some (.inl x)), by simp [DiversityAtom.converse]⟩
    have hf : Function.Bijective f := by
      constructor
      · intro x y h
        have h' := congrArg Subtype.val h
        simpa [f] using h'
      · rintro ⟨a, ha, hle, hstar⟩
        obtain ⟨x, rfl⟩ := (isAtom_iff T a).mp ha
        cases x with
        | none => simp at hle
        | some x =>
          rcases x with x | ⟨x, b⟩
          · exact ⟨x, rfl⟩
          · cases b <;> simp [DiversityAtom.converse] at hstar
    exact (Nat.card_congr (Equiv.ofBijective f hf)).symm.trans (by simp)
  · let f : Fin k × Bool →
        {a : Complex T // IsAtom a ∧ a ≤ (1 : Complex T)ᶜ ∧ star a ≠ a} :=
      fun x => ⟨atom T (some (.inr x)), by
        rcases x with ⟨x, b⟩
        cases b <;> simp [DiversityAtom.converse]⟩
    have hf : Function.Bijective f := by
      constructor
      · intro x y h
        have h' := congrArg Subtype.val h
        simpa [f] using h'
      · rintro ⟨a, ha, hle, hstar⟩
        obtain ⟨x, rfl⟩ := (isAtom_iff T a).mp ha
        cases x with
        | none => simp at hle
        | some x =>
          rcases x with x | x
          · simp [DiversityAtom.converse] at hstar
          · exact ⟨x, rfl⟩
    exact (Nat.card_congr (Equiv.ofBijective f hf)).symm.trans (by simp [Nat.mul_comm])

/-- The identity is an atom of the complex algebra. -/
theorem integral : Integral (Complex T) := by
  exact isAtom_atom T none

end Complex

end Cslib.RelationAlgebra
