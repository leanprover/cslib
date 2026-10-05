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

/-!
# Integral relation algebras from cycles

A finite integral relation algebra has one identity atom, `j` symmetric diversity atoms, and
`k` pairs of nonsymmetric atoms. Its diversity cycles specify which atoms occur in products:
the triple `(x, y, z)` means `z ≤ x * y`. We close the supplied triples under the six Peircean
transforms and add the identity cycles. Associativity is a separate certificate: an arbitrary
list of cycles need not define a relation algebra.

The operations of the complex algebra are concrete and computable. Structural proofs are
deliberately left as `sorry` in this initial statement-only development.

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

instance : Monoid (Complex T) where
  mul_assoc := by sorry
  one_mul := by sorry
  mul_one := by sorry

instance : StarMul (Complex T) where
  star_involutive := by sorry
  star_mul := by sorry

instance : RelationAlgebra (Complex T) where
  sup_mul := by sorry
  star_sup := by sorry
  tarski := by sorry

/-- The singleton generators are precisely the Boolean atoms. -/
theorem isAtom_iff (a : Complex T) : IsAtom a ↔ ∃ x, a = atom T x := by
  sorry

/-- The concrete composition table is exactly the closure of the supplied cycles. -/
theorem atom_le_mul_iff (x y z : Atom j k) :
    atom T z ≤ atom T x * atom T y ↔ cycleClosure T.cycles x y z := by
  sorry

/-- The identity and converse operations give the specified atom counts. -/
theorem hasSignature : HasSignature (Complex T) 1 j k := by
  sorry

/-- The identity is an atom of the complex algebra. -/
theorem integral : Integral (Complex T) := by
  sorry

end Complex

end Cslib.RelationAlgebra
