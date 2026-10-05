/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.GeneralLemmas
public import Cslib.Foundations.RelationAlgebra.Cycles
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Atomic reconstruction of finite relation algebras

Finite relation algebras can be recovered from their atoms and atomic composition.
The reconstruction uses a labelling of the atoms that preserves identity and converse.
-/

@[expose] public section

namespace Cslib.RelationAlgebra
variable {A : Type*} [RelationAlgebra A]
/-- Converse as an order automorphism. -/
def starOrderIso : A ≃o A where
  toFun := star
  invFun := star
  left_inv := star_star
  right_inv := star_star
  map_rel_iff' := by
    intro a b
    change star a ≤ star b ↔ a ≤ b
    exact ⟨fun h => by simpa only [star_star] using star_mono h, fun h => star_mono h⟩
theorem isAtom_star (a : A) : IsAtom (star a) ↔ IsAtom a :=
  starOrderIso.isAtom_iff a
theorem mul_le_compl_iff (a b c : A) : a * b ≤ cᶜ ↔ star a * c ≤ bᶜ := by
  have go (a b c : A) (h : a * b ≤ cᶜ) : star a * c ≤ bᶜ :=
    (mul_le_mul_left (le_compl_iff_le_compl.mp h) (star a)).trans (tarski a b)
  exact ⟨go a b c, fun h => by simpa only [star_star] using go (star a) c b h⟩
theorem atom_not_le_iff_le_compl {a b : A} (ha : IsAtom a) : ¬ a ≤ b ↔ a ≤ bᶜ := by
  rw [ha.not_le_iff_disjoint, le_compl_iff_disjoint_right]
theorem atom_peirce {a b c : A} (hb : IsAtom b) (hc : IsAtom c) :
    c ≤ a * b ↔ b ≤ star a * c := by
  apply not_iff_not.mp
  rw [atom_not_le_iff_le_compl hc, atom_not_le_iff_le_compl hb,
    le_compl_iff_le_compl, mul_le_compl_iff, le_compl_iff_le_compl]
theorem atom_le_sup {a b c : A} (ha : IsAtom a) : a ≤ b ⊔ c ↔ a ≤ b ∨ a ≤ c := by
  simp only [← ha.not_disjoint_iff_le, disjoint_sup_right, not_and_or]
theorem atom_le_finset_sup {a : A} (ha : IsAtom a) {ι : Type*}
    (s : Finset ι) (f : ι → A) : a ≤ s.sup f ↔ ∃ x ∈ s, a ≤ f x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ha.ne_bot]
  | @insert x s hx ih => simp only [Finset.sup_insert, atom_le_sup ha, ih, Finset.mem_insert,
      exists_eq_or_imp]

theorem finset_sup_mul {ι : Type*} (s : Finset ι) (f : ι → A) (b : A) :
    s.sup f * b = s.sup (fun x => f x * b) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih => simp [sup_mul, ih]

theorem mul_finset_sup {ι : Type*} (a : A) (s : Finset ι) (f : ι → A) :
    a * s.sup f = s.sup (fun x => a * f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih => simp [mul_sup, ih]

/-- A finite list of all Boolean atoms respecting identity and converse. -/
structure AtomLabelling (A : Type*) [RelationAlgebra A] (j k : ℕ) where
  /-- The list contains each atom exactly once. -/
  equiv : Atom j k ≃ {a : A // IsAtom a}
  /-- The distinguished index is the identity. -/
  map_one : (equiv none : A) = 1
  /-- Converse agrees with the prescribed involution on indices. -/
  map_converse (x : Atom j k) : (equiv x.converse : A) = star (equiv x : A)

namespace AtomLabelling

variable {j k : ℕ} (e : AtomLabelling A j k)

/-- The algebra element named by an atom index. -/
def val (x : Atom j k) : A := e.equiv x

theorem isAtom_val (x : Atom j k) : IsAtom (e.val x) := (e.equiv x).property

@[simp]
theorem val_inj (x y : Atom j k) : e.val x = e.val y ↔ x = y := by
  constructor
  · intro h
    exact e.equiv.injective (Subtype.ext h)
  · rintro rfl
    rfl

@[simp]
theorem val_le_val (x y : Atom j k) : e.val x ≤ e.val y ↔ x = y :=
  ((e.isAtom_val y).le_iff_eq (e.isAtom_val x).ne_bot).trans (e.val_inj x y)

@[simp]
theorem val_none : e.val none = 1 := e.map_one

@[simp]
theorem val_converse (x : Atom j k) : e.val x.converse = star (e.val x) := e.map_converse x

/-- The indices of the atoms below an element. -/
noncomputable def encode (a : A) : Finset (Atom j k) := by
  classical
  exact Finset.univ.filter fun x => e.val x ≤ a

/-- The join of a finite collection of named atoms. -/
def decode (s : Finset (Atom j k)) : A := s.sup e.val

@[simp]
theorem mem_encode (a : A) (x : Atom j k) : x ∈ e.encode a ↔ e.val x ≤ a := by
  classical
  simp [encode]

@[simp]
theorem val_le_decode (s : Finset (Atom j k)) (x : Atom j k) :
    e.val x ≤ e.decode s ↔ x ∈ s := by
  rw [decode, atom_le_finset_sup (e.isAtom_val x)]
  simp only [(e.isAtom_val _).le_iff_eq (e.isAtom_val x).ne_bot, val_inj]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

@[simp]
theorem encode_decode (s : Finset (Atom j k)) : e.encode (e.decode s) = s := by
  ext x
  simp only [mem_encode, val_le_decode]

@[simp]
theorem decode_encode [Finite A] (a : A) : e.decode (e.encode a) = a := by
  apply BooleanAlgebra.eq_iff_atom_le_iff.mpr
  intro b hb
  obtain ⟨x, hx⟩ := e.equiv.surjective ⟨b, hb⟩
  have hx' : e.val x = b := congrArg Subtype.val hx
  rw [← hx', val_le_decode, mem_encode]

/-- A finite Boolean algebra is the powerset of its named atoms. -/
noncomputable def orderIso [Finite A] : A ≃o Finset (Atom j k) where
  toFun := e.encode
  invFun := e.decode
  left_inv := e.decode_encode
  right_inv := e.encode_decode
  map_rel_iff' := by
    intro a b
    change e.encode a ⊆ e.encode b ↔ a ≤ b
    constructor
    · intro h
      rw [← e.decode_encode a, ← e.decode_encode b]
      exact Finset.sup_mono h
    · intro h x hx
      exact (e.mem_encode b x).mpr (((e.mem_encode a x).mp hx).trans h)

theorem val_le_mul_iff [Finite A] (a b : A) (z : Atom j k) :
    e.val z ≤ a * b ↔
      ∃ x ∈ e.encode a, ∃ y ∈ e.encode b, e.val z ≤ e.val x * e.val y := by
  calc
    e.val z ≤ a * b ↔ e.val z ≤ e.decode (e.encode a) * e.decode (e.encode b) := by
      rw [decode_encode, decode_encode]
    _ ↔ _ := by
      simp only [decode, finset_sup_mul, mul_finset_sup, atom_le_finset_sup (e.isAtom_val z)]
      aesop

/-- All the diversity cycles true of the named atoms. -/
noncomputable def cycles : Finset (Cycle j k) := by
  classical
  exact Finset.univ.filter fun c =>
    e.val (some c.2.2) ≤ e.val (some c.1) * e.val (some c.2.1)

@[simp]
theorem mem_cycles (c : Cycle j k) :
    c ∈ e.cycles ↔ e.val (some c.2.2) ≤ e.val (some c.1) * e.val (some c.2.1) := by
  classical
  simp [cycles]

theorem composition_converse {x y z : Atom j k} (h : e.val z ≤ e.val x * e.val y) :
    e.val z.converse ≤ e.val y.converse * e.val x.converse := by
  simpa only [val_converse, star_mul] using star_mono h

theorem composition_peirce {x y z : Atom j k} (h : e.val z ≤ e.val x * e.val y) :
    e.val y ≤ e.val x.converse * e.val z := by
  rw [val_converse]
  exact (atom_peirce (e.isAtom_val y) (e.isAtom_val z)).mp h

theorem cycleOrbit_le_mul {c : Cycle j k} (hc : c ∈ e.cycles) {x y z : Atom j k}
    (h : (x, y, z) ∈ cycleOrbit c) : e.val z ≤ e.val x * e.val y := by
  have h0 := (e.mem_cycles c).mp hc
  have h1 := e.composition_peirce h0
  have h3 := e.composition_converse h0
  have h4 := e.composition_peirce h3
  have h2 := e.composition_converse h4
  have h5 := e.composition_converse h1
  simp only [cycleOrbit, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact h0
  · exact h1
  · simpa only [Atom.converse_converse] using h2
  · exact h3
  · simpa only [Atom.converse_converse] using h4
  · simpa only [Atom.converse_converse] using h5

theorem cycleClosure_iff (x y z : Atom j k) :
    cycleClosure e.cycles x y z ↔ e.val z ≤ e.val x * e.val y := by
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨c, hc, h⟩)
    · simp
    · simp
    · rw [val_none]
      apply (atom_peirce (e.isAtom_val x.converse) (e.val_none ▸ e.isAtom_val none)).mpr
      simp
    · exact e.cycleOrbit_le_mul hc h
  · intro h
    cases x with
    | none =>
      simp only [val_none, one_mul, val_le_val] at h
      exact Or.inl ⟨rfl, h.symm⟩
    | some x =>
      cases y with
      | none =>
        simp only [val_none, mul_one, val_le_val] at h
        exact Or.inr (Or.inl ⟨rfl, h.symm⟩)
      | some y =>
        cases z with
        | none =>
          have h' := e.composition_peirce h
          simp only [val_none, mul_one, val_le_val] at h'
          exact Or.inr (Or.inr (Or.inl ⟨rfl, h'⟩))
        | some z =>
          refine Or.inr (Or.inr (Or.inr ⟨(x, y, z), (e.mem_cycles _).mpr h, ?_⟩))
          simp only [cycleOrbit, Finset.mem_insert, true_or]

theorem val_le_mul_atom_iff [Finite A] (a : A) (y z : Atom j k) :
    e.val z ≤ a * e.val y ↔ ∃ x, e.val x ≤ a ∧ e.val z ≤ e.val x * e.val y := by
  rw [val_le_mul_iff]
  simp only [mem_encode, val_le_val, exists_eq_left]

theorem val_le_atom_mul_iff [Finite A] (x : Atom j k) (b : A) (z : Atom j k) :
    e.val z ≤ e.val x * b ↔ ∃ y, e.val y ≤ b ∧ e.val z ≤ e.val x * e.val y := by
  rw [val_le_mul_iff]
  simp only [mem_encode, val_le_val, exists_eq_left]

/-- The cycle table of a finite relation algebra, with associativity inherited from it. -/
noncomputable def table [Finite A] : IntegralCycleTable j k where
  cycles := e.cycles
  associative a b c d := by
    simp only [e.cycleClosure_iff]
    rw [← e.val_le_mul_atom_iff, ← e.val_le_atom_mul_iff, mul_assoc]

theorem val_le_star_iff (a : A) (x : Atom j k) :
    e.val x ≤ star a ↔ e.val x.converse ≤ a := by
  rw [val_converse]
  constructor <;> intro h <;> simpa only [star_star] using star_mono h

/-- The Boolean algebra isomorphism into the complex algebra of the extracted table. -/
noncomputable def complexOrderIso [Finite A] : A ≃o Complex e.table where
  toFun a := ⟨e.encode a⟩
  invFun a := e.decode a.atoms
  left_inv := e.decode_encode
  right_inv a := by
    apply Complex.ext
    exact e.encode_decode a.atoms
  map_rel_iff' := by
    intro a b
    change e.encode a ⊆ e.encode b ↔ a ≤ b
    exact e.orderIso.map_rel_iff

/-- A finite relation algebra is reconstructed from its labelled atom composition table. -/
noncomputable def relationAlgebraEquiv [Finite A] : RelationAlgebraEquiv A (Complex e.table) :=
  { e.complexOrderIso with
    map_mul' := by
      intro a b
      apply Complex.ext
      apply Finset.ext
      intro z
      dsimp only [complexOrderIso]
      rw [e.mem_encode, Complex.mem_mul, e.val_le_mul_iff]
      simp only [table, e.cycleClosure_iff]
    map_star' := by
      intro a
      apply Complex.ext
      apply Finset.ext
      intro z
      dsimp only [complexOrderIso]
      rw [e.mem_encode, Complex.mem_star, e.mem_encode, e.val_le_star_iff] }

end AtomLabelling

/-- Two cycle tables with the same full cycle relation have isomorphic complex algebras. -/
def Complex.equivOfCycleClosure {j k : ℕ} (T U : IntegralCycleTable j k)
    (h : ∀ x y z, cycleClosure T.cycles x y z ↔ cycleClosure U.cycles x y z) :
    RelationAlgebraEquiv (Complex T) (Complex U) where
  toFun a := ⟨a.atoms⟩
  invFun a := ⟨a.atoms⟩
  left_inv a := by cases a; rfl
  right_inv a := by cases a; rfl
  map_rel_iff' := Iff.rfl
  map_mul' a b := by
    apply Complex.ext
    apply Finset.ext
    intro z
    dsimp only
    simp only [Complex.mem_mul, h]
  map_star' a := rfl

/-- Reconstruction against any supplied cycle table with the same atom composition. -/
noncomputable def AtomLabelling.relationAlgebraEquivTo {j k : ℕ} [Finite A]
    (e : AtomLabelling A j k) (T : IntegralCycleTable j k)
    (h : ∀ x y z, cycleClosure T.cycles x y z ↔ e.val z ≤ e.val x * e.val y) :
    RelationAlgebraEquiv A (Complex T) :=
  e.relationAlgebraEquiv.trans (Complex.equivOfCycleClosure e.table T fun x y z =>
    (e.cycleClosure_iff x y z).trans (h x y z).symm)

universe u
variable {α : Type u}
section LinearOrder
variable [LinearOrder α]
private def involutionPairMap (f : α → α) (p : {x : α // x < f x} × Bool) : α :=
  if p.2 then f p.1 else p.1
private theorem involutionPairMap_bijective (f : α → α) (hf : Function.Involutive f)
    (hn : ∀ x, f x ≠ x) : Function.Bijective (involutionPairMap f) := by
  constructor
  · rintro ⟨x, b⟩ ⟨y, c⟩ h
    have hx := x.property
    have hy := y.property
    cases b <;> cases c <;>
      simp only [involutionPairMap, Bool.false_eq_true, ite_false, ite_true] at h
    · exact Prod.ext (Subtype.ext h) rfl
    · have hh : f (y : α) < (y : α) := by simpa only [h, hf (y : α)] using hx
      exact False.elim (lt_asymm hy hh)
    · have hh : f (x : α) < (x : α) := by simpa only [← h, hf (x : α)] using hy
      exact False.elim (lt_asymm hx hh)
    · exact Prod.ext (Subtype.ext (hf.injective h)) rfl
  · intro x
    by_cases hx : x < f x
    · exact ⟨(⟨x, hx⟩, false), rfl⟩
    · have hx' : f x < x := lt_of_le_of_ne (le_of_not_gt hx) (hn x)
      exact ⟨(⟨f x, by simpa only [hf x] using hx'⟩, true), hf x⟩
private noncomputable def involutionPairEquiv (f : α → α) (hf : Function.Involutive f)
    (hn : ∀ x, f x ≠ x) : {x : α // x < f x} × Bool ≃ α :=
  Equiv.ofBijective (involutionPairMap f) (involutionPairMap_bijective f hf hn)
private theorem involutionPairEquiv_flip (f : α → α) (hf : Function.Involutive f)
    (hn : ∀ x, f x ≠ x) (p : {x : α // x < f x} × Bool) :
    involutionPairEquiv f hf hn (p.1, !p.2) = f (involutionPairEquiv f hf hn p) := by
  rcases p with ⟨x,b⟩
  cases b <;> simp [involutionPairEquiv, involutionPairMap, hf (x : α)]
end LinearOrder
/-- A fixed-point-free involution on a finite type is a disjoint union of converse pairs. -/
theorem exists_equiv_fin_prod_bool [Finite α] (f : α → α) (hf : Function.Involutive f)
    (hn : ∀ x, f x ≠ x) {k : ℕ} (hc : Nat.card α = 2 * k) :
    ∃ e : Fin k × Bool ≃ α, ∀ p, e (p.1, !p.2) = f (e p) := by
  classical
  let enum := Finite.equivFin α
  let _ : LinearOrder α := enum.linearOrder
  let g := involutionPairEquiv f hf hn
  have hcard : Nat.card {x : α // x < f x} = k := by
    have h := Nat.card_congr g
    simp only [Nat.card_prod, hc, Nat.card_eq_fintype_card, Fintype.card_bool] at h
    omega
  let eR := Finite.equivFinOfCardEq hcard
  let e : Fin k × Bool ≃ α := (Equiv.prodCongr eR.symm (Equiv.refl Bool)).trans g
  refine ⟨e, ?_⟩
  intro p
  exact involutionPairEquiv_flip f hf hn (eR.symm p.1, p.2)
/-- Converse preserves Boolean complements. -/
@[simp]
theorem star_compl (a : A) : star aᶜ = (star a)ᶜ :=
  map_compl' (starOrderIso : A ≃o A) a
/-- The symmetric Boolean atoms below diversity. -/
abbrev SymmetricDiversity (A : Type*) [RelationAlgebra A] :=
  {a : A // IsAtom a ∧ a ≤ (1 : A)ᶜ ∧ star a = a}
/-- The nonsymmetric Boolean atoms below diversity. -/
abbrev NonsymmetricDiversity (A : Type*) [RelationAlgebra A] :=
  {a : A // IsAtom a ∧ a ≤ (1 : A)ᶜ ∧ star a ≠ a}
/-- Converse restricts to the nonsymmetric diversity atoms. -/
def nonsymmetricConverse (a : NonsymmetricDiversity A) : NonsymmetricDiversity A :=
  ⟨star (a : A), (isAtom_star (a : A)).mpr a.property.1,
    by simpa only [star_compl, star_one] using star_mono a.property.2.1,
    fun h => a.property.2.2 (by simpa only [star_star] using h.symm)⟩
theorem nonsymmetricConverse_involutive :
    Function.Involutive (nonsymmetricConverse (A := A)) :=
  fun a => Subtype.ext (star_star a.val)
theorem nonsymmetricConverse_ne (a : NonsymmetricDiversity A) : nonsymmetricConverse a ≠ a :=
  fun h => a.property.2.2 (congrArg Subtype.val h)
/-- Label all atoms using the number of symmetric atoms and nonsymmetric converse pairs. -/
noncomputable def AtomLabelling.ofCardinalities [Finite A] {j k : ℕ} (h1 : IsAtom (1 : A))
    (hs : Nat.card (SymmetricDiversity A) = j)
    (hn : Nat.card (NonsymmetricDiversity A) = 2 * k) : AtomLabelling A j k := by
  classical
  let s := (Finite.equivFinOfCardEq hs).symm
  have hp := exists_equiv_fin_prod_bool (nonsymmetricConverse (A := A))
    nonsymmetricConverse_involutive nonsymmetricConverse_ne hn
  let n := Classical.choose hp
  have hflip := Classical.choose_spec hp
  let f : Atom j k → {a : A // IsAtom a}
    | none => ⟨1, h1⟩
    | some (.inl x) => ⟨s x, (s x).property.1⟩
    | some (.inr x) => ⟨n x, (n x).property.1⟩
  have hdiv (a : A) (ha : a ≤ (1 : A)ᶜ) : a ≠ 1 := by
    intro h
    rw [h] at ha
    exact h1.ne_bot (le_compl_self.mp ha)
  have hinj : Function.Injective f := by
    intro x y h
    have hv := congrArg Subtype.val h
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some y =>
        rcases y with y | y
        · exact False.elim (hdiv (s y) (s y).property.2.1 hv.symm)
        · exact False.elim (hdiv (n y) (n y).property.2.1 hv.symm)
    | some x =>
      cases y with
      | none =>
        rcases x with x | x
        · exact False.elim (hdiv (s x) (s x).property.2.1 hv)
        · exact False.elim (hdiv (n x) (n x).property.2.1 hv)
      | some y =>
        rcases x with x | x <;> rcases y with y | y
        · exact congrArg (fun x => some (Sum.inl x)) (s.injective (Subtype.ext hv))
        · have hsx := (s x).property.2.2
          have hny := (n y).property.2.2
          exact False.elim (hny (by simpa only [show (s x : A) = (n y : A) from hv] using hsx))
        · have hnx := (n x).property.2.2
          have hsy := (s y).property.2.2
          exact False.elim (hnx (by simpa only [show (s y : A) = (n x : A) from hv.symm] using hsy))
        · exact congrArg (fun x => some (Sum.inr x)) (n.injective (Subtype.ext hv))
  have hsurj : Function.Surjective f := by
    rintro ⟨a, ha⟩
    by_cases hai : a ≤ 1
    · have heq := (h1.le_iff_eq ha.ne_bot).mp hai
      exact ⟨none, Subtype.ext heq.symm⟩
    · have had := (atom_not_le_iff_le_compl ha).mp hai
      by_cases has : star a = a
      · obtain ⟨x, hx⟩ := s.surjective ⟨a, ha, had, has⟩
        exact ⟨some (.inl x), Subtype.ext (congrArg (fun t : SymmetricDiversity A => (t : A)) hx)⟩
      · obtain ⟨x, hx⟩ := n.surjective ⟨a, ha, had, has⟩
        exact ⟨some (.inr x),
          Subtype.ext (congrArg (fun t : NonsymmetricDiversity A => (t : A)) hx)⟩
  refine { equiv := Equiv.ofBijective f ⟨hinj, hsurj⟩, map_one := rfl, map_converse := ?_ }
  intro x
  cases x with
  | none => exact (star_one A).symm
  | some x =>
    rcases x with x | ⟨x,b⟩
    · exact (s x).property.2.2.symm
    · exact congrArg Subtype.val (hflip (x,b))

end Cslib.RelationAlgebra
