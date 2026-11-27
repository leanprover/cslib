/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.AtomStructure
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Integral atom structures

This module abstractly defines the atoms of an integral relation algebra, along with a
characterization of its identity and non-identity cycles that form an atom structure when
shown to be associative.

## References

* [Steven Givant, *Introduction to Relation Algebras*][Givant2017a], Section 4.2
* [Steven Givant, *Advanced Topics in Relation Algebras*][Givant2017b], Section 19.3
* [Peter Jipsen, *Small relation algebras*](https://www1.chapman.edu/~jipsen/gap/ramaddux.html)

-/

@[expose] public section

namespace Cslib.RelationAlgebra

/--
The atoms of an integral atom structure: the identity atom, a type `α` of symmetric diversity atoms,
and a type `β` of pairs of nonsymmetric atoms.
-/
inductive IntegralAtom (α β : Type*) where
  /-- The identity atom. -/
  | one
  /-- A symmetric diversity atom. -/
  | symm (a : α)
  /-- A nonsymmetric atom. `nsymm b true` is the converse of `nsymm b false`. -/
  | nsymm (b : β) (conv : Bool)
  deriving DecidableEq

namespace IntegralAtom

variable {α β : Type*}

/-- `IntegralAtom α β` as a sum. -/
def equivOptionSum : IntegralAtom α β ≃ Option (α ⊕ β × Bool) where
  toFun
    | one => none
    | symm a => some (.inl a)
    | nsymm b d => some (.inr (b, d))
  invFun
    | none => one
    | some (.inl a) => symm a
    | some (.inr (b, d)) => nsymm b d
  left_inv := by rintro (_ | _ | _) <;> rfl
  right_inv := by rintro (_ | _ | ⟨_, _⟩) <;> rfl

instance [Fintype α] [Fintype β] : Fintype (IntegralAtom α β) := .ofEquiv _ equivOptionSum.symm

/-- The converse of an atom, where just nonsymmetric atoms are flipped. -/
def conv : IntegralAtom α β → IntegralAtom α β
  | one => one
  | symm a => symm a
  | nsymm b d => nsymm b (!d)

/-- An integral cycle is a triple of integral atoms. -/
abbrev Cycle (α β : Type*) := IntegralAtom α β × IntegralAtom α β × IntegralAtom α β

/-- The left cycle transformation: `t ≤ r * u` implies `u ≤ conv r * t` -/
def Cycle.left : Cycle α β → Cycle α β
  | (r, u, t) => (conv r, t, u)

/-- The right cycle transformation: `t ≤ r * u` implies `r ≤ t * conv u` -/
def Cycle.right : Cycle α β → Cycle α β
  | (r, u, t) => (t, conv u, r)

/-- A cycle without identity. -/
abbrev Cycle.IsDiversity : Cycle α β → Prop
  | (r, u, t) => r ≠ one ∧ u ≠ one ∧ t ≠ one

/-- The union of the Peircean orbits of the generators and all identity cycles. -/
inductive CycleClosure (g : Set (Cycle α β)) : Cycle α β → Prop
  | of {c : Cycle α β} : c ∈ g → CycleClosure g c
  | id (x : IntegralAtom α β) : CycleClosure g (x, one, x)
  | left {c : Cycle α β} : CycleClosure g c → CycleClosure g c.left
  | right {c : Cycle α β} : CycleClosure g c → CycleClosure g c.right

@[simp, grind =]
theorem conv_one : conv (one : IntegralAtom α β) = one := rfl

@[simp, grind =]
theorem conv_symm (a : α) : conv (symm a : IntegralAtom α β) = symm a := rfl

@[simp, grind =]
theorem conv_nsymm (b : β) (d : Bool) : conv (nsymm b d : IntegralAtom α β) = nsymm b !d := rfl

@[simp, grind =]
theorem conv_conv (x : IntegralAtom α β) : conv (conv x) = x := by
  cases x <;> simp

private theorem CycleClosure.id_cycle_aux {g : Set (Cycle α β)} (hg : ∀ c ∈ g, c.IsDiversity)
    {r u t : IntegralAtom α β} (h : CycleClosure g (r, u, t)) :
    (r = one → t = u) ∧ (u = one → t = r) ∧ (t = one → u = conv r) := by
  generalize hc : (r, u, t) = c at h
  induction h generalizing r u t <;> grind [Cycle.left, Cycle.right, conv_conv]

theorem CycleClosure.id_cycle_left {g : Set (Cycle α β)} (hg : ∀ c ∈ g, c.IsDiversity)
    {u t : IntegralAtom α β} (h : CycleClosure g (one, u, t)) : t = u :=
  (h.id_cycle_aux hg).1 rfl

theorem CycleClosure.id_cycle_right {g : Set (Cycle α β)} (hg : ∀ c ∈ g, c.IsDiversity)
    {r t : IntegralAtom α β} (h : CycleClosure g (r, one, t)) : t = r :=
  (h.id_cycle_aux hg).2.1 rfl

theorem CycleClosure.id_cycle_conv {g : Set (Cycle α β)} (hg : ∀ c ∈ g, c.IsDiversity)
    {r u : IntegralAtom α β} (h : CycleClosure g (r, u, one)) : u = conv r :=
  (h.id_cycle_aux hg).2.2 rfl

theorem cycleClosure_one_iff {g : Set (Cycle α β)} (hg : ∀ c ∈ g, c.IsDiversity)
    {r p : IntegralAtom α β} : CycleClosure g (r, one, p) ↔ p = r :=
  ⟨fun h => h.id_cycle_right hg, fun h => h ▸ .id p⟩

/-- Construct an `AtomStructure` from diversity cycle generators. -/
def ofCycles (g : Set (Cycle α β)) : AtomStructure (IntegralAtom α β) where
  conv := conv
  id := {one}
  cycles := {c | CycleClosure g c}

@[simp]
theorem ofCycles_conv (g : Set (Cycle α β)) (x : IntegralAtom α β) :
    (ofCycles g).conv x = conv x := rfl

@[simp]
theorem mem_ofCycles_id {g : Set (Cycle α β)} {x : IntegralAtom α β} :
    x ∈ (ofCycles g).id ↔ x = one := .rfl

@[simp]
theorem mem_ofCycles_cycles {g : Set (Cycle α β)} {c : Cycle α β} :
    c ∈ (ofCycles g).cycles ↔ CycleClosure g c := .rfl

theorem lawfulAtomStructure_ofCycles (g : Set (Cycle α β))
    (hassoc : ∀ {r q p u t}, CycleClosure g (r, q, p) → CycleClosure g (u, t, q) →
      ∃ q', CycleClosure g (q', t, p) ∧ CycleClosure g (r, u, q'))
    (hg : ∀ c ∈ g, c.IsDiversity) :
    LawfulAtomStructure (ofCycles g) where
  assoc := hassoc
  id_cycle_right hs h := (cycleClosure_one_iff hg).mp (hs ▸ h)
  exists_id_cycle_right r := ⟨one, rfl, .id r⟩
  cycle_left := .left

/-- The complex algebra constructed from diversity cycles is integral. -/
@[simp]
theorem isIntegral_ofCycles (g : Set (Cycle α β)) [LawfulAtomStructure (ofCycles g)] :
    IsIntegral (ComplexAlgebra (ofCycles g)) :=
  (ComplexAlgebra.isIntegral_iff _).mpr ⟨one, rfl⟩

theorem preimage_singleton_symmetricDiversityAtoms (g : Set (Cycle α β))
    [LawfulAtomStructure (ofCycles g)] :
    singleton ⁻¹' symmetricDiversityAtoms (ComplexAlgebra (ofCycles g)) = Set.range symm := by
  ext x
  cases x <;> simp

theorem preimage_singleton_nonsymmetricDiversityAtoms (g : Set (Cycle α β))
    [LawfulAtomStructure (ofCycles g)] :
    singleton ⁻¹' nonsymmetricDiversityAtoms (ComplexAlgebra (ofCycles g)) =
      Set.range (Function.uncurry nsymm) := by
  ext x
  cases x <;> simp

theorem ncard_symmetricDiversityAtoms_ofCycles (g : Set (Cycle α β))
    [LawfulAtomStructure (ofCycles g)] :
    (symmetricDiversityAtoms (ComplexAlgebra (ofCycles g))).ncard = Nat.card α := by
  rw [← ComplexAlgebra.ncard_preimage_singleton fun _ => And.left,
    preimage_singleton_symmetricDiversityAtoms,
    Set.ncard_range_of_injective fun _ _ => symm.inj]

theorem ncard_nonsymmetricDiversityAtoms_ofCycles (g : Set (Cycle α β))
    [LawfulAtomStructure (ofCycles g)] :
    (nonsymmetricDiversityAtoms (ComplexAlgebra (ofCycles g))).ncard = 2 * Nat.card β := by
  rw [← ComplexAlgebra.ncard_preimage_singleton fun _ => And.left,
    preimage_singleton_nonsymmetricDiversityAtoms,
    Set.ncard_range_of_injective (by simp [Function.Injective])]
  simp [mul_comm]

instance (g : {g : Set (Cycle α β) // LawfulAtomStructure (ofCycles g)}) :
    LawfulAtomStructure (ofCycles g.val) := g.property

instance setoid (α β : Type*) :
    Setoid {g : Set (Cycle α β) // LawfulAtomStructure (ofCycles g)} where
  r g₁ g₂ := Nonempty (RelationAlgebraEquiv (ComplexAlgebra (ofCycles g₁.val))
    (ComplexAlgebra (ofCycles g₂.val)))
  iseqv := ⟨fun _ => ⟨.refl _⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

private theorem exists_equiv_fin_prod_bool {X : Type*} [Finite X] {f : X → X}
    (hf : ∀ x, f (f x) = x) (hne : ∀ x, f x ≠ x) {n : ℕ} (hn : Nat.card X = 2 * n) :
    ∃ e : X ≃ Fin n × Bool, ∀ x, e (f x) = ((e x).1, !(e x).2) := by
  classical
  let ι := Finite.equivFin X
  have hlt : ∀ x, ¬ι x < ι (f x) → ι (f x) < ι (f (f x)) := fun x hx => by
    rw [hf]
    exact lt_of_le_of_ne (not_lt.mp hx) fun h => hne x (ι.injective h)
  let φ : X ≃ {x : X // ι x < ι (f x)} × Bool :=
    { toFun x := if h : ι x < ι (f x) then (⟨x, h⟩, false) else (⟨f x, hlt x h⟩, true)
      invFun p := if p.2 then f p.1 else p.1
      left_inv x := by by_cases h : ι x < ι (f x) <;> simp [h, hf]
      right_inv := by
        rintro ⟨⟨x, hx⟩, b⟩
        cases b
        · simp [hx]
        · simp [hx.asymm, hf] }
  have hR : Nat.card {x : X // ι x < ι (f x)} = n := by
    have := Nat.card_congr φ
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
    omega
  refine ⟨φ.trans ((Finite.equivFinOfCardEq hR).prodCongr (Equiv.refl _)), fun x => ?_⟩
  by_cases h : ι x < ι (f x)
  · simp [φ, h, h.asymm, hf]
  · simp [φ, h, hlt x h]

private theorem exists_equiv_isAtom {α : Type*} [RelationAlgebra α] [Finite α]
    (h : IsIntegral α) {s n : ℕ} (hs : (symmetricDiversityAtoms α).ncard = s)
    (hn : (nonsymmetricDiversityAtoms α).ncard = 2 * n) :
    ∃ e : IntegralAtom (Fin s) (Fin n) ≃ {a : α // IsAtom a},
      (e .one : α) = 1 ∧ ∀ x, e x.conv = (atomStructure α).conv (e x) := by
  let eS : symmetricDiversityAtoms α ≃ Fin s := Finite.equivFinOfCardEq hs
  let f : nonsymmetricDiversityAtoms α → nonsymmetricDiversityAtoms α := fun a =>
    ⟨star a.val, isAtom_star_iff.mpr a.property.1, fun h => a.property.2 (star_injective h)⟩
  obtain ⟨eN, heN⟩ := exists_equiv_fin_prod_bool (f := f) (fun a => Subtype.ext (star_star a.val))
    (fun a h => a.property.2 (congrArg Subtype.val h)) hn
  let ψ : IntegralAtom (Fin s) (Fin n) → {a : α // IsAtom a}
    | .one => ⟨1, h⟩
    | .symm i => ⟨eS.symm i, (eS.symm i).property.1⟩
    | .nsymm i b => ⟨eN.symm (i, b), (eN.symm (i, b)).property.1⟩
  have hsurj : Function.Surjective ψ := by
    intro a
    obtain ⟨a, ha⟩ := a
    by_cases h1 : a = 1
    · exact ⟨.one, Subtype.ext h1.symm⟩
    by_cases hsym : star a = a
    · have ha' : a ∈ symmetricDiversityAtoms α :=
        ⟨ha, ha.le_compl_iff.mpr fun hle => h1 ((h.le_iff_eq ha.ne_bot).mp hle), hsym⟩
      exact ⟨.symm (eS ⟨a, ha'⟩), by simp [ψ]⟩
    · exact ⟨.nsymm (eN ⟨a, ha, hsym⟩).1 (eN ⟨a, ha, hsym⟩).2, by simp [ψ]⟩
  have hcard : Nat.card (IntegralAtom (Fin s) (Fin n)) = Nat.card {a : α // IsAtom a} := by
    have hA : Nat.card {a : α // IsAtom a} = 1 + s + 2 * n := by
      rw [← hs, ← hn]
      exact ncard_setOf_isAtom_of_isIntegral h
    rw [hA, Nat.card_congr IntegralAtom.equivOptionSum]
    simp only [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_sum, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_bool]
    omega
  refine ⟨Equiv.ofBijective ψ ((Nat.bijective_iff_surjective_and_card ψ).mpr ⟨hsurj, hcard⟩),
    rfl, ?_⟩
  rintro (_ | i | ⟨i, b⟩)
  · exact Subtype.ext (star_one α).symm
  · exact Subtype.ext (eS.symm i).property.2.2.symm
  · have := heN (eN.symm (i, b))
    rw [Equiv.apply_symm_apply] at this
    have key : (eN.symm (i, !b)).val = star (eN.symm (i, b)).val :=
      congrArg Subtype.val ((Equiv.symm_apply_eq eN).mpr this.symm)
    exact Subtype.ext key

private theorem exists_eq_ofCycles {α β : Type*} (B : AtomStructure (IntegralAtom α β))
    [LawfulAtomStructure B] (hconv : B.conv = conv) (hid : B.id = {one}) :
    B = ofCycles B.cycles := by
  apply AtomStructure.ext hconv hid
  ext c
  refine ⟨CycleClosure.of, fun (h : CycleClosure _ c) => ?_⟩
  induction h with
  | of hc => exact hc
  | id a =>
    obtain ⟨e, he, h⟩ := B.exists_id_cycle_right a
    rw [hid] at he
    exact he ▸ h
  | @left c _ ih =>
    obtain ⟨r, u, t⟩ := c
    simpa [Cycle.left, ← hconv] using B.cycle_left ih
  | @right c _ ih =>
    obtain ⟨r, u, t⟩ := c
    simpa [Cycle.right, ← hconv] using B.conv_cycles (B.cycle_left (B.conv_cycles ih))

/-- Every finite integral relation algebra has a presentation by integral cycle generators. -/
theorem exists_ofCycles_of_isIntegral {A : Type*} [RelationAlgebra A] [Finite A] {s n : ℕ}
    (hA : IsIntegral A) (hs : (symmetricDiversityAtoms A).ncard = s)
    (hn : (nonsymmetricDiversityAtoms A).ncard = 2 * n) :
    ∃ (g : Set (Cycle (Fin s) (Fin n))) (_ : LawfulAtomStructure (ofCycles g)),
      Nonempty (RelationAlgebraEquiv A (ComplexAlgebra (ofCycles g))) := by
  let _ := CompleteAtomicRelationAlgebra.ofFinite A
  obtain ⟨e, he1, heconv⟩ := exists_equiv_isAtom hA hs hn
  let B := (atomStructure A).map e.symm
  have hB : B = ofCycles B.cycles := exists_eq_ofCycles B
    (funext fun b => by simp [B, ← heconv]) <| by
      ext b
      refine ⟨fun hb => e.injective (Subtype.ext ?_), ?_⟩
      · exact ((hA.le_iff_eq (e b).property.ne_bot).mp hb).trans he1.symm
      · rintro rfl
        exact he1.le
  have f : RelationAlgebraEquiv A (ComplexAlgebra B) :=
    complexAlgebraEquiv.trans (ComplexAlgebra.mapEquiv _ e.symm)
  let P (S : AtomStructure (IntegralAtom (Fin s) (Fin n))) :=
    ∃ _ : LawfulAtomStructure S, Nonempty (RelationAlgebraEquiv A (ComplexAlgebra S))
  exact ⟨B.cycles, hB ▸ (show P B from ⟨inferInstance, ⟨f⟩⟩)⟩

namespace IsoClass

/-- The set of isomorphism classes with `s` symmetric diversity atoms and `n` pairs of nonsymmetric
atoms. This is an abbrev for the convenience of matching the usual convention without making proofs
more complicated. -/
abbrev ofSymmNsymm (s n : ℕ) : Type := Quotient (setoid (Fin s) (Fin n))

/-- The set of isomorphism classes with `k` atoms. -/
abbrev ofAtoms (k : ℕ) : Type := Σ s, Σ n : {n // 1 + s + 2 * n = k}, ofSymmNsymm s n

theorem isEmpty_ofAtoms_zero : IsEmpty (ofAtoms 0) :=
  ⟨fun ⟨_, n, _⟩ => by lia⟩

theorem card_ofAtoms_succ_eq_sum_ofSymmNsymm (k : ℕ) :
    Nat.card (ofAtoms (k + 1)) =
      ∑ n ∈ Finset.range (k / 2 + 1), Nat.card (ofSymmNsymm (k - 2 * n) n) := by
  rw [← Finset.sum_coe_sort, ← Nat.card_sigma, eq_comm]
  apply Nat.card_eq_of_bijective (fun ⟨n, q⟩ => ⟨k - 2 * n, ⟨n, by grind⟩, q⟩)
  constructor
  · rintro ⟨n, q⟩ ⟨n', q'⟩ h
    obtain rfl : n = n' := by grind
    grind
  · rintro ⟨s, ⟨n, h⟩, q⟩
    obtain rfl : s = k - 2 * n := by lia
    exact ⟨⟨⟨n, by grind⟩, q⟩, rfl⟩

/-!
### Counts of isomorphism classes

The following statements are all of the known counts of isomorphism classes of finite integral
relation algebras, by symmetric and nonsymmetric atoms as well as overall.

They will certainly be too computationally expensive to prove here, but we
provide their statements as a reference. Proofs of the `ofAtoms` statements can start with
`simp [card_ofAtoms_succ_eq_sum_ofSymmNsymm, Finset.sum_range_succ]` and then use each of
the `ofSymmNsymm` results.
-/

theorem_wanted card_ofSymmNsymm_zero_zero : Nat.card (ofSymmNsymm 0 0) = 1

theorem_wanted card_ofAtoms_one : Nat.card (ofAtoms 1) = 1 := by
  simpa [card_ofAtoms_succ_eq_sum_ofSymmNsymm] using (❰card_ofSymmNsymm_zero_zero❱)

theorem_wanted card_ofSymmNsymm_one_zero : Nat.card (ofSymmNsymm 1 0) = 2

theorem_wanted card_ofAtoms_two : Nat.card (ofAtoms 2) = 2 := by
  simpa [card_ofAtoms_succ_eq_sum_ofSymmNsymm] using (❰card_ofSymmNsymm_one_zero❱)

theorem_wanted card_ofSymmNsymm_zero_one : Nat.card (ofSymmNsymm 0 1) = 3

theorem_wanted card_ofSymmNsymm_two_zero : Nat.card (ofSymmNsymm 2 0) = 7

theorem_wanted card_ofAtoms_three : Nat.card (ofAtoms 3) = 10 := by
  simpa [card_ofAtoms_succ_eq_sum_ofSymmNsymm, Finset.sum_range_succ] using
    congr($(❰card_ofSymmNsymm_two_zero❱) + $(❰card_ofSymmNsymm_zero_one❱))

theorem_wanted card_ofSymmNsymm_one_one : Nat.card (ofSymmNsymm 1 1) = 37

theorem_wanted card_ofSymmNsymm_three_zero : Nat.card (ofSymmNsymm 3 0) = 65

theorem_wanted card_ofAtoms_four : Nat.card (ofAtoms 4) = 102 := by
  simpa [card_ofAtoms_succ_eq_sum_ofSymmNsymm, Finset.sum_range_succ] using
    congr($(❰card_ofSymmNsymm_three_zero❱) + $(❰card_ofSymmNsymm_one_one❱))

theorem_wanted card_ofSymmNsymm_zero_two : Nat.card (ofSymmNsymm 0 2) = 83

theorem_wanted card_ofSymmNsymm_two_one : Nat.card (ofSymmNsymm 2 1) = 1316

theorem_wanted card_ofSymmNsymm_four_zero : Nat.card (ofSymmNsymm 4 0) = 3013

theorem_wanted card_ofAtoms_five : Nat.card (ofAtoms 5) = 4412 := by
  simpa [card_ofAtoms_succ_eq_sum_ofSymmNsymm, Finset.sum_range_succ] using
    congr($(❰card_ofSymmNsymm_four_zero❱) + $(❰card_ofSymmNsymm_two_one❱) +
      $(❰card_ofSymmNsymm_zero_two❱))

theorem_wanted card_ofSymmNsymm_one_two : Nat.card (ofSymmNsymm 1 2) = 47965

theorem_wanted card_ofSymmNsymm_three_one : Nat.card (ofSymmNsymm 3 1) = 988464

theorem_wanted card_ofSymmNsymm_five_zero : Nat.card (ofSymmNsymm 5 0) = 3849920

theorem_wanted card_ofAtoms_six : Nat.card (ofAtoms 6) = 4886349 := by
  simpa [card_ofAtoms_succ_eq_sum_ofSymmNsymm, Finset.sum_range_succ] using
    congr($(❰card_ofSymmNsymm_five_zero❱) + $(❰card_ofSymmNsymm_three_one❱) +
      $(❰card_ofSymmNsymm_one_two❱))

theorem_wanted card_ofSymmNsymm_zero_three : Nat.card (ofSymmNsymm 0 3) = 4492953

theorem_wanted card_ofSymmNsymm_two_two : Nat.card (ofSymmNsymm 2 2) = 2186435732

theorem_wanted card_ofSymmNsymm_four_one : Nat.card (ofSymmNsymm 4 1) = 50265788140

theorem_wanted card_ofSymmNsymm_six_zero : Nat.card (ofSymmNsymm 6 0) = 292352449486

theorem_wanted card_ofAtoms_seven : Nat.card (ofAtoms 7) = 344809166311 := by
  simpa [card_ofAtoms_succ_eq_sum_ofSymmNsymm, Finset.sum_range_succ] using
    congr($(❰card_ofSymmNsymm_six_zero❱) + $(❰card_ofSymmNsymm_four_one❱) +
      $(❰card_ofSymmNsymm_two_two❱) + $(❰card_ofSymmNsymm_zero_three❱))

theorem_wanted card_ofSymmNsymm_one_three : Nat.card (ofSymmNsymm 1 3) = 52506245239168

end IsoClass

end IntegralAtom

end Cslib.RelationAlgebra
