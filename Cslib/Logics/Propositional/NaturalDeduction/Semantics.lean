/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
import Cslib.Logics.Propositional.NaturalDeduction.Lemmas
import Mathlib.Order.Heyting.Regular
import Mathlib.Data.Finset.Lattice.Fold


/-! # Heyting algebra semantics -/

namespace PL

namespace NJ

open Proposition Theory Theory.Derivation

variable {Atom : Type _} [DecidableEq Atom] {T : Theory Atom}

def Valuation (Atom : Type _) (H : Type _) := Atom → H

/-- Extend a valuation to propositions using the Heyting algebra operations. -/
def Valuation.pInterpret {H : Type _} [GeneralizedHeytingAlgebra H] (v : Valuation Atom H) :
    Proposition Atom → H
  | atom x => v x
  | conj A B => (v.pInterpret A) ⊓ (v.pInterpret B)
  | disj A B => (v.pInterpret A) ⊔ (v.pInterpret B)
  | impl A B => (v.pInterpret A) ⇨ (v.pInterpret B)

/-- TODO: this coercion doesn't work without explicit type annotation eg:
(↑v : Proposition Atom → H) A because lean defaults to v : Atom → H. There should be some way to
override this especially since v x = ↑v (atom x). -/
instance {H : Type _} [GeneralizedHeytingAlgebra H] :
    CoeFun (Valuation Atom H) (fun _ => Proposition Atom → H) where
  coe := Valuation.pInterpret

/-- Extend a valuation to contexts using conjunction. -/
def Valuation.ctxInterpret {H : Type _} [GeneralizedHeytingAlgebra H] (v : Valuation Atom H)
    (Γ : Ctx Atom) : H := Γ.inf (v.pInterpret)

@[inherit_doc]
scoped notation v "⟦" A "⟧" => Valuation.pInterpret v A

@[inherit_doc]
scoped notation v "⟦" Γ "⟧" => Valuation.ctxInterpret v Γ

open Valuation

variable {H : Type _} [iH : GeneralizedHeytingAlgebra H] (v : Valuation Atom H)

/-- A valuation models a proposition if its interpretation is the top element. -/
@[reducible]
def Valuation.PValid (A : Proposition Atom) : Prop := v⟦A⟧ = ⊤

/-- A valuation models a sequent if the interpretation of the context is ≤ the interpretation of
the conclusion. -/
@[reducible]
def Valuation.SValid (S : Sequent Atom) : Prop := v⟦S.1⟧ ≤ v⟦S.2⟧

/-- A valuation models a theory if it models every axiom. -/
@[reducible]
def Valuation.TValid (T : Theory Atom) : Prop := ∀ A ∈ T, v.PValid A

@[inherit_doc]
scoped notation v' " ⊨ " A => Valuation.PValid v' A

@[inherit_doc]
scoped notation v' " ⊨ " S => Valuation.SValid v' S

@[inherit_doc]
scoped notation v' " ⊨ " T => Valuation.TValid v' T

omit [DecidableEq Atom] in
theorem Valuation.MPL_valid : v ⊨ MPL := by grind

omit [DecidableEq Atom] in
theorem Valuation.IPL_valid_of_heytingAlgebra [Bot Atom] {H' : Type _} [HeytingAlgebra H']
    {v : Valuation Atom H'} :
    v ⊥ = ⊥ → v ⊨ IPL := by
  intro hv A hA
  rw [Set.mem_range] at hA
  replace ⟨A', hA⟩ := hA
  simp_rw [←hA, PValid, pInterpret, hv]
  exact bot_himp _

omit [DecidableEq Atom] in
theorem Valuation.CPL_valid_of_booleanAlgebra [Bot Atom] {H' : Type _} [BooleanAlgebra H']
    {v : Valuation Atom H'} :
    v ⊥ = ⊥ → v ⊨ CPL := by
  intro hv A hA
  cases hA
  case inl hA =>
    rw [Set.mem_range] at hA
    replace ⟨A', hA⟩ := hA
    simp [←hA, PValid, pInterpret, hv]
  case inr hA =>
    rw [Set.mem_range] at hA
    replace ⟨A', hA⟩ := hA
    simp [←hA, PValid, pInterpret, hv]


/-! ### Soundness

A derivable sequent is valid in every Heyting algebra.
-/

theorem Theory.sound_of_derivation {Γ : Ctx Atom} {B : Proposition Atom} :
    T.Derivation ⟨Γ, B⟩ → ∀ (v : Valuation Atom H), (v ⊨ T) → v ⊨ ⟨Γ, B⟩
  | Theory.Derivation.ax hB, v, _ => by have : v⟦Γ⟧ ≤ ⊤ := iH.le_top _; grind
  | Theory.Derivation.ass hB, _, _ => Finset.inf_le hB
  | Theory.Derivation.conjI D E, v, hT =>
    iH.le_inf _ _ _ (sound_of_derivation D v hT) (sound_of_derivation E v hT)
  | Theory.Derivation.conjE₁ D, v, hT =>
    iH.le_trans _ _ _ (sound_of_derivation D v hT) (iH.inf_le_left _ _)
  | Theory.Derivation.conjE₂ D, v, hT =>
    iH.le_trans _ _ _ (sound_of_derivation D v hT) (iH.inf_le_right _ _)
  | Theory.Derivation.disjI₁ D, v, hT =>
    iH.le_trans _ _ _ (sound_of_derivation D v hT) (iH.le_sup_left _ _)
  | Theory.Derivation.disjI₂ D, v, hT =>
    iH.le_trans _ _ _ (sound_of_derivation D v hT) (iH.le_sup_right _ _)
  | @Theory.Derivation.disjE _ _ _ Γ A B C D E E', v, hT => by
    change v⟦Γ⟧ ≤ v⟦C⟧
    trans v⟦insert A Γ⟧ ⊔ v⟦insert B Γ⟧
    · simp_rw [Valuation.ctxInterpret, Finset.inf_insert, ←inf_sup_right]
      apply iH.le_inf
      · exact sound_of_derivation D v hT
      · rfl
    · exact iH.sup_le _ _ _ (sound_of_derivation E v hT) (sound_of_derivation E' v hT)
  | @Theory.Derivation.implI _ _ _ A B _ D, v, hT => by
    refine (iH.le_himp_iff _ _ _).mpr ?_
    have : v⟦insert A Γ⟧ ≤ v⟦B⟧ := sound_of_derivation D v hT
    rwa [Valuation.ctxInterpret, Finset.inf_insert, inf_comm] at this
  | @Theory.Derivation.implE _ _ _ _ A B D E, v, hT => by
    change v⟦Γ⟧ ≤ v⟦B⟧
    trans (v⟦A⟧ ⇨ v⟦B⟧) ⊓ v⟦A⟧
    · exact iH.le_inf _ _ _ (sound_of_derivation D v hT) (sound_of_derivation E v hT)
    · exact himp_inf_le

/-- A derivable sequent is valid for every valuation. -/
protected theorem Theory.sound {Γ : Ctx Atom} {B : Proposition Atom} :
    Γ ⊢[T] B → ∀ (v : Valuation Atom H), (v ⊨ T) → v ⊨ ⟨Γ, B⟩
  | ⟨D⟩ => sound_of_derivation D

/-! ### Completeness

A sequent is derivable if it valid in every Heyting algebra. In fact, for a sequent ⟨Γ, A⟩, the
result follows from validity in the Heyting algebra `Proposition Atom` modulo the relation
`≡[T ∪ Γ]`.
-/

def Theory.propQuotient (T : Theory Atom) := Quotient T.propositionSetoid

instance Theory.propPO : PartialOrder <| Theory.propQuotient T where
  le := Quotient.lift₂ (f := fun A B => {A} ⊢[T] B) (by
    simp_rw [eq_iff_iff]
    exact Theory.le_wd
  )
  le_refl := by
    apply Quotient.ind
    intro A
    simp_rw [Quotient.lift_mk]
    exact Theory.le_refl
  le_trans := by
    apply Quotient.ind₂
    intro A B
    apply Quotient.ind
    intro C
    simp_rw [Quotient.lift_mk]
    exact Theory.le_trans
  le_antisymm := by
    apply Quotient.ind₂
    intro A B
    simp_rw [Quotient.lift_mk, Theory.propositionSetoid, propQuotient, Quotient.eq]
    exact Theory.le_antisymm

instance Theory.propLattice : Lattice <| Theory.propQuotient T where
  inf := Quotient.lift₂ (f := fun A B => ⟦A ⋏ B⟧) (by
    simp only [Quotient.eq, Theory.propositionSetoid, propQuotient]
    exact Theory.inf_wd
  )
  sup := Quotient.lift₂ (f := fun A B => ⟦A ⋎ B⟧) (by
    simp only [Quotient.eq, Theory.propositionSetoid, propQuotient]
    exact Theory.sup_wd
  )
  inf_le_left := by
    apply Quotient.ind₂
    simp only [Quotient.lift_mk, LE.le]
    intro _ _
    exact Theory.inf_le_left
  inf_le_right := by
    apply Quotient.ind₂
    simp only [Quotient.lift_mk, LE.le]
    intro _ _
    exact Theory.inf_le_right
  le_inf := by
    apply Quotient.ind₂
    intro _ _
    apply Quotient.ind
    intro _
    simp only [Quotient.lift_mk, LE.le]
    exact Theory.le_inf
  le_sup_left := by
    apply Quotient.ind₂
    simp only [Quotient.lift_mk, LE.le]
    intro _ _
    exact Theory.le_sup_left
  le_sup_right := by
    apply Quotient.ind₂
    simp only [Quotient.lift_mk, LE.le]
    intro _ _
    exact Theory.le_sup_right
  sup_le := by
    apply Quotient.ind₂
    intro _ _
    apply Quotient.ind
    intro _
    simp only [Quotient.lift_mk, LE.le]
    exact Theory.sup_le

instance Theory.propGeneralizedHeyting [Inhabited Atom] :
    GeneralizedHeytingAlgebra <| Theory.propQuotient T where
  top := ⟦⊤⟧
  le_top := by
    apply Quotient.ind
    simp only [Quotient.lift_mk, LE.le]
    intro _
    exact Theory.le_top
  himp := Quotient.lift₂ (f := fun A B => ⟦A ⟶ B⟧) (by
    simp only [Theory.propositionSetoid, propQuotient, Quotient.eq]
    exact Theory.himp_wd
  )
  le_himp_iff := by
    apply Quotient.ind₂
    intro _ _
    apply Quotient.ind
    intro _
    simp only [Quotient.lift₂_mk, LE.le, min, Lattice.inf]
    exact Theory.le_himp_iff

instance Theory.propHeyting [Bot Atom] [IsIntuitionistic T] :
    HeytingAlgebra <| Theory.propQuotient T where
  bot := ⟦⊥⟧
  bot_le := by
    apply Quotient.ind
    simp only [Quotient.lift_mk, LE.le]
    intro _
    exact Theory.bot_le
  compl := Quotient.lift (f := fun A => ⟦~A⟧) (by
    simp only [Theory.propositionSetoid, propQuotient, Quotient.eq]
    exact Theory.compl_wd
  )
  himp_bot := by
    apply Quotient.ind
    simp [himp]

instance Theory.propBoolean [Bot Atom] [IsClassical T] :
    BooleanAlgebra <| Theory.propQuotient T := by
  apply BooleanAlgebra.ofRegular
  apply Quotient.ind
  intro _
  unfold Heyting.IsRegular
  simp_rw [compl_sup, inf_compl_self, compl_bot, Top.top, propQuotient, max, SemilatticeSup.sup,
    compl, Quotient.lift_mk, Quotient.eq, Theory.propositionSetoid]
  exact equivalent_comm <| (Theory.pDerivable_iff_equiv_top _).mp lem

def Theory.canonicalV (T : Theory Atom) : (Valuation Atom <| Theory.propQuotient T) :=
  fun x => ⟦atom x⟧

theorem canonicalV_spec [Inhabited Atom] (A : Proposition Atom) :
    (canonicalV T).pInterpret A = ⟦A⟧ := by
  induction A with
  | atom _ => simp! [Theory.canonicalV]
  | conj _ _ ihA ihB => simp! [min, SemilatticeInf.inf, Lattice.inf, ihA, ihB]
  | disj _ _ ihA ihB => simp! [max, SemilatticeSup.sup, ihA, ihB]
  | impl _ _ ihA ihB => simp! [himp, ihA, ihB]

theorem Theory.prop_complete [Inhabited Atom] (A : Proposition Atom) (h : (canonicalV T) ⊨ A) :
    ⊢[T] A := by
  simp_rw [Valuation.PValid, canonicalV_spec, Top.top, Theory.propQuotient, Quotient.eq] at h
  have : A ≡[T] ⊤ := by simpa
  exact (Theory.pDerivable_iff_equiv_top A).mpr this

protected theorem Theory.complete.{u} {Atom : Type u} [DecidableEq Atom] [Inhabited Atom]
    {T : Theory Atom} (Γ : Ctx Atom) (A : Proposition Atom)
    (h : ∀ (H : Type u) [GeneralizedHeytingAlgebra H] (v : Valuation Atom H), v ⊨ ⟨Γ, A⟩) :
    Γ ⊢[T] A := by
  let H := Theory.propQuotient (T ∪ Γ)
  suffices (canonicalV (T ∪ Γ))⟦A⟧ = ⊤ by
    simp_rw [canonicalV_spec, Top.top, Theory.propQuotient, Quotient.eq] at this
    have : A ≡[T ∪ Γ] ⊤ := by simpa
    rw [show Γ = ∅ ∪ Γ by grind, Theory.SDerivable.iff_sDerivable_extension]
    exact (Theory.pDerivable_iff_equiv_top A).mpr this
  rw [eq_top_iff]
  trans (canonicalV (T ∪ Γ))⟦Γ⟧
  · apply Finset.le_inf
    intro A hA
    simp_rw [canonicalV_spec, LE.le, Top.top, Quotient.lift_mk]
    exact ⟨Theory.Derivation.ax <| by grind⟩
  · exact h H (canonicalV (T ∪ Γ))

/-! ### Consistency results -/

theorem consistent_of_nontrivial_model {H : Type _} [GeneralizedHeytingAlgebra H]
    (v : Valuation Atom H) (A : Proposition Atom) (hT : v ⊨ T) (hA : v⟦A⟧ ≠ ⊤) : Consistent T := by
  intro hc
  replace hc : v⟦∅⟧ ≤ v⟦A⟧ := (Theory.sound (H := H) <| hc A) v hT
  simp_rw [Valuation.ctxInterpret, Finset.inf_empty, top_le_iff] at hc
  exact hA hc

theorem MPL_consistent [Inhabited Atom] : Consistent (Atom := Atom) MPL := by
  let v : Valuation Atom Prop := fun _ => False
  apply consistent_of_nontrivial_model v (atom default) v.MPL_valid
  simp [Valuation.pInterpret, v]

theorem IPL_consistent [Bot Atom] : Consistent (Atom := Atom) IPL := by
  let v : Valuation Atom Prop := fun _ => False
  apply consistent_of_nontrivial_model v (atom default)
  · exact v.IPL_valid_of_heytingAlgebra rfl
  · simp [Valuation.pInterpret, v]

theorem CPL_consistent [Bot Atom] : Consistent (Atom := Atom) CPL := by
  let v : Valuation Atom Prop := fun _ => False
  apply consistent_of_nontrivial_model v (atom default)
  · exact v.CPL_valid_of_booleanAlgebra rfl
  · simp [Valuation.pInterpret, v]

end NJ

end PL
