/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Bhavik Mehta
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Data.Set.Basic
import Mathlib.Order.Closure
import Mathlib.Tactic.Cases
import Cslib.Logics.LinearLogic.CLL.Basic

/-!
# Phase semantics for Classical Linear Logic

This file develops the phase semantics for Classical Linear Logic (CLL), providing an
algebraic interpretation of linear logic propositions in terms of phase spaces.

Phase semantics is a denotational semantics for linear logic where
propositions are interpreted as subsets of a commutative monoid, and logical operations
correspond to specific set-theoretic operations.

## Main definitions

* `PhaseSpace`: A commutative monoid equipped with a distinguished subset ⊥
* `PhaseSpace.imp`: Linear implication `X ⊸ Y` between sets in a phase space
* `PhaseSpace.orthogonal`: The orthogonal `X⫠` of a set X
* `PhaseSpace.isFact`: A fact is a set that equals its biorthogonal closure
* `Fact`: The type of facts in a phase space
* `PhaseSpace.FactExpr`: Inductive type for representing operations on facts
* `PhaseSpace.interpret`: Interpretation of the connectives on facts
* `PhaseSpace.interpProp`: Interpretation of CLL propositions as facts in a phase space

## Main results

* `PhaseSpace.biorthogonalClosure`: The biorthogonal operation forms a closure operator
* `PhaseSpace.orth_iUnion`: Orthogonal of union equals intersection of orthogonals
* `PhaseSpace.sInf_isFact` and `PhaseSpace.inter_isFact_of_isFact`: Facts are closed under
  intersections
* `PhaseSpace.biorth_least_fact`: The biorthogonal closure gives the smallest fact containing a set

Several lemmas about facts and orthogonality useful in the proof of soundness are proven here.

## TODO
- Soundness theorem
- Completeness theorem

## References

* [J.-Y. Girard, *Linear logic*][Girard1987]
* [J.-Y. Girard, *Linear Logic: its syntax and semantics*][Girard1995]
-/

universe u v

namespace CLL

open Proposition
open scoped Pointwise
open Set

/--
A phase space is a commutative monoid M equipped with a distinguished subset ⊥.
This forms the algebraic foundation for interpreting linear logic propositions.
-/
class PhaseSpace (M : Type u) extends CommMonoid M where
  /-- The distinguished subset ⊥ used to define orthogonality -/
  bot : Set M

namespace PhaseSpace

variable {P : Type*} [PhaseSpace P] {p q : P}

section

-- ## Basic operations

/--
Linear implication `X ⊸ Y` in a phase space: the set of elements m such that
for all x ∈ X, we have m * x ∈ Y.
-/
def imp [PhaseSpace M] (X Y : Set M) : Set M := {m | ∀ x ∈ X, m * x ∈ Y}

@[inherit_doc] scoped infix:50 " ⊸ " => imp

/--
The orthogonal `X⫠` of a set X: the set of elements that map X into ⊥ under multiplication.
-/
def orthogonal (X : Set P) : Set P := X ⊸ bot

@[inherit_doc] scoped postfix:max "⫠" => orthogonal

-- ## Properties of orthogonality

@[grind, simp] lemma orthogonal_def (X : Set P) : X⫠ = {m | ∀ x ∈ X, m * x ∈ bot} := rfl

/--
The orthogonal operation is antitone: if X ⊆ Y then Y⫠ ⊆ X⫠.
-/
lemma orth_antitone {X Y : Set P} (hXY : X ⊆ Y) :
    Y⫠ ⊆ X⫠ := by
  intro m hm x hx
  exact hm x (hXY hx)

/--
The biorthogonal operation is extensive: X ⊆ X⫠⫠ for any set X.
-/
lemma orthogonal_extensive (X : Set P) : X ⊆ X⫠⫠ := by
  intro x hx n hn
  simpa [orthogonal, imp, Set.mem_setOf, mul_comm] using hn x hx

/--
The triple orthogonal equals the orthogonal: X⫠⫠⫠ = X⫠.
-/
lemma triple_orth (X : Set P) : X⫠⫠⫠ = X⫠ := by
  apply le_antisymm
  · intro m hm x hxX
    have hx' : x ∈ (X⫠)⫠ := by
      intro y hy
      simpa [orthogonal, imp, Set.mem_setOf, mul_comm] using hy x hxX
    exact hm x hx'
  · apply orthogonal_extensive (X := X⫠)

lemma triple_dual {G : Set P} : G⫠⫠⫠⫠ = G⫠⫠ := triple_orth G⫠
/--
The biorthogonal closure operator on sets in a phase space.
-/
def biorthogonalClosure : ClosureOperator (Set P) := {
  toFun X := X⫠⫠
  monotone' := by
    intro X Y hXY m hm n hnY
    have hnX : n ∈ X⫠ := by
      intro x hxX
      exact hnY x (hXY hxX)
    exact hm n hnX
  le_closure' := by
    intro X x hx n hn
    simpa [orthogonal, imp, Set.mem_setOf, mul_comm] using hn x hx
  idempotent' X := triple_orth X⫠
}

-- # Basic theory of phase spaces

/--
Given a phase space (P, ⊥) and a set of subsets (Gᵢ)_{i ∈ I} of P, we have that
(⋃ᵢ Gᵢ)⫠ = ⋂ᵢ Gᵢ⫠.
-/
lemma orth_iUnion {ι : Sort*} (G : ι → Set P) :
    (⋃ i, G i)⫠ = ⋂ i, (G i)⫠ := by
  ext m; constructor
  · intro hm
    have hm' : ∀ x ∈ ⋃ j, G j, m * x ∈ PhaseSpace.bot := by
      simpa [orthogonal, imp, mem_setOf] using hm
    refine mem_iInter.mpr (fun i => ?_)
    exact fun x hx => hm' x (mem_iUnion.mpr ⟨i, hx⟩)
  · intro hm x hx
    rcases mem_iUnion.mp hx with ⟨i, hix⟩
    have hmi : m ∈ (G i)⫠ := mem_iInter.mp hm i
    simpa [orthogonal, imp, mem_setOf] using hmi x hix

/--
Given a phase space (P, ⊥) and a set of subsets (Gᵢ)_{i ∈ I} of P, we have that
∩ᵢ Gᵢ⫠⫠ = (∪ᵢ Gᵢ⫠)⫠.
-/
lemma iInter_biorth_eq_orth_iUnion_orth {ι : Sort*} (G : ι → Set P) :
    (⋂ i, (G i)⫠⫠ : Set P) = (⋃ i, (G i)⫠)⫠ := by
  simpa using (orth_iUnion (G := fun i => (G i)⫠)).symm

-- ## Facts

/--
A fact is a subset of a phase space that equals its biorthogonal closure.
-/
def isFact (X : Set P) : Prop := X = X⫠⫠

/--
The type of facts in a phase space.
-/
structure Fact (P : Type*) [PhaseSpace P] where
  /-- The underlying set that is a fact -/
  (carrier : Set P)
  (property : isFact carrier)

instance : SetLike (Fact P) P where
  coe := Fact.carrier
  coe_injective' := fun p q h => by cases p; cases q; congr

instance [PhaseSpace M] : Coe (Fact M) (Set M) := ⟨Fact.carrier⟩

initialize_simps_projections Fact (carrier → coe)

@[grind, simp] lemma mem_carrier (G : Fact P) : G.carrier = (G : Set P) := rfl

@[grind] lemma subset_dual_dual (G : Set P) : G ⊆ G⫠⫠ := fun p hp q hq => mul_comm p q ▸ hq _ hp

/--
Construct a fact from a set G and a proof that its biorthogonal closure is contained in G.
-/
@[simps] def Fact.mk_subset (G : Set P) (h : G⫠⫠ ⊆ G) : Fact P where
  carrier := G
  property := by simp only [isFact]; symm; apply h.antisymm (subset_dual_dual G)

lemma dual_subset_dual {G H : Set P} (h : G ⊆ H) : H⫠ ⊆ G⫠ := fun _ hp _ hq => hp _ (h hq)

/--
Construct a fact from a set G and a proof that G equals the orthogonal of some set H.
-/
@[simps!] def Fact.mk_dual (G H : Set P) (h : G = H⫠) : Fact P :=
  Fact.mk_subset G <| by rw [h, triple_orth]

lemma coe_mk {X : Set P} {h : isFact X} :
    ((⟨X, h⟩ : Fact P) : Set P) = X := rfl

@[grind, simp] lemma closed (F : Fact P) : isFact (F : Set P) := F.property

/-- In any phase space, `{1}⫠ = ⊥`. -/
lemma orth_one_eq_bot :
    ({(1 : P)} : Set P)⫠ = (PhaseSpace.bot : Set P) := by
  ext m; constructor
  · intro hm
    simpa [orthogonal, imp, mem_setOf, mul_one] using hm 1 (by simp)
  · intro hm x hx
    rcases hx with rfl
    simpa [orthogonal, imp, mem_setOf, mul_one] using hm

/-- The fact given by the dual of G. -/
@[simps!] def dualFact (G : Set P) : Fact P := Fact.mk_dual (G⫠) G rfl

instance : One (Fact P) where one := dualFact (PhaseSpace.bot : Set P)

@[grind, simp] lemma coe_one : ((1 : Fact P) : Set P) = (PhaseSpace.bot : Set P)⫠ := rfl
@[grind, simp] lemma mem_one :
  p ∈ (1 : Fact P) ↔ (∀ q ∈ PhaseSpace.bot, p * q ∈ PhaseSpace.bot) := Iff.rfl

@[grind] lemma one_mem_one : (1 : P) ∈ (1 : Fact P) := by simp

lemma mul_mem_one (hp : p ∈ (1 : Fact P)) (hq : q ∈ (1 : Fact P)) : p * q ∈ (1 : Fact P) := by
  aesop (add simp mul_assoc)

instance : Top (Fact P) where
  top := Fact.mk_subset Set.univ <| fun _ _ => Set.mem_univ _

@[grind, simp] lemma coe_top : ((⊤ : Fact P) : Set P) = Set.univ := rfl
@[grind, simp] lemma mem_top : x ∈ (⊤ : Fact P) := Set.mem_univ _

@[grind] lemma dual_empty : (∅ : Set P)⫠ = Set.univ := by simp
@[grind, simp] lemma dualFact_empty : dualFact (∅ : Set P) = ⊤ := SetLike.coe_injective (by simp)

instance : Zero (Fact P) where zero := dualFact ⊤

@[grind, simp] lemma coe_zero : ((0 : Fact P) : Set P) = (Set.univ : Set P)⫠ := rfl
lemma mem_zero : p ∈ (0 : Fact P) ↔ ∀ q, p * q ∈ PhaseSpace.bot := by
  rw [← SetLike.mem_coe]; simp

instance : Bot (Fact P) where
  bot := Fact.mk_dual (PhaseSpace.bot : Set P) {1} (orth_one_eq_bot).symm


/-- In a phase space, `G⫠⫠` is the smallest fact containing `G`. -/
lemma biorth_least_fact (G : Set P) :
      ∀ {F : Set P}, isFact F → G ⊆ F → G⫠⫠ ⊆ F := by
  let c : ClosureOperator (Set P) := biorthogonalClosure
  have h_min :
      ∀ {F : Set P}, isFact F → G ⊆ F → G⫠⫠ ⊆ F := by
    intro F hF hGF
    have hF_closed : c.IsClosed F := by
      have : F = c F := by simpa [isFact, c] using hF
      exact (c.isClosed_iff).2 this.symm
    simpa [c] using ClosureOperator.closure_min hGF hF_closed
  apply h_min

/-- `0` is the least fact (w.r.t. inclusion). -/
lemma zero_least_fact :
    ∀ {F : Set P}, isFact F → ((∅ : Set P)⫠⫠) ⊆ F := by
  intro F hF
  have h := biorth_least_fact (G := (∅ : Set P)) (F := F) hF
              (by simp)
  simpa using h

/-- `⊤ = ∅⫠`, so `⊤` is a fact. -/
@[grind] lemma top_eq_orth_empty :
  (Set.univ : Set P) = (∅ : Set P)⫠ := by
  ext m; simp [orthogonal, imp]

lemma isFact_iff_closed (X : Set P) :
  isFact X ↔ biorthogonalClosure.IsClosed X := by
  constructor <;> (intro; simp only [isFact, biorthogonalClosure]; symm; assumption)

/--
Arbitrary intersections of facts are facts.
-/
lemma sInf_isFact {S : Set (Fact P)} :
  isFact (sInf ((fun F : Fact P => (F : Set P)) '' S)) := by
  have H' :
      ∀ X ∈ ((fun F : Fact P => (F : Set P)) '' S),
        biorthogonalClosure.IsClosed X := by
    intro X hX
    rcases hX with ⟨F, hF, rfl⟩
    exact (isFact_iff_closed (X := (F : Set P))).1 F.property
  have hclosed :
      biorthogonalClosure.IsClosed
        (sInf ((fun F : Fact P => (F : Set P)) '' S)) :=
    ClosureOperator.sInf_isClosed
      (c := biorthogonalClosure) (S := ((fun F : Fact P => (F : Set P)) '' S)) H'
  -- translate back to `isFact`
  exact (isFact_iff_closed
          (X := sInf ((fun F : Fact P => (F : Set P)) '' S))).2 hclosed

/-- Intersection of the carriers of a set of facts. -/
def carriersInf (S : Set (Fact P)) : Set P :=
  sInf ((fun F : Fact P => (F : Set P)) '' S)

lemma carriersInf_isFact {S : Set (Fact P)} : isFact (carriersInf S) := by
  unfold carriersInf
  have H' :
      ∀ X ∈ ((fun F : Fact P => (F : Set P)) '' S),
        biorthogonalClosure.IsClosed X := by
    intro X hX
    rcases hX with ⟨F, hF, rfl⟩
    exact (isFact_iff_closed (X := (F : Set P))).1 F.property
  have hclosed :
      biorthogonalClosure.IsClosed
        (sInf ((fun F : Fact P => (F : Set P)) '' S)) :=
    ClosureOperator.sInf_isClosed
      (c := biorthogonalClosure) (S := ((fun F : Fact P => (F : Set P)) '' S)) H'
  exact (isFact_iff_closed
          (X := sInf ((fun F : Fact P => (F : Set P)) '' S))).2 hclosed

/--
Binary intersections of facts are facts.
-/
lemma inter_isFact_of_isFact {A B : Set P}
    (hA : isFact A) (hB : isFact B) : isFact (A ∩ B) := by
  let FA : Fact P := ⟨A, hA⟩
  let FB : Fact P := ⟨B, hB⟩
  have h := carriersInf_isFact (S := ({FA, FB} : Set (Fact P)))
  simpa [carriersInf, Set.image_pair, sInf_insert, sInf_singleton, inf_eq_inter]
    using h

instance : InfSet (Fact P) where
  sInf S := ⟨carriersInf S, carriersInf_isFact (S := S)⟩

omit [PhaseSpace P] in
@[grind, simp]
lemma iInter_eq_sInf_image {α} (S : Set α) (f : α → Set P) :
  (⋂ x ∈ S, f x) = sInf (f '' S) := by
  ext x; constructor
  · intro hx; aesop
  · intro hx; aesop

@[grind, simp]
lemma inter_eq_orth_union_orth (G H : Fact P) :
  ((G : Set P) ∩ (H : Set P) : Set P) =
    (((G : Set P)⫠) ∪ ((H : Set P)⫠) : Set P)⫠ := by
  ext m; constructor
  · intro hm y hy
    rcases hy with hyG | hyH
    · have : y * m ∈ PhaseSpace.bot := hyG m hm.left
      simpa [mul_comm] using this
    · have : y * m ∈ PhaseSpace.bot := hyH m hm.right
      simpa [mul_comm] using this
  · intro hm
    have hmGbi : m ∈ ((G : Set P)⫠⫠) := by
      intro y hy
      exact hm y (Or.inl hy)
    have hmHbi : m ∈ ((H : Set P)⫠⫠) := by
      intro y hy
      exact hm y (Or.inr hy)
    have hGeq : (G : Set P) = (G : Set P)⫠⫠ := G.property
    have hHeq : (H : Set P) = (H : Set P)⫠⫠ := H.property
    have hmG : m ∈ (G : Set P) := by rw [hGeq]; exact hmGbi
    have hmH : m ∈ (H : Set P) := by rw [hHeq]; exact hmHbi
    exact ⟨hmG, hmH⟩

instance : Min (Fact P) where
  min G H :=
    Fact.mk_dual (G ∩ H) (G⫠ ∪ H⫠) <| by simp

/--
The idempotent elements within a given set X.
-/
def idempotentsIn [Monoid M] (X : Set M) : Set M := {m | IsIdempotentElem m ∧ m ∈ X}

/--
The set I of idempotents that "belong to 1" in the phase semantics.
-/
def I : Set P := idempotentsIn (1 : Set P)

-- ## Interpretation of the connectives

namespace Fact

/--
The tensor product `X ⊗ Y` of two facts,
defined as the dual of the orthogonal of the pointwise product.
-/
def tensor (X Y : Fact P) : Fact P := dualFact (X * Y)⫠
@[inherit_doc] scoped infix:35 " ⊗ " => tensor
/--
The par (multiplicative disjunction) `X ⅋ Y` of two facts,
defined as the dual of the pointwise product of the orthogonals.
-/
def parr (X Y : Fact P) : Fact P := dualFact ((X⫠) * (Y⫠))
@[inherit_doc] scoped infix:35 " ⅋ " => parr
/--
The with (additive conjunction) `X & Y` of two facts,
defined as the intersection of the two facts.
-/
def withh (X Y : Fact P) : Fact P := X ⊓ Y
@[inherit_doc] scoped infix:30 " & " => withh
/--
The oplus (additive disjunction) `X ⊕ Y` of two facts,
defined as the dual of the orthogonal of the union.
-/
def oplus (X Y : Fact P) : Fact P := dualFact (X ∪ Y)⫠
@[inherit_doc] scoped infix:35 " ⊕ " => oplus
/--
The exponential `!X` (of course) of a fact,
defined as the dual of the orthogonal of the intersection with the idempotents.
-/
def bang (X : Fact P) : Fact P := dualFact (X ∩ I)⫠
@[inherit_doc] scoped prefix:95 " ! " => bang
/--
The exponential `?X` (why not) of a fact,
defined as the dual of the intersection of the orthogonal with the idempotents.
-/
def quest (X : Fact P) : Fact P := dualFact (X⫠ ∩ I)
@[inherit_doc] scoped prefix:95 " ʔ " => quest
/--
Linear implication between facts,
defined as the dual of the orthogonal of the pointwise product.
-/
def linImpl (X Y : Fact P) : Fact P := dualFact ((X : Set P) * (Y : Set P)⫠)
@[inherit_doc] scoped infix:25 " ⊸ " => linImpl

end Fact

open Fact

-- ## Interpretation of propositions

/--
The interpretation of a CLL proposition in a phase space, given a valuation of atoms to facts.
-/
def interpProp [PhaseSpace M] (v : Atom → Fact M) : Proposition Atom → Fact M
  | .atom a       => v a
  | .atomDual a   => Fact.mk_dual (v a)⫠ (v a) rfl
  | .one          => 1
  | .zero         => 0
  | .top          => ⊤
  | .bot          => ⊥
  | .tensor A B   => (interpProp v A) ⊗ (interpProp v B)
  | .parr   A B   => (interpProp v A) ⅋ (interpProp v B)
  | .with   A B   => (interpProp v A) & (interpProp v B)
  | .oplus  A B   => (interpProp v A) ⊕ (interpProp v B)
  | .bang   A     => !(interpProp v A)
  | .quest  A     => ʔ(interpProp v A)

@[inherit_doc] scoped notation:max "⟦" P "⟧" v:90 => interpProp v P

end

end PhaseSpace

end CLL
