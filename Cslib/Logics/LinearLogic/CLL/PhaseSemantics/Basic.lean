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
def orthogonal [PhaseSpace M] (X : Set M) : Set M := X ⊸ bot

@[inherit_doc] scoped postfix:max "⫠" => orthogonal

-- ## Properties of orthogonality

@[simp] lemma orthogonal_def [PhaseSpace M] (X : Set M) : X⫠ = {m | ∀ x ∈ X, m * x ∈ bot} := rfl

/--
The orthogonal operation is antitone: if X ⊆ Y then Y⫠ ⊆ X⫠.
-/
lemma orth_antitone [PhaseSpace M] {X Y : Set M} (hXY : X ⊆ Y) :
    Y⫠ ⊆ X⫠ := by
  intro m hm x hx
  exact hm x (hXY hx)

/--
The biorthogonal operation is extensive: X ⊆ X⫠⫠ for any set X.
-/
lemma orthogonal_extensive [PhaseSpace M] (X : Set M) : X ⊆ X⫠⫠ := by
  intro x hx n hn
  simpa [orthogonal, imp, Set.mem_setOf, mul_comm] using hn x hx

/--
The triple orthogonal equals the orthogonal: X⫠⫠⫠ = X⫠.
-/
lemma triple_orth [PhaseSpace M] (X : Set M) : X⫠⫠⫠ = X⫠ := by
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
def biorthogonalClosure [PhaseSpace M] : ClosureOperator (Set M) := {
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
lemma orth_iUnion [PhaseSpace M] {ι : Sort*} (G : ι → Set M) :
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
lemma iInter_biorth_eq_orth_iUnion_orth [PhaseSpace M] {ι : Sort*} (G : ι → Set M) :
    (⋂ i, (G i)⫠⫠ : Set M) = (⋃ i, (G i)⫠)⫠ := by
  simpa using (orth_iUnion (M := M) (G := fun i => (G i)⫠)).symm

-- ## Facts

/--
A fact is a subset of a phase space that equals its biorthogonal closure.
-/
def isFact [PhaseSpace M] (X : Set M) : Prop := X = X⫠⫠

/--
The type of facts in a phase space.
-/
structure Fact (P : Type*) [PhaseSpace P] where
  (carrier : Set P)
  (property : isFact carrier)

instance : SetLike (Fact P) P where
  coe := Fact.carrier
  coe_injective' := fun p q h => by cases p; cases q; congr

instance [PhaseSpace M] : Coe (Fact M) (Set M) := ⟨Fact.carrier⟩

initialize_simps_projections Fact (carrier → coe)

@[simp] lemma mem_carrier (G : Fact P) : G.carrier = (G : Set P) := rfl

lemma subset_dual_dual (G : Set P) : G ⊆ G⫠⫠ := fun p hp q hq => mul_comm p q ▸ hq _ hp

@[simps] def Fact.mk_subset (G : Set P) (h : G⫠⫠ ⊆ G) : Fact P where
  carrier := G
  property := by simp only [isFact]; symm; apply h.antisymm (subset_dual_dual G)

lemma dual_subset_dual {G H : Set P} (h : G ⊆ H) : H⫠ ⊆ G⫠ := fun _ hp _ hq => hp _ (h hq)

@[simps!] def Fact.mk_dual (G H : Set P) (h : G = H⫠) : Fact P :=
  Fact.mk_subset G <| by rw [h, triple_orth]

lemma coe_mk {X : Set P} {h : isFact X} :
    ((⟨X, h⟩ : Fact P) : Set P) = X := rfl

@[simp] lemma closed (F : Fact P) : isFact (F : Set P) := F.property

@[simp] lemma top_isFact :
    isFact (univ : Set P) := by
  rw [isFact]; symm
  simpa only [top_eq_univ]
    using ClosureOperator.closure_top (CLL.PhaseSpace.biorthogonalClosure (M:=P))

/-- In any phase space, `{1}⫠ = ⊥`. -/
lemma orth_one_eq_bot :
    ({(1 : P)} : Set P)⫠ = (PhaseSpace.bot : Set P) := by
  ext m; constructor
  · intro hm
    simpa [orthogonal, imp, mem_setOf, mul_one] using hm 1 (by simp)
  · intro hm x hx
    rcases hx with rfl
    simpa [orthogonal, imp, mem_setOf, mul_one] using hm

/-- `0 := ⊤⫠` is a fact and is the smallest fact. -/
@[simp] lemma zero_isFact : isFact ((∅ : Set P)⫠⫠) := by
  simp only [isFact, triple_orth]

/--
A set is a fact if and only if it is the orthogonal of some set
-/
lemma fact_iff_exists_orth (X : Set P) :
    isFact X ↔ ∃ Y : Set P, X = Y⫠ := by
  constructor
  · intro hX
    refine ⟨X⫠, ?_⟩
    exact hX
  · rintro ⟨Y, rfl⟩
    simp only [isFact, triple_orth (X := Y)]

/-- The fact given by the dual of G. -/
@[simps!] def dualFact (G : Set P) : Fact P := Fact.mk_dual (G⫠) G rfl

/-- `⊥` is a fact. -/
@[simp] lemma bot_isFact : isFact (PhaseSpace.bot : Set P) := by
  refine (fact_iff_exists_orth (X := (PhaseSpace.bot : Set P))).2 ?_
  exact ⟨{(1 : P)}, (orth_one_eq_bot).symm⟩

/--
The interpretation of the multiplicative unit 1: the biorthogonal closure of {1}.
-/
def oneSet [PhaseSpace P] : Set P := ({1} : Set P)⫠⫠

@[simp] lemma oneSet_isFact : isFact (oneSet : Set P) := by
  simp only [oneSet, isFact, triple_orth]

/--
The dual of oneSet is a fact.
-/
lemma oneSet_dual_isFact : isFact (oneSet⫠ : Set P) := by
  simp only [oneSet, isFact, triple_orth]

/--
If Y is a fact, then X ⊸ Y is also a fact
-/
lemma imp_isFact_of_fact (X Y : Set P) (hY : isFact Y) :
    isFact (X ⊸ Y) := by
  have hXY : (X ⊸ Y) = (X * Y⫠)⫠ := by
    ext m
    constructor
    · intro hm z hz
      rcases hz with ⟨x, hxX, y, hyYperp, rfl⟩
      have hmx : m * x ∈ Y := hm x hxX
      have : y * (m * x) ∈ bot := hyYperp (m * x) (by simpa using hmx)
      simpa [mul_left_comm, mul_comm, mul_assoc] using this
    · intro hm x hxX
      have hxYbi : m * x ∈ Y⫠⫠ := by
        intro y hy
        have : m * (x * y) ∈ bot := hm (x * y) ⟨x, hxX, y, hy, rfl⟩
        simpa [mul_assoc, mul_left_comm, mul_comm] using this
      rw [hY]; exact hxYbi
  simp only [isFact, hXY, triple_orth]

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
@[simp] lemma top_eq_orth_empty :
  (Set.univ : Set P) = (∅ : Set P)⫠ := by
  ext m; simp [orthogonal, imp]

/--
Linear implication between a set and a fact, yielding a fact.
-/
def Fact.imp (X : Set P) (Y : Fact P) : Fact P :=
  ⟨ X ⊸ Y, imp_isFact_of_fact X Y Y.property ⟩

lemma isFact_iff_closed (X : Set P) :
  isFact X ↔ biorthogonalClosure.IsClosed X := by
  constructor <;> (intro; simp only [isFact, biorthogonalClosure]; symm; assumption)

/--
Arbitrary intersections of facts are facts.
-/
lemma sInf_isFact {S : Set (Set P)}
    (H : ∀ X ∈ S, isFact X) : isFact (sInf S) := by
  have H' : ∀ X ∈ S, biorthogonalClosure.IsClosed X :=
    fun X hX => (isFact_iff_closed (X := X)).1 (H X hX)
  have : biorthogonalClosure.IsClosed (sInf S) :=
    ClosureOperator.sInf_isClosed (c := biorthogonalClosure) (S := S) H'
  exact (isFact_iff_closed (X := sInf S)).2 this

/--
Binary intersections of facts are facts.
-/
lemma inter_isFact_of_isFact {A B : Set P}
    (hA : isFact A) (hB : isFact B) : isFact (A ∩ B) := by
  have : isFact (sInf ({A,B} : Set (Set P))) := sInf_isFact (by
    intro X hX; rcases hX with rfl | rfl | _; simp [hA]; simp [hB])
  simpa [sInf_insert, sInf_singleton, inf_eq_inter] using this

-- instance : InfSet (Fact P) where
--   sInf S := @sInf_isFact P _ S

-- @[simp] lemma coe_sInf {S : Set (Fact P)} : ((sInf S : Fact P) : Set P) = ⋂ i ∈ S, i := rfl

-- instance : Min (Fact P) where
--   min G H := Fact.mk_dual (G ∩ H) (dual G ∪ dual H) <| by simp


/-- `𝟭 := {1}⫠⫠ = ⊥⫠` -/
lemma oneSet_eq_bot_orth :
    (oneSet : Set P) = (PhaseSpace.bot : Set P)⫠ := by
  simp only [oneSet, orth_one_eq_bot]

/-- for any fact `G`, we have `𝟭 · G = G` -/
lemma one_mul_fact_set (G : Fact P) :
    (oneSet : Set P) * (G : Set P) = (G : Set P) := by
  apply le_antisymm
  · intro z hz
    rcases hz with ⟨a, ha, q, hq, rfl⟩
    have : a * q ∈ ((G : Set P)⫠⫠) := by
      intro y hy
      have hyq : y * q ∈ (PhaseSpace.bot : Set P) := by
        simpa [orthogonal, imp, Set.mem_setOf] using hy q hq
      have ha' : a ∈ (PhaseSpace.bot : Set P)⫠ := by
        simpa [oneSet_eq_bot_orth] using ha
      have : a * (y * q) ∈ PhaseSpace.bot := ha' _ hyq
      simpa [mul_left_comm, mul_comm, mul_assoc] using this
    have h : isFact (G : Set P) := G.property
    rw [h]; exact this
  · intro g hg
    have h1 : (1 : P) ∈ (oneSet : Set P) := by
      have : (1 : P) ∈ ({(1 : P)} : Set P) := by simp
      exact orthogonal_extensive _ this
    exact ⟨1, h1, g, hg, by simp⟩

/--
The idempotent elements within a given set X.
-/
def idempotentsIn [Monoid M] (X : Set M) : Set M := {m | IsIdempotentElem m ∧ m ∈ X}

/--
The set I of idempotents that "belong to 1" in the phase semantics.
-/
def I [PhaseSpace M] : Set M := idempotentsIn (oneSet : Set M)

-- ## Interpretation of the connectives

inductive const where
| one | zero | top | bot

inductive unop where
| bang | quest

inductive binop where
| tensor | parr | with | oplus

inductive FactExpr where
| const (c : const) : FactExpr
| unop (u : unop) (X : Fact P) : FactExpr
| binop (b : binop) (X Y : Fact P) : FactExpr

def constInterpret (c : const) : Fact P :=
match c with
| .one => ⟨oneSet, oneSet_isFact⟩
| .zero => ⟨(∅ : Set P)⫠⫠, zero_isFact⟩
| .top => ⟨(Set.univ : Set P), top_isFact⟩
| .bot => ⟨oneSet⫠, oneSet_dual_isFact⟩

def unopInterpret (u : unop) (X : Fact P) : Fact P := match u with
| .bang => dualFact (X ∩ I)⫠
| .quest => dualFact (X⫠ ∩ I)

def binopInterpret (b : binop) (X Y : Fact P) : Fact P := match b with
| .tensor => dualFact (X * Y)⫠
| .parr => dualFact ((X⫠) * (Y⫠))
| .with => sorry
| .oplus => dualFact (X ∪ Y)⫠

def interpret (c : @FactExpr P _) : Fact P := match c with
| .const c => constInterpret c
| .unop u X => unopInterpret u X
| .binop b X Y => binopInterpret b X Y

-- ## Interpretation of propositions

/--
The interpretation of a CLL proposition in a phase space, given a valuation of atoms to facts.
-/
def interpProp [PhaseSpace M] (v : Atom → Fact M) : Proposition Atom → Fact M
  | .atom a       => v a
  | .atomDual a   => ⟨(v a)⫠, by rw [fact_iff_exists_orth]; use (v a)⟩
  | .one          => interpret (.const .one)
  | .zero         => interpret (.const .zero)
  | .top          => interpret (.const .top)
  | .bot          => interpret (.const .bot)
  | .tensor A B   => interpret (.binop .tensor (interpProp v A) (interpProp v B))
  | .parr   A B   => interpret (.binop .parr   (interpProp v A) (interpProp v B))
  | .with   A B   => interpret (.binop .with   (interpProp v A) (interpProp v B))
  | .oplus  A B   => interpret (.binop .oplus  (interpProp v A) (interpProp v B))
  | .bang   A     => interpret (.unop  .bang   (interpProp v A))
  | .quest  A     => interpret (.unop  .quest  (interpProp v A))

@[inherit_doc] scoped notation:max "⟦" P "⟧" v:90 => interpProp v P
