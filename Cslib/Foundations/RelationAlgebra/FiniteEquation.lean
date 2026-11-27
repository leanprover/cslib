/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Language
public import Cslib.Foundations.RelationAlgebra.Representation
public import Cslib.Foundations.RelationAlgebra.WitnessNetwork
public import Mathlib.ModelTheory.Semantics

/-!
# Finite witness bounds for relation-algebra equations

An equation failing at every finite witness bound would fail for concrete relations on the
natural numbers. To construct those relations, take an ultrafilter limit of finite labelled
networks. Only products occurring in the equation need witnesses. Their scheduled witnesses
lie in a fixed finite set of vertices, so existence of a witness passes to the limit.

This gives the finite-equation implication used in Maddux, *Finite integral relation algebras*,
Theorems 13–15, specialized to symmetric tables.
-/

@[expose] public section

namespace Cslib.RelationAlgebra

open FirstOrder.Language FirstOrder.RelationAlgebra

/-- A pair of relation-algebra terms with variables in `α`, asserted to be equal. -/
abbrev Equation (α : Type*) := relationAlgebra.Term α × relationAlgebra.Term α

variable {α : Type*}

/-- An algebra satisfies an equation if the terms agree at every assignment. -/
def Equation.Holds (e : Equation α) (A : Type*) [RelationAlgebra A] : Prop :=
  letI := compatibleRelationAlgebraOfRelationAlgebra A
  ∀ v : α → A, e.1.realize v = e.2.realize v

/-- An equation valid in every representable relation algebra, including infinite ones. -/
def Equation.ValidInRRA (e : Equation α) : Prop :=
  ∀ (A : Type*) [RelationAlgebra A], Representable A → e.Holds A

/-- Equations valid in the codomain of an embedding also hold in its domain. -/
theorem Equation.holds_of_injective {A B : Type*} [RelationAlgebra A] [RelationAlgebra B]
    (e : Equation α) (f : RelationAlgebraHom A B) (hf : Function.Injective f) (h : e.Holds B) :
    e.Holds A := by
  let _ := compatibleRelationAlgebraOfRelationAlgebra A
  let _ := compatibleRelationAlgebraOfRelationAlgebra B
  intro v
  apply hf
  simpa only [HomClass.realize_term] using h (f ∘ v)

namespace Equation

open Filter SymmetricCycles

universe u

private abbrev value {A : Type*} [RelationAlgebra A] (v : α → A) (t : relationAlgebra.Term α) : A :=
  letI := compatibleRelationAlgebraOfRelationAlgebra A
  t.realize v

/-- Pairs of subterms whose relational composition must have witnesses. -/
private def products [DecidableEq α] : relationAlgebra.Term α → Finset (Equation α)
  | .var _ => ∅
  | .func f ts => (Finset.univ.biUnion fun i => products (ts i)) ∪
      match f with
      | .mul => {(ts 0, ts 1)}
      | _ => ∅

private structure Failure (e : Equation α) (k : ℕ) where
  d : ℕ
  pos : 0 < d
  table : Table (Fin d)
  lawful : LawfulAtomStructure (SymmetricCycles.atomStructure table)
  witnesses : HasCommonWitnesses k table
  assignment : α → ComplexAlgebra (SymmetricCycles.atomStructure table)
  atom : Option (Fin d)
  different : letI := lawful
    ¬ (atom ∈ value assignment e.1 ↔ atom ∈ value assignment e.2)

attribute [local instance] Failure.lawful

private noncomputable abbrev U := hyperfilter ℕ

private theorem large (m : ℕ) : ∀ᶠ n in U, m < n :=
  Nat.hyperfilter_le_atTop (eventually_gt_atTop m)

private theorem transfer {e : Equation α} (F : (n : ℕ) → Failure e (n + 2))
    (N : ∀ n, Network (F n).table (n + 2 + 2)) (tasks : ℕ → Equation α)
    (hN : ∀ n i j t, Nat.pair (Nat.pair i j) t < n + 2 →
      (N n).Meets (Nat.pair (Nat.pair i j) t + 3) i j
        (value (F n).assignment (tasks t).1).carrier (value (F n).assignment (tasks t).2).carrier)
    [DecidableEq α] (t : relationAlgebra.Term α)
    (ht : ∀ p ∈ products t, ∃ m, tasks m = p) (i j : ULift.{u} ℕ) :
    let v (x : α) : SetRel (ULift.{u} ℕ) (ULift.{u} ℕ) :=
      {p | ∀ᶠ n in U, (N n).atom p.1.down p.2.down ∈ (F n).assignment x}
    (i, j) ∈ value v t ↔ ∀ᶠ n in U, (N n).atom i.down j.down ∈ value (F n).assignment t := by
  intro v
  induction t generalizing i j with
  | var => rfl
  | @func l f ts ih =>
    have hv (a : Fin l) := ih a (fun p hp => ht p
      (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, hp⟩)))
    cases f with
    | sup =>
      change (_ ∨ _) ↔ ∀ᶠ n in U, (N n).atom i.down j.down ∈ value (F n).assignment (ts 0) ∨
        (N n).atom i.down j.down ∈ value (F n).assignment (ts 1)
      rw [hv 0 i j, hv 1 i j, Ultrafilter.eventually_or]
    | compl =>
      change (¬ _) ↔ ∀ᶠ n in U, (N n).atom i.down j.down ∉ value (F n).assignment (ts 0)
      rw [hv 0 i j, Ultrafilter.eventually_not]
    | star =>
      change (j,i) ∈ value v (ts 0) ↔ ∀ᶠ n in U, (N n).atom i.down j.down ∈ star _
      simp only [ComplexAlgebra.mem_star]
      change _ ↔ ∀ᶠ n in U, (N n).atom i.down j.down ∈ value (F n).assignment (ts 0)
      simpa only [Network.atom_symm _ i.down j.down] using hv 0 j i
    | one =>
      change i = j ↔ ∀ᶠ n in U, (N n).atom i.down j.down = none
      by_cases h : i = j
      · subst j
        simp [Network.atom]
      · have hd : i.down ≠ j.down := fun he => h (ULift.ext he)
        simp [Network.atom, h, hd, Filter.NeBot.ne]
    | mul =>
      obtain ⟨t, ht⟩ := ht (ts 0, ts 1) (Finset.mem_union_right _ (Finset.mem_singleton_self _))
      change (∃ z, (i,z) ∈ value v (ts 0) ∧ (z,j) ∈ value v (ts 1)) ↔
        ∀ᶠ n in U, (N n).atom i.down j.down ∈ value (F n).assignment (ts 0) *
          value (F n).assignment (ts 1)
      constructor
      · rintro ⟨z, hiz, hzj⟩
        filter_upwards [(hv 0 i z).mp hiz, (hv 1 z j).mp hzj, large i.down, large j.down,
          large z.down] with n h₁ h₂ hi hj hz
        exact ⟨_, h₁, _, h₂, (N n).cycle_atom (by omega) (by omega) (by omega)⟩
      · intro h
        let m := Nat.pair (Nat.pair i.down j.down) t
        have hex : ∀ᶠ n in U, ∃ z : Fin (m + 3),
            (N n).atom i.down z ∈ value (F n).assignment (ts 0) ∧
            (N n).atom z j.down ∈ value (F n).assignment (ts 1) := by
          filter_upwards [h, large m] with n hn hm
          have meet := hN n i.down j.down t (by change m < n + 2; omega)
          rw [ht] at meet
          obtain ⟨z, hz, h₁,h₂⟩ := meet hn
          exact ⟨⟨z,hz⟩, h₁,h₂⟩
        -- The same finite witness bound works in every sufficiently large network, so a
        -- single vertex realizes the composition on an ultrafilter-large set of indices.
        obtain ⟨z, hz⟩ := Ultrafilter.eventually_exists_iff.mp hex
        exact ⟨⟨z.val⟩, (hv 0 i ⟨z.val⟩).mpr (hz.mono fun _ => And.left),
          (hv 1 ⟨z.val⟩ j).mpr (hz.mono fun _ => And.right)⟩

private theorem no_failures {e : Equation α}
    (he : e.Holds (SetRel (ULift.{u} ℕ) (ULift.{u} ℕ))) (F : (n : ℕ) → Failure e (n + 2)) :
    False := by
  classical
  let pool := products e.1 ∪ products e.2
  let index : pool ↪ ℕ := pool.equivFin.toEmbedding.trans Fin.valEmbedding
  let tasks : ℕ → Equation α := Function.extend index Subtype.val fun _ => e
  have enumerates (p) (hp : p ∈ pool) : ∃ m, tasks m = p :=
    ⟨index ⟨p,hp⟩, index.injective.extend_apply _ _ _⟩
  let seed (n : ℕ) := (F n).atom.getD ⟨0, (F n).pos⟩
  have networks (n : ℕ) := Network.exists_meeting_requests (F n).witnesses (seed n)
    (fun t => (value (F n).assignment (tasks t).1).carrier)
    (fun t => (value (F n).assignment (tasks t).2).carrier)
  choose N hseed hN using networks
  let v (x : α) : SetRel (ULift.{u} ℕ) (ULift.{u} ℕ) :=
    {p | ∀ᶠ n in U, (N n).atom p.1.down p.2.down ∈ (F n).assignment x}
  have hv : value v e.1 = value v e.2 := he v
  have endpoints : ∀ᶠ n in U, ∃ j : Fin 2, (N n).atom 0 j = (F n).atom := .of_forall fun n => by
    cases h : (F n).atom with
    | none => exact ⟨0, by simp [Network.atom]⟩
    | some a => exact ⟨1, by simpa [seed, h] using hseed n⟩
  obtain ⟨j, hj⟩ := Ultrafilter.eventually_exists_iff.mp endpoints
  let i' : ULift.{u} ℕ := ⟨0⟩
  let j' : ULift.{u} ℕ := ⟨j⟩
  have h₁ := transfer F N tasks hN e.1
    (fun p hp => enumerates p (Finset.mem_union_left _ hp)) i' j'
  have h₂ := transfer F N tasks hN e.2
    (fun p hp => enumerates p (Finset.mem_union_right _ hp)) i' j'
  have heq := h₁.symm.trans ((Set.ext_iff.mp hv (i',j')).trans h₂)
  have same := (Ultrafilter.eventually_imp.mpr heq.mp).and (Ultrafilter.eventually_imp.mpr heq.mpr)
  obtain ⟨n, hn, hz⟩ := (same.and hj).exists
  exact (F n).different (hz ▸ (Iff.intro hn.1 hn.2))

/-- Each equation valid in representable algebras follows on symmetric tables from a fixed
finite common-witness bound. -/
theorem exists_commonWitnesses_bound (e : Equation α) (he : e.ValidInRRA) :
    ∃ k, 2 ≤ k ∧ ∀ (d : ℕ) (_ : 0 < d) (T : Table (Fin d))
      [LawfulAtomStructure (SymmetricCycles.atomStructure T)], HasCommonWitnesses k T →
      e.Holds (ComplexAlgebra (SymmetricCycles.atomStructure T)) := by
  classical
  by_contra! h
  have bad (n : ℕ) : Nonempty (Failure e (n + 2)) := by
    obtain ⟨d,hd,T,inst,hw,hbad⟩ := h (n + 2) (by omega)
    let _ := inst
    obtain ⟨v,hv⟩ := not_forall.mp hbad
    have hz : ∃ z, ¬ (z ∈ value v e.1 ↔ z ∈ value v e.2) :=
      not_forall.mp fun hs => hv (ComplexAlgebra.ext hs)
    obtain ⟨z,hz⟩ := hz
    exact ⟨⟨d,hd,T,inst,hw,v,z,hz⟩⟩
  apply no_failures _ (fun n => (bad n).some)
  apply he
  exact ⟨PUnit, fun _ => _, ⟨RelationAlgebraHom.pi (fun _ => RelationAlgebraHom.id _),
    fun _ _ h => congrFun h PUnit.unit⟩⟩

end Equation

end Cslib.RelationAlgebra
