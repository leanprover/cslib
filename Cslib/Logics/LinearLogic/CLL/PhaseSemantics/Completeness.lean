/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Bhavik Mehta, Aleph Prover
-/

module

public import Cslib.Logics.LinearLogic.CLL.PhaseSemantics.Soundness
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Algebra.Order.Group.Multiset
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Group.Pointwise.Set.Basic

@[expose] public section

/-!
# Completeness for MALL via a phase model

This file constructs a canonical phase model and proves completeness for the
multiplicative-additive fragment of classical linear logic.

## Main definitions

* `CanonM`: the monoid of sequents
* `PrSet`: the interpretation of propositions in the model
* `canonVal`: the distinguished valuation

## Main results

* `PrSet_eq_orth`: truth sets are characterized by orthogonality
* `interpProp_canon_carrier`: semantic interpretation agrees with `PrSet`
* `derivable_of_foldParr`: derivability of the folded formula implies derivability of the sequent
* `completeness`: semantic validity implies derivability for MALL sequents

TODO: extend completeness from MALL to full CLL with exponentials. This
requires a more complex phase-model construction to account for `!` and `?`.
-/

@[expose] public section

namespace Cslib
namespace CLL

open scoped Pointwise
open PhaseSpace Logic InferenceSystem
open Fact Sequent

universe u

variable {Atom : Type u}

/-- The canonical monoid for the completeness construction: sequents under multiset addition. -/
@[reducible] def CanonM (Atom : Type u) : Type u := Multiplicative (Sequent Atom)

/-- The truth set of a proposition: sequent contexts that make `a` provable. -/
def PrSet (Atom : Type u) (a : Proposition Atom) : Set (CanonM Atom) :=
  {m | Derivable (a ::ₘ m.toAdd)}

theorem PrSet_top {Atom : Type u} : PrSet Atom ⊤ = .univ := by
  ext m; exact ⟨fun _ => trivial, fun _ => ⟨Proof.top⟩⟩

theorem PrSet_with {Atom : Type u} (a b : Proposition Atom) :
    PrSet Atom (a & b) = PrSet Atom a ∩ PrSet Atom b := by
  ext m; simp only [PrSet, Set.mem_setOf_eq, Set.mem_inter_iff]
  exact ⟨fun ⟨p⟩ => ⟨⟨p.with_inversion₁⟩, ⟨p.with_inversion₂⟩⟩,
    fun ⟨⟨p⟩, ⟨q⟩⟩ => ⟨.with p q⟩⟩

/-- The bottom set of the canonical phase space: provable sequents. -/
def canonBot (Atom : Type u) : Set (CanonM Atom) :=
  {m | Derivable m.toAdd}

theorem PrSet_bot {Atom : Type u} : PrSet Atom ⊥ = canonBot Atom := by
  ext m; exact ⟨fun ⟨p⟩ => ⟨p.bot_inversion⟩, fun ⟨p⟩ => ⟨p.bot⟩⟩

instance canonPhaseSpace (Atom : Type u) : PhaseSpace (CanonM Atom) where
  bot := canonBot Atom

theorem PrSet_eq_orth {Atom : Type u} (a : Proposition Atom) :
    PrSet Atom a = orthogonal (PrSet Atom (Proposition.dual a)) := by
  ext m; constructor
  · intro hm n hn
    change (m * n) ∈ canonBot Atom
    exact ⟨(toAdd_mul m n).symm ▸ hm.toDerivation.cut hn.toDerivation⟩
  · intro hm
    let n : CanonM Atom := Multiplicative.ofAdd {a}
    have hn : n ∈ PrSet Atom a⫠ := ⟨@Proof.ax' Atom a⟩
    exact ⟨(hm n hn).toDerivation.rwConclusion (by simp [n, toAdd_mul, add_comm])⟩

theorem PrSet_dual_eq_orth {Atom : Type u} (a : Proposition Atom) :
    PrSet Atom (Proposition.dual a) = orthogonal (PrSet Atom a) := by
  grind [Proposition.dual_involution, PrSet_eq_orth]

theorem PrSet_oplus {Atom : Type u} (a b : Proposition Atom) :
    PrSet Atom (a ⊕ b) = orthogonal (orthogonal (PrSet Atom a ∪ PrSet Atom b)) := by
  rw [PrSet_eq_orth (a := a ⊕ b)]; congr 1
  simp only [Proposition.dual]
  rw [PrSet_with a⫠ b⫠, PrSet_dual_eq_orth a, PrSet_dual_eq_orth b]
  ext m; simp only [orthogonal, imp, Multiplicative.forall, Set.mem_inter_iff, Set.mem_setOf_eq]
  exact ⟨fun ⟨hma, hmb⟩ _ ha => ha.elim (hma _) (hmb _),
    fun hm => ⟨fun x hx => hm x (.inl hx), fun x hx => hm x (.inr hx)⟩⟩

theorem PrSet_parr {Atom : Type u} (a b : Proposition Atom) :
    PrSet Atom (a ⅋ b) =
    orthogonal (PrSet Atom (Proposition.dual a) * PrSet Atom (Proposition.dual b)) := by
  ext m; constructor
  · intro hm x hx
    rcases Set.mem_mul.mp hx with ⟨s, hs, t, ht, rfl⟩
    change Derivable ((m * (s * t)).toAdd)
    have hab := Proof.parr_inversion hm.toDerivation
    have hb : ⇓(b ::ₘ (m.toAdd + s.toAdd)) :=
      Proof.rwConclusion (by simp) (Proof.cut hab (hs : Derivable _).toDerivation)
    exact ⟨Proof.rwConclusion (by simp [toAdd_mul, add_assoc])
      (Proof.cut hb (ht : Derivable _).toDerivation)⟩
  · intro hm
    let s : CanonM Atom := Multiplicative.ofAdd {a}
    let t : CanonM Atom := Multiplicative.ofAdd {b}
    have hs : s ∈ PrSet Atom a⫠ := by
      simp only [PrSet, Set.mem_setOf_eq, s]; exact ⟨@Proof.ax' _ a⟩
    have ht : t ∈ PrSet Atom b⫠ := by
      simp only [PrSet, Set.mem_setOf_eq, t]; exact ⟨@Proof.ax' _ b⟩
    have hprov : Derivable ((m * (s * t)).toAdd) := hm (s * t) (Set.mul_mem_mul hs ht)
    exact ⟨Proof.parr (hprov.toDerivation.rwConclusion (by simp [s, t, toAdd_mul, add_comm,
      Multiset.singleton_add]))⟩

theorem PrSet_tensor {Atom : Type u} (a b : Proposition Atom) :
    PrSet Atom (a ⊗ b) =
    orthogonal (orthogonal (PrSet Atom a * PrSet Atom b)) := by
  rw [PrSet_eq_orth (a ⊗ b)]
  congr 1
  have := PrSet_parr (Proposition.dual a) (Proposition.dual b)
  simp only [Proposition.dual_involution, orthogonal_def, Multiplicative.forall] at this; exact this

/-- The canonical valuation: interprets each atom via its dual's truth set. -/
def canonVal {Atom : Type u} (a : Atom) : Fact (CanonM Atom) :=
  dualFact (PrSet Atom (Proposition.atomDual a))

theorem interpProp_canon_carrier {Atom : Type u} (a : Proposition Atom)
    (ha : Proposition.IsMALL a) :
    ((@interpProp (CanonM Atom) Atom _ canonVal a) :
        Set (CanonM Atom)) =
      PrSet Atom a := by
  induction a with
  | atom a =>
    simp [interpProp, canonVal, PrSet_eq_orth (.atom a), Proposition.dual]
  | atomDual a =>
    simp only [interpProp, canonVal, dualFact, coe_neg, mk_dual_coe]
    conv_rhs => rw [PrSet_eq_orth (.atomDual a)]
    simp only [Proposition.dual]; rw [PrSet_eq_orth (.atom a)]
    simp [Proposition.dual, -orthogonal_def]
  | one =>
    simp only [interpProp, coe_one]; rw [PrSet_eq_orth (.one)]
    simp only [Proposition.dual]
    have hb : PrSet _ .bot = canonBot Atom := PrSet_bot
    aesop
  | zero =>
    simp only [interpProp, coe_zero]; rw [PrSet_eq_orth .zero, Proposition.dual]
    rw [show PrSet Atom .top = Set.univ from by simp [← PrSet_top]; rfl]
  | top => simp [interpProp, PrSet_top.symm]; rfl
  | bot =>
    simp only [interpProp]
    exact PrSet_bot.symm
  | tensor _ _ iha ihb =>
    simp [interpProp, iha ha.1, ihb ha.2, tensor, dualFact, PrSet_tensor, -orthogonal_def]
  | parr _ _ iha ihb =>
    simp [interpProp, iha ha.1, ihb ha.2, parr, dualFact, PrSet_parr,
      PrSet_dual_eq_orth, -orthogonal_def]
  | oplus _ _ iha ihb =>
    simp [interpProp, iha ha.1, ihb ha.2, oplus, dualFact, PrSet_oplus, -orthogonal_def]
  | «with» _ _ iha ihb => simp [interpProp, iha ha.1, ihb ha.2, withh, PrSet_with]
  | bang _ _ => exact False.elim ha
  | quest _ _ => exact False.elim ha

theorem interpProp_list_foldr_parr {Atom : Type u} {M : Type*} [PhaseSpace M]
    (v : Atom → Fact M) (l : List (Proposition Atom)) :
    interpProp v (List.foldr (fun A B => A ⅋ B) ⊥ l) =
    List.foldr (fun A acc => (interpProp v A) ⅋ acc) ⊥ l := by
  induction l <;> aesop

theorem Sequent.toFact_eq_interpProp_foldParr {Atom : Type u} (M : Type*) [PhaseSpace M]
    (v : Atom → Fact M) (Γ : Sequent Atom) :
    Sequent.toFact M v Γ = interpProp v (foldParr Γ) := by
  simp only [Sequent.toFact, foldParr]
  rw [interpProp_list_foldr_parr v Γ.toList]
  have hfold : ∀ l : List (Proposition Atom),
      List.foldr (fun A acc => interpProp v A ⅋ acc) ⊥ l =
      List.foldr (fun x y : Fact M => x ⅋ y) ⊥ (l.map (interpProp v)) := by
    intro l; induction l <;> aesop
  rw [hfold]
  calc
    (Γ.map (fun A => (interpProp v A))).fold (fun x y : Fact M => x ⅋ y) ⊥
        = ((Γ.toList : Multiset (Proposition Atom)).map (fun A =>
        (interpProp v A))).fold (fun x y : Fact M => x ⅋ y) ⊥ := by simp
    _ = (((Γ.toList).map (fun A => interpProp v A)) :
            Multiset (Fact M)).fold (fun x y : Fact M => x ⅋ y) ⊥ := by
      grind [congrArg (fun s => s.fold (fun x y : Fact M => x ⅋ y) ⊥)
        (@Multiset.map_coe _ _ (fun A => (interpProp v A)) (Γ.toList))]
    _ = List.foldr (fun x y : Fact M => x ⅋ y) ⊥
            ((Γ.toList).map (fun A => interpProp v A)) := by simp

theorem completeness {Atom : Type u} (Γ : Sequent Atom)
    (hMALL : IsMALL Γ) :
    (∀ (M : Type u) [PhaseSpace M] (v : Atom → Fact M),
        (Sequent.toFact M v Γ).IsValid) → Derivable Γ := by
  intro h
  have h₁ : 1 ∈ PrSet Atom (foldParr Γ) := by
    rw [← interpProp_canon_carrier _ (foldParr_isMALL Γ hMALL)]
    simp_all only [SetLike.mem_coe, ← Sequent.toFact_eq_interpProp_foldParr]
  exact derivable_of_foldParr Γ (by aesop)

end CLL
end Cslib
