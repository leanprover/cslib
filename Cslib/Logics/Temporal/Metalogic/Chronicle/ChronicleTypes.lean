/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/

import Cslib.Logics.Temporal.Metalogic.TemporalContent
import Cslib.Logics.Temporal.Metalogic.GeneralizedNecessitation
import Cslib.Logics.Temporal.Metalogic.PropositionalHelpers
import Cslib.Logics.Temporal.Metalogic.MCS

/-!
# Chronicle Types for Temporal Logic

DCS infrastructure, r-relation definitions, r-maximality, and Burgess relation
definitions for the temporal chronicle construction.

## References

* Ported from Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleTypes.lean
* Burgess 1982: "Axioms for tense logic II: Time periods"
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Cslib.Logic.Temporal.Metalogic.Chronicle

open Cslib.Logic.Temporal
open Cslib.Logic.Temporal.Metalogic

attribute [local instance] Classical.propDecidable

variable {Atom : Type*}

/-! ## Deductively Closed Sets (DCS) -/

/-- A set is closed under derivation. -/
def ClosedUnderDerivation (Omega : Set (Formula Atom)) : Prop :=
  ∀ (L : List (Formula Atom)) (phi : Formula Atom),
    (∀ psi ∈ L, psi ∈ Omega) → (DerivationTree FrameClass.Base L phi) → phi ∈ Omega

/-- A set is deductively closed (consistent + closed under derivation). -/
def SetDeductivelyClosed (Omega : Set (Formula Atom)) : Prop :=
  Temporal.SetConsistent Omega ∧ ClosedUnderDerivation Omega

/-- Every MCS is deductively closed. -/
theorem mcs_is_dcs {Omega : Set (Formula Atom)}
    (h : Temporal.SetMaximalConsistent Omega) :
    SetDeductivelyClosed Omega :=
  ⟨h.1, fun L _ hL hd => temporal_closed_under_derivation h hL ⟨hd⟩⟩

/-- A CUD set contains all theorems. -/
theorem cud_contains_theorems {Omega : Set (Formula Atom)}
    (h : ClosedUnderDerivation Omega)
    {phi : Formula Atom} (hd : DerivationTree FrameClass.Base [] phi) : phi ∈ Omega :=
  h [] phi (fun _ h => absurd h List.not_mem_nil) hd

/-- A DCS contains all theorems. -/
theorem dcs_contains_theorems {Omega : Set (Formula Atom)}
    (h : SetDeductivelyClosed Omega)
    {phi : Formula Atom} (hd : DerivationTree FrameClass.Base [] phi) : phi ∈ Omega :=
  cud_contains_theorems h.2 hd

/-- Modus ponens in a CUD set. -/
theorem cud_modus_ponens {Omega : Set (Formula Atom)}
    (h : ClosedUnderDerivation Omega)
    {phi psi : Formula Atom} (h_imp : phi.imp psi ∈ Omega) (h_phi : phi ∈ Omega) : psi ∈ Omega := by
  apply h [phi, phi.imp psi] psi
  · intro chi h_mem
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at h_mem
    rcases h_mem with rfl | rfl
    · exact h_phi
    · exact h_imp
  · exact DerivationTree.modus_ponens [phi, phi.imp psi] phi psi
      (DerivationTree.assumption _ (phi.imp psi) (by simp))
      (DerivationTree.assumption _ phi (by simp))

/-- Modus ponens in a DCS. -/
theorem dcs_modus_ponens {Omega : Set (Formula Atom)}
    (h : SetDeductivelyClosed Omega)
    {phi psi : Formula Atom} (h_imp : phi.imp psi ∈ Omega) (h_phi : phi ∈ Omega) : psi ∈ Omega :=
  cud_modus_ponens h.2 h_imp h_phi

/-- A CUD set is closed under conjunction. -/
theorem cud_conj_closed {Omega : Set (Formula Atom)}
    (h : ClosedUnderDerivation Omega)
    {phi psi : Formula Atom} (h_phi : phi ∈ Omega) (h_psi : psi ∈ Omega) : Formula.and phi psi ∈ Omega := by
  have h_pair := cud_contains_theorems h (pairing phi psi)
  exact cud_modus_ponens h (cud_modus_ponens h h_pair h_phi) h_psi

/-- A DCS is closed under conjunction. -/
theorem dcs_conj_closed {Omega : Set (Formula Atom)}
    (h : SetDeductivelyClosed Omega)
    {phi psi : Formula Atom} (h_phi : phi ∈ Omega) (h_psi : psi ∈ Omega) : Formula.and phi psi ∈ Omega :=
  cud_conj_closed h.2 h_phi h_psi

/-- A CUD set with a non-member is SDC. -/
theorem cud_not_mem_is_sdc {B : Set (Formula Atom)}
    (h_cud : ClosedUnderDerivation B)
    {phi : Formula Atom} (h_not_mem : phi ∉ B) : SetDeductivelyClosed B := by
  refine ⟨?_, h_cud⟩
  intro L hL ⟨d⟩
  have h_bot : (Formula.bot : Formula Atom) ∈ B := h_cud L (Formula.bot : Formula Atom) hL d
  have h_efq : DerivationTree FrameClass.Base [] ((Formula.bot : Formula Atom).imp phi) :=
    efq_axiom phi
  exact h_not_mem (cud_modus_ponens h_cud (cud_contains_theorems h_cud h_efq) h_bot)

/-! ## The r-Relation (Burgess Lemma 2.3) -/

def rRelation (A B : Set (Formula Atom)) : Prop :=
  ∀ (gamma delta : Formula Atom),
    Formula.untl delta gamma ∈ A →
    delta ∈ B ∨ (gamma ∈ B ∧ Formula.untl delta gamma ∈ B)

def rRelationSince (A B : Set (Formula Atom)) : Prop :=
  ∀ (gamma delta : Formula Atom),
    Formula.snce delta gamma ∈ A →
    delta ∈ B ∨ (gamma ∈ B ∧ Formula.snce delta gamma ∈ B)

def r3Relation (A B C : Set (Formula Atom)) : Prop :=
  rRelation A B ∧ rRelationSince C B

def r3RelationSince (A B C : Set (Formula Atom)) : Prop :=
  rRelationSince A B ∧ rRelation C B

/-! ## R-Maximality -/

def rMaximal (A B : Set (Formula Atom)) : Prop :=
  SetDeductivelyClosed B ∧
  rRelation A B ∧
  ∀ (C : Set (Formula Atom)),
    SetDeductivelyClosed C →
    B ⊂ C →
    ¬rRelation A C

def rMaximalSince (A B : Set (Formula Atom)) : Prop :=
  SetDeductivelyClosed B ∧
  rRelationSince A B ∧
  ∀ (C : Set (Formula Atom)),
    SetDeductivelyClosed C →
    B ⊂ C →
    ¬rRelationSince A C

def R3Maximal (A B C : Set (Formula Atom)) : Prop :=
  SetDeductivelyClosed B ∧
  r3Relation A B C ∧
  ∀ (D : Set (Formula Atom)),
    SetDeductivelyClosed D →
    B ⊂ D →
    ¬r3Relation A D C

def R3MaximalSince (A B C : Set (Formula Atom)) : Prop :=
  SetDeductivelyClosed B ∧
  r3RelationSince A B C ∧
  ∀ (D : Set (Formula Atom)),
    SetDeductivelyClosed D →
    B ⊂ D →
    ¬r3RelationSince A D C

/-! ## Burgess r-Relation (Content-Based) -/

def burgessR (A : Set (Formula Atom)) (beta : Formula Atom) (C : Set (Formula Atom)) : Prop :=
  ∀ gamma ∈ C, Formula.untl gamma beta ∈ A

def burgessRSet (A B C : Set (Formula Atom)) : Prop :=
  ∀ beta ∈ B, burgessR A beta C

def burgessRSince (A : Set (Formula Atom)) (beta : Formula Atom) (C : Set (Formula Atom)) : Prop :=
  ∀ gamma ∈ C, Formula.snce gamma beta ∈ A

def burgessRSetSince (A B C : Set (Formula Atom)) : Prop :=
  ∀ beta ∈ B, burgessRSince A beta C

def burgessR3 (A B C : Set (Formula Atom)) : Prop :=
  burgessRSet A B C ∧ burgessRSetSince C B A

def BurgessR3Maximal (A B C : Set (Formula Atom)) : Prop :=
  ClosedUnderDerivation B ∧
  burgessR3 A B C ∧
  ∀ D, ClosedUnderDerivation D → B ⊂ D → ¬burgessR3 A D C

/-! ## Basic Properties -/

theorem rRelation_subset {A B C : Set (Formula Atom)}
    (h_r : rRelation A B) (h_sub : B ⊆ C) : rRelation A C := by
  intro gamma delta h_until
  rcases h_r gamma delta h_until with h_delta | ⟨h_gamma, h_u⟩
  · exact Or.inl (h_sub h_delta)
  · exact Or.inr ⟨h_sub h_gamma, h_sub h_u⟩

theorem rRelationSince_subset {A B C : Set (Formula Atom)}
    (h_r : rRelationSince A B) (h_sub : B ⊆ C) : rRelationSince A C := by
  intro gamma delta h_since
  rcases h_r gamma delta h_since with h_delta | ⟨h_gamma, h_s⟩
  · exact Or.inl (h_sub h_delta)
  · exact Or.inr ⟨h_sub h_gamma, h_sub h_s⟩

theorem r3Relation_subset {A B B' C : Set (Formula Atom)}
    (h : r3Relation A B C) (h_sub : B ⊆ B') : r3Relation A B' C :=
  ⟨rRelation_subset h.1 h_sub, rRelationSince_subset h.2 h_sub⟩

theorem R3Maximal_dcs {A B C : Set (Formula Atom)}
    (h : R3Maximal A B C) : SetDeductivelyClosed B := h.1

theorem R3Maximal_r3 {A B C : Set (Formula Atom)}
    (h : R3Maximal A B C) : r3Relation A B C := h.2.1

/-! ## DCS Intersection Properties -/

theorem SetConsistent_of_subset {Omega T : Set (Formula Atom)}
    (h_sub : Omega ⊆ T) (h_cons : Temporal.SetConsistent T) : Temporal.SetConsistent Omega := by
  intro L hL hd
  exact h_cons L (fun psi hpsi => h_sub (hL psi hpsi)) hd

end Cslib.Logic.Temporal.Metalogic.Chronicle
