/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.Core.MaximalConsistent
public import Cslib.Logics.Bimodal.Metalogic.Core.MCSProperties
public import Cslib.Logics.Bimodal.Metalogic.Bundle.TemporalContent
public import Cslib.Logics.Bimodal.Metalogic.BXCanonical.Frame
public import Cslib.Logics.Bimodal.Theorems.GeneralizedNecessitation
public import Cslib.Logics.Bimodal.Metalogic.Bundle.ModalSaturation
public import Mathlib.Data.Rat.Defs

/-!
# Chronicle Types for Burgess 1982 Construction

Defines the chronicle data structure from Burgess 1982, Section 2.

## References

* Ported from BimodalLogic/Theories/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleTypes.lean
* Burgess 1982: "Axioms for tense logic II: Time periods"
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.BXCanonical.Chronicle

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Metalogic.Core
open Cslib.Logic.Bimodal.Metalogic.Bundle
open Cslib.Logic.Bimodal.Theorems

attribute [local instance] Classical.propDecidable

variable {Atom : Type*}

/-! ## FC-Parametric Utilities -/

/-- Lift a Base-level derivation to any frame class. -/
noncomputable def liftBase (fc : FrameClass) {Gamma : Context Atom} {phi : Formula Atom}
    (d : DerivationTree FrameClass.Base Gamma phi) : DerivationTree fc Gamma phi :=
  d.lift (FrameClass.base_le fc)

/-- An MCS at any frame class is also an MCS at Base. -/
theorem mcs_to_base {fc : FrameClass} {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) :
    SetMaximalConsistent FrameClass.Base A := by
  constructor
  · intro L hL ⟨d⟩
    exact h_mcs.1 L hL ⟨liftBase fc d⟩
  · intro phi hphi
    have h_neg : phi.neg ∈ A := by
      rcases SetMaximalConsistent.negation_complete h_mcs phi with h | h
      · exact absurd h hphi
      · exact h
    intro h_cons
    exact set_consistent_not_both h_cons phi (Set.mem_insert phi A) (Set.mem_insert_of_mem phi h_neg)

/-! ## Deductively Closed Sets (DCS) -/

/-- A set is closed under derivation. -/
def ClosedUnderDerivation (fc : FrameClass) (Omega : Set (Formula Atom)) : Prop :=
  ∀ (L : List (Formula Atom)) (phi : Formula Atom),
    (∀ psi ∈ L, psi ∈ Omega) → (DerivationTree fc L phi) → phi ∈ Omega

/-- A set is deductively closed (consistent + closed under derivation). -/
def SetDeductivelyClosed (fc : FrameClass) (Omega : Set (Formula Atom)) : Prop :=
  SetConsistent fc Omega ∧ ClosedUnderDerivation fc Omega

/-- Every MCS is deductively closed. -/
theorem mcs_is_dcs {fc : FrameClass} {Omega : Set (Formula Atom)}
    (h : SetMaximalConsistent fc Omega) :
    SetDeductivelyClosed fc Omega :=
  ⟨h.1, fun L _ hL hd => SetMaximalConsistent.closed_under_derivation h L hL hd⟩

/-- A CUD set contains all theorems. -/
theorem cud_contains_theorems {fc : FrameClass} {Omega : Set (Formula Atom)}
    (h : ClosedUnderDerivation fc Omega)
    {phi : Formula Atom} (hd : DerivationTree fc [] phi) : phi ∈ Omega :=
  h [] phi (fun _ h => absurd h List.not_mem_nil) hd

/-- A DCS contains all theorems. -/
theorem dcs_contains_theorems {fc : FrameClass} {Omega : Set (Formula Atom)}
    (h : SetDeductivelyClosed fc Omega)
    {phi : Formula Atom} (hd : DerivationTree fc [] phi) : phi ∈ Omega :=
  cud_contains_theorems h.2 hd

/-- Modus ponens in a CUD set. -/
theorem cud_modus_ponens {fc : FrameClass} {Omega : Set (Formula Atom)}
    (h : ClosedUnderDerivation fc Omega)
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
theorem dcs_modus_ponens {fc : FrameClass} {Omega : Set (Formula Atom)}
    (h : SetDeductivelyClosed fc Omega)
    {phi psi : Formula Atom} (h_imp : phi.imp psi ∈ Omega) (h_phi : phi ∈ Omega) : psi ∈ Omega :=
  cud_modus_ponens h.2 h_imp h_phi

/-- A CUD set is closed under conjunction. -/
theorem cud_conj_closed {fc : FrameClass} {Omega : Set (Formula Atom)}
    (h : ClosedUnderDerivation fc Omega)
    {phi psi : Formula Atom} (h_phi : phi ∈ Omega) (h_psi : psi ∈ Omega) : Formula.and phi psi ∈ Omega := by
  have h_pair := cud_contains_theorems h (Combinators.pairing phi psi)
  exact cud_modus_ponens h (cud_modus_ponens h h_pair h_phi) h_psi

/-- A DCS is closed under conjunction. -/
theorem dcs_conj_closed {fc : FrameClass} {Omega : Set (Formula Atom)}
    (h : SetDeductivelyClosed fc Omega)
    {phi psi : Formula Atom} (h_phi : phi ∈ Omega) (h_psi : psi ∈ Omega) : Formula.and phi psi ∈ Omega :=
  cud_conj_closed h.2 h_phi h_psi

/-- A CUD set with a non-member is SDC. -/
theorem cud_not_mem_is_sdc {fc : FrameClass} {B : Set (Formula Atom)}
    (h_cud : ClosedUnderDerivation fc B)
    {phi : Formula Atom} (h_not_mem : phi ∉ B) : SetDeductivelyClosed fc B := by
  refine ⟨?_, h_cud⟩
  intro L hL ⟨d⟩
  have h_bot : (Formula.bot : Formula Atom) ∈ B := h_cud L (Formula.bot : Formula Atom) hL d
  have h_efq : DerivationTree fc [] ((Formula.bot : Formula Atom).imp phi) :=
    Propositional.efq_axiom phi
  exact h_not_mem (cud_modus_ponens h_cud (cud_contains_theorems h_cud h_efq) h_bot)

/-! ## Adjacency predicate -/

def Adjacent (dom : Finset Rat) (x y : Rat) : Prop :=
  x ∈ dom ∧ y ∈ dom ∧ x < y ∧ ∀ z ∈ dom, ¬(x < z ∧ z < y)

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

def rMaximal (fc : FrameClass) (A B : Set (Formula Atom)) : Prop :=
  SetDeductivelyClosed fc B ∧
  rRelation A B ∧
  ∀ (C : Set (Formula Atom)),
    SetDeductivelyClosed fc C →
    B ⊂ C →
    ¬rRelation A C

def rMaximalSince (fc : FrameClass) (A B : Set (Formula Atom)) : Prop :=
  SetDeductivelyClosed fc B ∧
  rRelationSince A B ∧
  ∀ (C : Set (Formula Atom)),
    SetDeductivelyClosed fc C →
    B ⊂ C →
    ¬rRelationSince A C

def R3Maximal (fc : FrameClass) (A B C : Set (Formula Atom)) : Prop :=
  SetDeductivelyClosed fc B ∧
  r3Relation A B C ∧
  ∀ (D : Set (Formula Atom)),
    SetDeductivelyClosed fc D →
    B ⊂ D →
    ¬r3Relation A D C

def R3MaximalSince (fc : FrameClass) (A B C : Set (Formula Atom)) : Prop :=
  SetDeductivelyClosed fc B ∧
  r3RelationSince A B C ∧
  ∀ (D : Set (Formula Atom)),
    SetDeductivelyClosed fc D →
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

def BurgessR3Maximal (fc : FrameClass) (A B C : Set (Formula Atom)) : Prop :=
  ClosedUnderDerivation fc B ∧
  burgessR3 A B C ∧
  ∀ D, ClosedUnderDerivation fc D → B ⊂ D → ¬burgessR3 A D C

/-! ## Chronicle Structure -/

structure Chronicle (Atom : Type*) where
  f : Rat → Set (Formula Atom)
  g : Rat → Rat → Set (Formula Atom)
  dom : Finset Rat

/-! ## Chronicle Conditions -/

def Chronicle.c0 (fc : FrameClass) (chi : Chronicle Atom) : Prop :=
  ∀ x ∈ chi.dom, SetMaximalConsistent fc (chi.f x)

def Chronicle.c1 (fc : FrameClass) (chi : Chronicle Atom) : Prop :=
  ∀ x y : Rat, x ∈ chi.dom → y ∈ chi.dom → x < y → ClosedUnderDerivation fc (chi.g x y)

def Chronicle.c2 (chi : Chronicle Atom) : Prop :=
  ∀ x y : Rat, x ∈ chi.dom → y ∈ chi.dom → x < y → r3Relation (chi.f x) (chi.g x y) (chi.f y)

def Chronicle.c2' (fc : FrameClass) (chi : Chronicle Atom) : Prop :=
  ∀ x y : Rat, Adjacent chi.dom x y →
    BurgessR3Maximal fc (chi.f x) (chi.g x y) (chi.f y)

def Chronicle.c3 (chi : Chronicle Atom) : Prop :=
  ∀ x y z : Rat, x ∈ chi.dom → y ∈ chi.dom → z ∈ chi.dom →
    x < y → y < z → chi.g x z = chi.g x y ∩ chi.f y ∩ chi.g y z

def Chronicle.c4 (chi : Chronicle Atom) : Prop :=
  ∀ x y : Rat, x ∈ chi.dom → y ∈ chi.dom → x < y →
    ∀ (gamma delta : Formula Atom),
      (Formula.untl delta gamma).neg ∈ chi.f x →
      delta ∈ chi.f y →
      ∃ z ∈ chi.dom, x < z ∧ z < y ∧ gamma.neg ∈ chi.f z

def Chronicle.c4' (chi : Chronicle Atom) : Prop :=
  ∀ x y : Rat, x ∈ chi.dom → y ∈ chi.dom → y < x →
    ∀ (gamma delta : Formula Atom),
      (Formula.snce delta gamma).neg ∈ chi.f x →
      delta ∈ chi.f y →
      ∃ z ∈ chi.dom, y < z ∧ z < x ∧ gamma.neg ∈ chi.f z

def Chronicle.c5 (chi : Chronicle Atom) : Prop :=
  ∀ x ∈ chi.dom,
    ∀ (gamma delta : Formula Atom),
      Formula.untl delta gamma ∈ chi.f x →
      ∃ y ∈ chi.dom, x < y ∧ delta ∈ chi.f y ∧
        ∀ z ∈ chi.dom, x < z → z < y →
          gamma ∈ chi.f z ∧ Formula.untl delta gamma ∈ chi.f z

def Chronicle.c5' (chi : Chronicle Atom) : Prop :=
  ∀ x ∈ chi.dom,
    ∀ (gamma delta : Formula Atom),
      Formula.snce delta gamma ∈ chi.f x →
      ∃ y ∈ chi.dom, y < x ∧ delta ∈ chi.f y ∧
        ∀ z ∈ chi.dom, y < z → z < x →
          gamma ∈ chi.f z ∧ Formula.snce delta gamma ∈ chi.f z

/-! ## Valid Chronicle -/

structure ValidChronicle (Atom : Type*) (fc : FrameClass) extends Chronicle Atom where
  hc0 : toChronicle.c0 fc
  hc1 : toChronicle.c1 fc
  hc2 : toChronicle.c2
  hc2' : toChronicle.c2' fc
  hc3 : toChronicle.c3
  hc4 : toChronicle.c4
  hc4' : toChronicle.c4'
  hc5 : toChronicle.c5
  hc5' : toChronicle.c5'

/-! ## C3 Consequences -/

theorem c3_interval_subset_point (chi : Chronicle Atom) (h_c3 : chi.c3)
    {x y z : Rat} (hx : x ∈ chi.dom) (hy : y ∈ chi.dom) (hz : z ∈ chi.dom)
    (hxy : x < y) (hyz : y < z) :
    chi.g x z ⊆ chi.f y := by
  intro phi hphi; rw [h_c3 x y z hx hy hz hxy hyz] at hphi; exact hphi.1.2

theorem c3_interval_subset_left (chi : Chronicle Atom) (h_c3 : chi.c3)
    {x y z : Rat} (hx : x ∈ chi.dom) (hy : y ∈ chi.dom) (hz : z ∈ chi.dom)
    (hxy : x < y) (hyz : y < z) :
    chi.g x z ⊆ chi.g x y := by
  intro phi hphi; rw [h_c3 x y z hx hy hz hxy hyz] at hphi; exact hphi.1.1

theorem c3_interval_subset_right (chi : Chronicle Atom) (h_c3 : chi.c3)
    {x y z : Rat} (hx : x ∈ chi.dom) (hy : y ∈ chi.dom) (hz : z ∈ chi.dom)
    (hxy : x < y) (hyz : y < z) :
    chi.g x z ⊆ chi.g y z := by
  intro phi hphi; rw [h_c3 x y z hx hy hz hxy hyz] at hphi; exact hphi.2

/-! ## ChronicleInvariant Bundle -/

structure ChronicleInvariant (fc : FrameClass) (chi : Chronicle Atom) : Prop where
  hc0 : chi.c0 fc
  hc1 : chi.c1 fc
  hc2' : chi.c2' fc
  hc3 : chi.c3

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

theorem r3Relation_implies_rRelation {A B C : Set (Formula Atom)}
    (h : r3Relation A B C) : rRelation A B := h.1

theorem r3Relation_implies_rRelationSince {A B C : Set (Formula Atom)}
    (h : r3Relation A B C) : rRelationSince C B := h.2

theorem r3Relation_subset {A B B' C : Set (Formula Atom)}
    (h : r3Relation A B C) (h_sub : B ⊆ B') : r3Relation A B' C :=
  ⟨rRelation_subset h.1 h_sub, rRelationSince_subset h.2 h_sub⟩

theorem R3Maximal_dcs {fc : FrameClass} {A B C : Set (Formula Atom)}
    (h : R3Maximal fc A B C) : SetDeductivelyClosed fc B := h.1

theorem R3Maximal_r3 {fc : FrameClass} {A B C : Set (Formula Atom)}
    (h : R3Maximal fc A B C) : r3Relation A B C := h.2.1

theorem R3Maximal_rRelation {fc : FrameClass} {A B C : Set (Formula Atom)}
    (h : R3Maximal fc A B C) : rRelation A B := h.2.1.1

/-! ## DCS Intersection Properties -/

theorem dcs_inter_dcs {fc : FrameClass} {S1 S2 : Set (Formula Atom)}
    (h1 : SetDeductivelyClosed fc S1) (h2 : SetDeductivelyClosed fc S2)
    (h_cons : SetConsistent fc (S1 ∩ S2)) :
    SetDeductivelyClosed fc (S1 ∩ S2) := by
  exact ⟨h_cons, fun L phi hL hd => ⟨h1.2 L phi (fun psi hpsi => (hL psi hpsi).1) hd,
    h2.2 L phi (fun psi hpsi => (hL psi hpsi).2) hd⟩⟩

theorem dcs_inter_mcs {fc : FrameClass} {S1 S2 : Set (Formula Atom)}
    (h1 : SetDeductivelyClosed fc S1) (h2 : SetMaximalConsistent fc S2)
    (h_cons : SetConsistent fc (S1 ∩ S2)) :
    SetDeductivelyClosed fc (S1 ∩ S2) :=
  dcs_inter_dcs h1 (mcs_is_dcs h2) h_cons

theorem SetConsistent_of_subset {fc : FrameClass} {Omega T : Set (Formula Atom)}
    (h_sub : Omega ⊆ T) (h_cons : SetConsistent fc T) : SetConsistent fc Omega := by
  intro L hL hd
  exact h_cons L (fun psi hpsi => h_sub (hL psi hpsi)) hd

theorem three_way_inter_consistent {fc : FrameClass} {S1 S2 S3 : Set (Formula Atom)}
    (h3_cons : SetConsistent fc S3) :
    SetConsistent fc (S1 ∩ S2 ∩ S3) :=
  SetConsistent_of_subset (fun _ h => h.2) h3_cons

theorem dcs_inter_mcs_inter_dcs {fc : FrameClass} {S1 S2 S3 : Set (Formula Atom)}
    (h1 : SetDeductivelyClosed fc S1) (h2 : SetMaximalConsistent fc S2)
    (h3 : SetDeductivelyClosed fc S3)
    (h_cons : SetConsistent fc (S1 ∩ S2 ∩ S3)) :
    SetDeductivelyClosed fc (S1 ∩ S2 ∩ S3) := by
  exact ⟨h_cons, fun L phi hL hd =>
    ⟨⟨h1.2 L phi (fun psi hpsi => (hL psi hpsi).1.1) hd,
      (mcs_is_dcs h2).2 L phi (fun psi hpsi => (hL psi hpsi).1.2) hd⟩,
      h3.2 L phi (fun psi hpsi => (hL psi hpsi).2) hd⟩⟩

end Cslib.Logic.Bimodal.Metalogic.BXCanonical.Chronicle
