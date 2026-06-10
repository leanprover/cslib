/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.ProofSystem.Instances
public import Cslib.Logics.Bimodal.Theorems.Propositional.Core
public import Cslib.Foundations.Logic.Theorems.Propositional.Connectives

/-!
# Derived Connective Reasoning

Classical merge, iff introduction/elimination, contraposition, and De Morgan laws
for the Hilbert-style proof system.

Most theorems delegate to the generic Foundations equivalents via the wrap/unwrap
bridge pattern.

Ported from BimodalLogic/Theories/Bimodal/Theorems/Propositional/Connectives.lean
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

@[expose] public section

namespace Cslib.Logic.Bimodal.Theorems.Propositional

open Cslib.Logic
open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Theorems.Combinators

variable {Atom : Type*}

noncomputable section

/-- Convert a derivation tree to a Nonempty (for typeclass functions). -/
def wrap' {φ : Formula Atom}
    (d : DerivationTree FrameClass.Base [] φ) :
    InferenceSystem.DerivableIn Bimodal.HilbertTM φ := ⟨d⟩

/-- Extract a derivation tree from Nonempty (from typeclass functions). -/
def unwrap' {φ : Formula Atom}
    (h : InferenceSystem.DerivableIn Bimodal.HilbertTM φ) :
    DerivationTree FrameClass.Base [] φ := h.some

def classical_merge (Q R : Formula Atom) :
    DerivationTree FrameClass.Base [] ((Q.imp R).imp ((Q.neg.imp R).imp R)) :=
  unwrap' (@_root_.Cslib.Logic.Theorems.Propositional.Connectives.classical_merge
    _ _ _ Bimodal.HilbertTM _ _ (φ := Q) (ψ := R))

def iff_intro (A B : Formula Atom)
    (h1 : DerivationTree FrameClass.Base [] (A.imp B))
    (h2 : DerivationTree FrameClass.Base [] (B.imp A)) :
    DerivationTree FrameClass.Base [] ((A.imp B).and (B.imp A)) :=
  unwrap' (@_root_.Cslib.Logic.Theorems.Propositional.Connectives.iff_intro
    _ _ _ Bimodal.HilbertTM _ _ (φ := A) (ψ := B) (wrap' h1) (wrap' h2))

def iff_elim_left (A B : Formula Atom) :
    DerivationTree FrameClass.Base [((A.imp B).and (B.imp A)), A] B := by
  have h_a : DerivationTree FrameClass.Base [((A.imp B).and (B.imp A)), A] A := by
    apply DerivationTree.assumption; simp
  have h_imp : DerivationTree FrameClass.Base [((A.imp B).and (B.imp A)), A] (A.imp B) := by
    have lce_inst := lce (A.imp B) (B.imp A)
    exact DerivationTree.weakening [(A.imp B).and (B.imp A)] _ _ lce_inst
      (by intro x; simp; intro h; left; exact h)
  exact DerivationTree.modus_ponens _ _ _ h_imp h_a

def iff_elim_right (A B : Formula Atom) :
    DerivationTree FrameClass.Base [((A.imp B).and (B.imp A)), B] A := by
  have h_b : DerivationTree FrameClass.Base [((A.imp B).and (B.imp A)), B] B := by
    apply DerivationTree.assumption; simp
  have h_imp : DerivationTree FrameClass.Base [((A.imp B).and (B.imp A)), B] (B.imp A) := by
    have rce_inst := rce (A.imp B) (B.imp A)
    exact DerivationTree.weakening [(A.imp B).and (B.imp A)] _ _ rce_inst
      (by intro x; simp; intro h; left; exact h)
  exact DerivationTree.modus_ponens _ _ _ h_imp h_b

def contrapose_imp (A B : Formula Atom) :
    DerivationTree FrameClass.Base [] ((A.imp B).imp (B.neg.imp A.neg)) :=
  unwrap' (@_root_.Cslib.Logic.Theorems.Propositional.Connectives.contrapose_imp
    _ _ _ Bimodal.HilbertTM _ _ (φ := A) (ψ := B))

def contraposition {A B : Formula Atom}
    (h : DerivationTree FrameClass.Base [] (A.imp B)) :
    DerivationTree FrameClass.Base [] (B.neg.imp A.neg) :=
  unwrap' (@_root_.Cslib.Logic.Theorems.Propositional.Connectives.contraposition
    _ _ _ Bimodal.HilbertTM _ _ (φ := A) (ψ := B) (wrap' h))

def contrapose_iff (A B : Formula Atom)
    (h : DerivationTree FrameClass.Base [] ((A.imp B).and (B.imp A))) :
    DerivationTree FrameClass.Base [] ((A.neg.imp B.neg).and (B.neg.imp A.neg)) :=
  unwrap' (@_root_.Cslib.Logic.Theorems.Propositional.Connectives.contrapose_iff
    _ _ _ Bimodal.HilbertTM _ _ (φ := A) (ψ := B) (wrap' h))

def iff_neg_intro (A B : Formula Atom)
    (h1 : DerivationTree FrameClass.Base [] (A.neg.imp B.neg))
    (h2 : DerivationTree FrameClass.Base [] (B.neg.imp A.neg)) :
    DerivationTree FrameClass.Base [] ((A.neg.imp B.neg).and (B.neg.imp A.neg)) :=
  unwrap' (@_root_.Cslib.Logic.Theorems.Propositional.Connectives.iff_neg_intro
    _ _ _ Bimodal.HilbertTM _ _ (φ := A) (ψ := B) (wrap' h1) (wrap' h2))

def demorgan_conj_neg_forward (A B : Formula Atom) :
    DerivationTree FrameClass.Base [] ((A.and B).neg.imp (A.neg.or B.neg)) :=
  unwrap' (@_root_.Cslib.Logic.Theorems.Propositional.Connectives.demorgan_conj_neg_forward
    _ _ _ Bimodal.HilbertTM _ _ (φ := A) (ψ := B))

def demorgan_conj_neg_backward (A B : Formula Atom) :
    DerivationTree FrameClass.Base [] ((A.neg.or B.neg).imp (A.and B).neg) :=
  unwrap' (@_root_.Cslib.Logic.Theorems.Propositional.Connectives.demorgan_conj_neg_backward
    _ _ _ Bimodal.HilbertTM _ _ (φ := A) (ψ := B))

def demorgan_conj_neg (A B : Formula Atom) :
    DerivationTree FrameClass.Base []
      (((A.and B).neg.imp (A.neg.or B.neg)).and ((A.neg.or B.neg).imp (A.and B).neg)) :=
  iff_intro (A.and B).neg (A.neg.or B.neg)
    (demorgan_conj_neg_forward A B) (demorgan_conj_neg_backward A B)

def demorgan_disj_neg_forward (A B : Formula Atom) :
    DerivationTree FrameClass.Base [] ((A.or B).neg.imp (A.neg.and B.neg)) :=
  unwrap' (@_root_.Cslib.Logic.Theorems.Propositional.Connectives.demorgan_disj_neg_forward
    _ _ _ Bimodal.HilbertTM _ _ (φ := A) (ψ := B))

def demorgan_disj_neg_backward (A B : Formula Atom) :
    DerivationTree FrameClass.Base [] ((A.neg.and B.neg).imp (A.or B).neg) :=
  unwrap' (@_root_.Cslib.Logic.Theorems.Propositional.Connectives.demorgan_disj_neg_backward
    _ _ _ Bimodal.HilbertTM _ _ (φ := A) (ψ := B))

def demorgan_disj_neg (A B : Formula Atom) :
    DerivationTree FrameClass.Base []
      (((A.or B).neg.imp (A.neg.and B.neg)).and ((A.neg.and B.neg).imp (A.or B).neg)) :=
  iff_intro (A.or B).neg (A.neg.and B.neg)
    (demorgan_disj_neg_forward A B) (demorgan_disj_neg_backward A B)

end -- noncomputable section

end Cslib.Logic.Bimodal.Theorems.Propositional
