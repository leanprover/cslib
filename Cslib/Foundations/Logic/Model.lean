/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Foundations.Logic.Connectives
public import Cslib.Foundations.Logic.InferenceSystem
public import Cslib.Logics.Modal.Basic
public import Cslib.Logics.Propositional.NaturalDeduction.Basic
public import Cslib.Logics.HML.Basic

/-! # Semantics for logical systems

This file is a **draft** proposal for how CSLib might factor out useful semantic concepts across
different logics, in order to share notation and basic results. Some concepts we aim to unify are:

- A satisfaction relation: `HasEntails Model Formula` indicates that a "model" `M : Model`
carries a satisfaction relation `Entails : Model → Formula → Prop` over the "proposition" type
`Formula`. Examples are `Modal.Satisfies` and `HML.Satisfies`.
- Soundness and completeness wrt an inference system.
- The `theory` associated to a single model, and the `logic` associated to a set of models. This
captures `HML.theory`, `Modal.theory` and `Modal.logic`.

Further developments could include relating different models of a given logic, models of
higher-order logics (once they exist in CSLib), and ...
-/

public section

namespace Cslib.Logic

/-- Objects of type `Model` carry a forcing relation with the proposition type `Formula`. -/
class HasEntails (Model : Type*) (Formula : outParam Type*) where
  /-- `Entails b a` has the intended semantics "`a` is valid in the model `b`". -/
  Entails : Model → Formula → Prop

scoped notation M " ⊨ " A => HasEntails.Entails M A

/-- Bundled interpretation function. -/
class HasInterp (Model : Type*) (Formula : outParam Type*) where
  /-- Type carrying interpretation. -/
  Ground : Model → Type*
  /-- Interpret a proposition in a model. -/
  interp : (M : Model) → Formula → Ground M

/-- An `InterpModel` consists of an interpretation function, and a set specifying which
  interpretations are considered valid. -/
class HasInterpEntails (Model : Type*) (Formula : outParam Type*) extends
    HasInterp Model Formula where
  /-- The set of valid interpretations. -/
  filter (M : Model) : Set (Ground M)

instance HasInterpEntails.instHasEntails {Model Formula : Type*}
    [HasInterpEntails Model Formula] : HasEntails Model Formula where
  Entails b a := HasInterp.interp b a ∈ filter b

namespace HasInterp

class AlgebraicAnd (Model Formula : Type*) [HasInterp Model Formula] [HasAnd Formula]
    [∀ M : Model, Min (Ground M)] where
  interp_and_eq (M : Model) (x y : Formula) : interp M (x ∧ y) = interp M x ⊓ interp M y

class AlgebraicOr (Model Formula : Type*) [HasInterp Model Formula] [HasOr Formula]
    [∀ M : Model, Max (Ground M)] where
  interp_or_eq (M : Model) (x y : Formula) : interp M (x ∨ y) = interp M x ⊔ interp M y

class AlgebraicImpl (Model Formula : Type*) [HasInterp Model Formula] [HasImpl Formula]
    [∀ M : Model, HImp (Ground M)] where
  interp_impl_eq (M : Model) (x y : Formula) : interp M (x → y) = interp M x ⇨ interp M y

class AlgebraicNot (Model Formula : Type*) [HasInterp Model Formula] [HasNot Formula]
    [∀ M : Model, Compl (Ground M)] where
  interp_not_eq (M : Model) (x y : Formula) : interp M (¬ x) = (interp M x)ᶜ

end HasInterp

open HasEntails InferenceSystem

variable {Model Formula T} [HasEntails Model Formula] [InferenceSystem T Formula]

def SoundFor (Model Formula T) [HasEntails Model Formula] [InferenceSystem T Formula]
    (S : Set Model) : Prop := ∀ (A : Formula), DerivableIn T A → ∀ M ∈ S, M ⊨ A

lemma SoundFor.subset {S S' : Set Model} (hS : S ⊆ S') :
    SoundFor Model Formula T S' → SoundFor Model Formula T S := fun h A hA M hM => h A hA M (hS hM)

def CompleteFor (Model Formula T : Type*) [HasEntails Model Formula] [InferenceSystem T Formula]
    (S : Set Model) : Prop := ∀ A : Formula, (∀ M ∈ S, M ⊨ A) → DerivableIn T A

lemma CompleteFor.supset {S S' : Set Model} (hS : S ⊆ S') :
    CompleteFor Model Formula T S → CompleteFor Model Formula T S' :=
  fun h A hA => h A (fun M hM => hA M (hS hM))

def IsCompleteModel (Model Formula T) [HasEntails Model Formula] [InferenceSystem T Formula]
    (M : Model) : Prop := ∀ (A : Formula), (M ⊨ A) → DerivableIn T A

def HasEntails.theory {Model Formula : Type*} [HasEntails Model Formula] (M : Model) :
    Set Formula := {A : Formula | M ⊨ A}

def HasEntails.logic {Model Formula : Type*} [HasEntails Model Formula] (S : Set Model) :
    Set Formula := {A | ∀ M ∈ S, M ⊨ A}

/-! ### Modal logic

NB: we define entailment for pairs `(M, w)` of `M : Modal.Model World Atom` and a world `w`.
-/

section Modal

/-- Instance for "local forcing" (ie at the specific world) using unbundled design. -/
instance {Atom World : Type*} :
    HasEntails (Modal.Model World Atom × World) (Modal.Proposition Atom) where
  Entails M A := Modal.Satisfies M.1 M.2 A

/-- Global forcing in the unbundled design. -/
instance {Atom World : Type*} :
    HasEntails (Modal.Model World Atom) (Modal.Proposition Atom) where
  Entails M A := ∀ w : World, Modal.Satisfies M w A

example {World Atom : Type*} (M : Modal.Model World Atom) (w : World) (A : Modal.Proposition Atom) :
    Modal.Satisfies M w A ↔ (M, w) ⊨ A := by rfl

example {World Atom : Type*} (M : Modal.Model World Atom) (A : Modal.Proposition Atom) :
    A.valid {M} ↔ M ⊨ A := by simp [Entails]; rfl

example {World Atom : Type*} (M : Modal.Model World Atom) (w : World) :
    Modal.theory M w = HasEntails.theory (M, w) := by rfl

example {World Atom : Type*} (S : Set (Modal.Model World Atom)) :
    Modal.logic S = HasEntails.logic S := rfl

end Modal

/-! ### Propositional logic

Examples for interpretation-style models of propositional logic.
-/

namespace PL

variable {Atom : Type*}

instance : HasAnd (Proposition Atom) := ⟨Proposition.and⟩
instance : HasOr (Proposition Atom) := ⟨Proposition.or⟩
instance : HasImpl (Proposition Atom) := ⟨Proposition.impl⟩
instance [Bot Atom] : HasNot (Proposition Atom) := ⟨Proposition.neg⟩

structure HeytingModel (Atom : Type*) where
  H : Type*
  [inst : GeneralizedHeytingAlgebra H]
  v : Atom → H

instance (M : HeytingModel Atom) : GeneralizedHeytingAlgebra M.H := M.inst

def HeytingModel.interp (M : HeytingModel Atom) : Proposition Atom → M.H
  | Proposition.atom x => M.v x
  | Proposition.and A B => M.interp A ⊓ M.interp B
  | Proposition.or A B => M.interp A ⊔ M.interp B
  | Proposition.impl A B => M.interp A ⇨ M.interp B

instance : HasInterpEntails (HeytingModel Atom) (Proposition Atom) where
  Ground M := M.H
  interp := HeytingModel.interp
  filter _ := {⊤}

instance (M : HeytingModel Atom) : GeneralizedHeytingAlgebra (HasInterp.Ground M) := M.inst

instance : HasInterp.AlgebraicAnd (HeytingModel Atom) (Proposition Atom) where
  interp_and_eq _ _ _ := rfl

instance : HasInterp.AlgebraicOr (HeytingModel Atom) (Proposition Atom) where
  interp_or_eq _ _ _ := rfl

instance : HasInterp.AlgebraicImpl (HeytingModel Atom) (Proposition Atom) where
  interp_impl_eq _ _ _ := rfl

theorem HeytingModel.sound [DecidableEq Atom] {T : Theory Atom} :
    SoundFor (HeytingModel Atom) (Proposition Atom) T {M | ∀ A ∈ T, interp M A = ⊤} :=
  sorry -- i have this in a branch

def Theory.lindenbaum [DecidableEq Atom] (T : Theory Atom) : HeytingModel Atom :=
  sorry -- usual Heyting-algebra of propositions modulo equivalence

theorem Theory.lindenbaum_complete [DecidableEq Atom] {T : Theory Atom} :
    IsCompleteModel (HeytingModel Atom) (Proposition Atom) T T.lindenbaum :=
  sorry -- also in a branch

abbrev Valuation (Atom : Type*) := Atom → Prop

def Valuation.interp (v : Valuation Atom) : Proposition Atom → Prop
  | .atom x => v x
  | .and A B => v.interp A ∧ v.interp B
  | .or A B => v.interp A ∨ v.interp B
  | .impl A B => v.interp A → v.interp B

instance : HasInterpEntails (Valuation Atom) (Proposition Atom) where
  Ground _ := Prop
  interp v A := v.interp A
  filter _ := {True}

end PL

/-! ### Hindley-Miller logic -/

variable {State Label : Type*}

instance : HasEntails  (LTS State Label × State) (HML.Proposition Label) where
  Entails M := HML.Satisfies M.1 M.2

example (lts : LTS State Label) (s : State) :
  HML.theory lts s = HasEntails.theory (lts, s) := by rfl

end Cslib.Logic
