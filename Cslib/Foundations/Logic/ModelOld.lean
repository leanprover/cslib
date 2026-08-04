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

- A satisfaction relation: `Models α β` (resp. `ParamModels α β`) indicates that a "model" `M : β`
carries a satisfaction relation `Satisfies : β → α → Prop` over the "proposition" type α (resp.
a local `SatisfiesAt : (b : β) → (Param b) → α → Prop`). Examples are `Modal.Satisfies` and
`HML.Satisfies`.
- Soundness and completeness wrt an inference system.
- The `theory` associated to a parameter, and the `logic` associated to a class of models. This
captures `HML.theory`, `Modal.theory` and `Modal.logic`.

Further developments could include relating different models of a given logic, models of
higher-order logics (once they exist in CSLib), and ...
-/

public section

namespace Cslib.Logic

/-- Objects of type `β` carry a forcing relation with the proposition type `α`. -/
class Models (α : outParam Type*) (β : Type*) where
  /-- `Satisfies b a` has the intended semantics "`a` is valid in the model `b`". -/
  Satisfies : β → α → Prop

scoped notation "⊨[" b "] " a => Models.Satisfies b a

/-- Objects of type `β` carry a forcing relation worlds of type `γ` and the proposition type `α`. -/
class ParamModels (α : outParam Type*) (β : Type*) where
  Param : β → Type*
  /-- Forcing relation associated to each parameter. -/
  SatisfiesAt (b : β) : (Param b) → α → Prop

scoped notation w " ⊨[" b "] " a => ParamModels.SatisfiesAt b w a

instance ParamModels.toModels {α β : Type*} [ParamModels α β] : Models α β where
  Satisfies M A := ∀ w : ParamModels.Param M, w ⊨[M] A

/-- Bundled interpretation function. -/
class HasInterp (α : outParam Type*) (β : Type*) where
  /-- Type carrying interpretation. -/
  Ground : β → Type*
  /-- Interpret a proposition in a model. -/
  interp : (b : β) → α → Ground b

/-- An `InterpModel` consists of an interpretation function, and a set specifying which
  interpretations are considered valid. -/
class InterpModels (α : outParam (Type*)) (β : Type*) extends HasInterp α β where
  /-- The set of valid interpretations. -/
  filter (b : β) : Set (Ground b)

instance InterpModels.instModels {α β : Type*} [InterpModels α β] : Models α β where
  Satisfies b a := HasInterp.interp b a ∈ filter b

namespace HasInterp

class AlgebraicAnd (α β : Type*) [HasInterp α β] [HasAnd α] [∀ b : β, Min (Ground b)] where
  interp_and_eq (M : β) (x y : α) : interp M (x ∧ y) = interp M x ⊓ interp M y

class AlgebraicOr (α β : Type*) [HasInterp α β] [HasOr α] [∀ b : β, Max (Ground b)] where
  interp_or_eq (M : β) (x y : α) : interp M (x ∨ y) = interp M x ⊔ interp M y

class AlgebraicImpl (α β : Type*) [HasInterp α β] [HasImpl α] [∀ b : β, HImp (Ground b)] where
  interp_impl_eq (M : β) (x y : α) : interp M (x → y) = interp M x ⇨ interp M y

class AlgebraicNot (α β : Type*) [HasInterp α β] [HasNot α] [∀ b : β, Compl (Ground b)] where
  interp_not_eq (M : β) (x y : α) : interp M (¬ x) = (interp M x)ᶜ

end HasInterp

open Models ParamModels InferenceSystem

variable {α β T} [Models α β] [InferenceSystem T α]

def SoundFor (α β T) [Models α β] [InferenceSystem T α] (S : Set β) : Prop :=
  ∀ (A : α), DerivableIn T A → ∀ M ∈ S, ⊨[M] A

lemma SoundFor.subset {S S' : Set β} (hS : S ⊆ S') : SoundFor α β T S' → SoundFor α β T S :=
  fun h A hA M hM => h A hA M (hS hM)

def CompleteFor (α β T : Type*) [Models α β] [InferenceSystem T α] (S : Set β) : Prop :=
  ∀ A : α, (∀ M ∈ S, ⊨[M] A) → DerivableIn T A

lemma CompleteFor.supset {S S' : Set β} (hS : S ⊆ S') :
    CompleteFor α β T S → CompleteFor α β T S' := fun h A hA => h A (fun M hM => hA M (hS hM))

def IsCompleteModel (α β T) [Models α β] [InferenceSystem T α] (M : β) : Prop :=
  ∀ (A : α), (⊨[M] A) → DerivableIn T A

def ParamModels.theory {α β : Type*} [ParamModels α β] {M : β} (w : Param M) : Set α :=
  {A : α | w ⊨[M] A}

def Models.logic {α β : Type*} [Models α β] (S : Set β) : Set α := {A | ∀ b ∈ S, ⊨[b] A}

structure BundledModel (Atom : Type*) where
  World : Type*
  model : Modal.Model World Atom

def Modal.Model.toBundledModel {World Atom : Type*} (M : Modal.Model World Atom) :
  BundledModel Atom := {World := World, model := M}

/-- Instance using the bundled design. -/
instance {Atom : Type*} : ParamModels (Modal.Proposition Atom) (BundledModel Atom) where
  Param M := M.World
  SatisfiesAt M w A := Modal.Satisfies M.model w A

example {World Atom : Type*} (S : Set (Modal.Model World Atom)) :
    Modal.logic S = Models.logic (Modal.Model.toBundledModel '' S) := by
  simp [Models.logic]
  rfl

example {World Atom : Type*} (m : Modal.Model World Atom) (w : World) :
    Modal.theory m w = ParamModels.theory (M := m.toBundledModel) w := rfl

/-- Instance for "local forcing" (ie at the specific world) using unbundled design. -/
instance {Atom World : Type*} :
    Models (Modal.Proposition Atom) (Modal.Model World Atom × World) where
  Satisfies M A := Modal.Satisfies M.1 M.2 A

/-- Global forcing in the unbundled design. -/
instance {Atom World : Type*} :
    Models (Modal.Proposition Atom) (Modal.Model World Atom) where
  Satisfies M A := ∀ w : World, Modal.Satisfies M w A

example {World Atom : Type*} (M : Modal.Model World Atom) (w : World) :
    Modal.theory M w = Models.logic {(M, w)} := by
  simp [Modal.theory, logic]
  rfl

example {World Atom : Type*} (S : Set (Modal.Model World Atom)) :
    Modal.logic S = Models.logic S := rfl

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

instance : InterpModels (Proposition Atom) (HeytingModel Atom) where
  Ground M := M.H
  interp := HeytingModel.interp
  filter _ := {⊤}

instance (M : HeytingModel Atom) : GeneralizedHeytingAlgebra (HasInterp.Ground M) := M.inst

instance : HasInterp.AlgebraicAnd (Proposition Atom) (HeytingModel Atom) where
  interp_and_eq _ _ _ := rfl

instance : HasInterp.AlgebraicOr (Proposition Atom) (HeytingModel Atom) where
  interp_or_eq _ _ _ := rfl

instance : HasInterp.AlgebraicImpl (Proposition Atom) (HeytingModel Atom) where
  interp_impl_eq _ _ _ := rfl

theorem HeytingModel.sound [DecidableEq Atom] {T : Theory Atom} :
    SoundFor (Proposition Atom) (HeytingModel Atom) T {M | ∀ A ∈ T, interp M A = ⊤} :=
  sorry -- i have this in a branch

def Theory.lindenbaum [DecidableEq Atom] (T : Theory Atom) : HeytingModel Atom :=
  sorry -- usual Heyting-algebra of propositions modulo equivalence

theorem Theory.lindenbaum_complete [DecidableEq Atom] {T : Theory Atom} :
    IsCompleteModel (Proposition Atom) (HeytingModel Atom) T T.lindenbaum :=
  sorry -- also in a branch

abbrev Valuation (Atom : Type*) := Atom → Prop

def Valuation.interp (v : Valuation Atom) : Proposition Atom → Prop
  | .atom x => v x
  | .and A B => v.interp A ∧ v.interp B
  | .or A B => v.interp A ∨ v.interp B
  | .impl A B => v.interp A → v.interp B

instance : InterpModels (Proposition Atom) (Valuation Atom) where
  Ground _ := Prop
  interp v A := v.interp A
  filter _ := {True}

end PL

variable {State Label : Type*}

instance : ParamModels (HML.Proposition Label) (LTS State Label) where
  Param _ := State
  SatisfiesAt := HML.Satisfies

example (lts : LTS State Label) (s : State) :
    HML.theory lts s = ParamModels.theory (M := lts) s := by
  simp [theory, HML.theory]
  rfl

end Cslib.Logic
