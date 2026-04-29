/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Marianna Girlando
-/

module

public import Cslib.Init
public import Cslib.Foundations.Logic.InferenceSystem
public import Mathlib.Data.Set.Basic
public import Mathlib.Order.Defs.Unbundled
public import Cslib.Foundations.Data.Relation
public import Mathlib.Logic.Nonempty

/-! # Modal Logic

Modal logic is a logic for reasoning about relational structures, studying statements about
necessity (`□φ`) and possibility `⋄φ`.

## References

* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001]
* The definitions of theory equivalence and the denotational semantics of worlds are inspired by
  the development of `Cslib.Logic.HML`.
-/

@[expose] public section

namespace Cslib.Logic.Modal

/-- A model consists of a relation between worlds `r` and a valuation `v`. -/
structure Model (World : Type*) (Atom : Type*) where
  /-- World accessibility relation. -/
  r : World → World → Prop
  /-- Valuation of atoms at a world. -/
  v : World → Atom → Prop

/-- Propositions. -/
inductive Proposition (Atom : Type u) : Type u where
  /-- Atomic proposition. -/
  | atom (p : Atom)
  /-- Negation. -/
  | neg (φ : Proposition Atom)
  /-- Conjunction. -/
  | and (φ₁ φ₂ : Proposition Atom)
  /-- Possibility. -/
  | diamond (φ : Proposition Atom)

@[inherit_doc] scoped prefix:40 "¬" => Proposition.neg
@[inherit_doc] scoped infix:36 " ∧ " => Proposition.and
@[inherit_doc] scoped prefix:40 "⋄" => Proposition.diamond

/-- Disjunction. -/
def Proposition.or (φ₁ φ₂ : Proposition Atom) : Proposition Atom := ¬(¬φ₁ ∧ ¬φ₂)

@[inherit_doc] scoped infix:35 " ∨ " => Proposition.or

/-- Implication. -/
def Proposition.impl (φ₁ φ₂ : Proposition Atom) : Proposition Atom := ¬φ₁ ∨ φ₂

@[inherit_doc] scoped infix:30 " → " => Proposition.impl

/-- Bi-implication. -/
@[simp, scoped grind =]
def Proposition.biImpl (φ₁ φ₂ : Proposition Atom) : Proposition Atom := (φ₁ → φ₂) ∧ (φ₂ → φ₁)

@[inherit_doc] scoped infix:30 " ↔ " => Proposition.biImpl

/-- Necessity. -/
def Proposition.box (φ : Proposition Atom) : Proposition Atom := ¬⋄¬φ

@[inherit_doc] scoped prefix:40 "□" => Proposition.box

/-- Satisfaction relation. `Satisfies m w φ` means that, in the model `m`, the world `w` satisfies
the proposition `φ`. -/
@[scoped grind]
def Satisfies (m : Model World Atom) (w : World) : Proposition Atom → Prop
  | .atom p => m.v w p
  | .neg φ => ¬Satisfies m w φ
  | .and φ₁ φ₂ => Satisfies m w φ₁ ∧ Satisfies m w φ₂
  | .diamond φ => ∃ w', m.r w w' ∧ Satisfies m w' φ

/-- Judgement, representing the conclusions one reaches in modal logic. -/
structure Judgement World Atom where
  /-- Constructs a judgement. -/
  mk ::
  /-- Model. -/
  m : Model World Atom
  /-- The world satisfying the proposition `φ`. -/
  w : World
  /-- The proposition satisfied by the world `w`. -/
  φ : Proposition Atom

@[inherit_doc] scoped notation m "," w " ⊨ " φ => Judgement.mk m w φ

/-- Satisfaction for judgements. This just refers to the unbundled `Satisfies`. -/
@[simp, scoped grind =]
def Satisfies.Bundled (j : Judgement World Atom) : Prop := Satisfies j.m j.w j.φ

instance : HasInferenceSystem (Judgement World Atom) := ⟨Satisfies.Bundled⟩

open scoped InferenceSystem Proposition

@[scoped grind =]
theorem derivation_def {m : Model World Atom} {w : World} {φ : Proposition Atom} :
  ⇓(m,w ⊨ φ) = Satisfies m w φ := rfl

/-- A world satisfies a proposition iff it does not satisfy the negation of the proposition. -/
@[scoped grind =]
theorem neg_satisfies : ⇓(m,w ⊨ ¬φ) ↔ ¬⇓(m,w ⊨ φ) := by
  induction φ generalizing w <;> grind

/-- Characterisation of the `∨` connective.

Disjunction is defined in terms of the more primitive connectives given in `Proposition`.
This result proves that the definition is correct. -/
@[scoped grind =]
theorem Satisfies.or_char {m : Model World Atom} :
    ⇓(m,w ⊨ φ₁ ∨ φ₂) ↔ ⇓(m,w ⊨ φ₁) ∨ ⇓(m,w ⊨ φ₂) := by grind [Proposition.or]

/-- Characterisation of the `→` connective.

Implication is defined in terms of the more primitive connectives given in `Proposition`.
This result proves that the definition is correct.
-/
@[scoped grind =]
theorem Satisfies.impl_char {m : Model World Atom} :
    ⇓(m,w ⊨ φ₁ → φ₂) ↔ (⇓(m,w ⊨ φ₁) → ⇓(m,w ⊨ φ₂)) := by grind [Proposition.impl]

/-- Characterisation of the `□` modality.

Necessity is defined in terms of the more primitive connectives given in `Proposition`.
This result proves that the definition is correct. -/
@[scoped grind =]
theorem Satisfies.box_char {m : Model World Atom} :
    ⇓(m,w ⊨ □φ) ↔ ∀ w', m.r w w' → ⇓(m,w' ⊨ φ) := by grind [Proposition.box]

/-- The theory of a world in a model is the set of all propositions that it satifies. -/
abbrev theory (m : Model World Atom) (w : World) : Set (Proposition Atom) :=
  {φ | ⇓(m,w ⊨ φ)}

/-- Two worlds are theory-equivalent under a model if they have the same theory. -/
abbrev TheoryEq (m : Model World Atom) (w₁ w₂ : World) :=
  theory m w₁ = theory m w₂

/-- Any proposition satisfied by a world is in the theory of that world. -/
@[scoped grind →]
theorem satisfies_theory (h : Satisfies m w φ) : φ ∈ theory m w := by grind

/-- If two worlds are not theory equivalent, there exists a distinguishing proposition. -/
lemma not_theoryEq_satisfies (h : ¬TheoryEq m w₁ w₂) :
    ∃ φ, (⇓(m,w₁ ⊨ φ) ∧ ¬⇓(m,w₂ ⊨ φ)) := by grind [=_ neg_satisfies]

/-- If two worlds are theory equivalent and the former satisfies a proposition, the latter does as
well. -/
theorem theoryEq_satisfies {m : Model World Atom} (h : TheoryEq m w₁ w₂)
    (hs : Satisfies m w₁ φ) : ⇓(m,w₂ ⊨ φ) := by
  unfold TheoryEq theory at h
  rw [Set.ext_iff] at h
  exact (h φ).mp hs

/-- The K axiom, valid for all models. -/
theorem Satisfies.k : ⇓(m,w ⊨ □(φ₁ → φ₂) → (□φ₁ → □φ₂)) := by grind

/-- The dual axiom, valid for all models. -/
theorem Satisfies.dual : ⇓(m,w ⊨ ⋄φ ↔ ¬□¬φ) := by
  constructor <;> grind

/-- The T axiom, valid for all reflexive models. -/
theorem Satisfies.t {m : Model World Atom} [instRefl : Std.Refl m.r] {w : World}
    (φ : Proposition Atom) : ⇓(m,w ⊨ φ → ⋄φ) := by grind [instRefl.refl w]

/-- Any model that admits the axiom T is reflexive. -/
theorem Satisfies.t_refl
    {r : World → World → Prop}
    [instAtomNonempty : Nonempty Atom]
    (h : ∀ {v : World → Atom → Prop} {w : World} {φ : Proposition Atom},
      ⇓((Model.mk r v),w ⊨ φ → ⋄φ)) :
    Std.Refl r where
  refl := by
    intro w
    have a := Classical.arbitrary Atom
    let v := fun (w' : World) (a : Atom) => w' = w
    let h' := h (v := v) (w := w) (φ := .atom a)
    grind

/-- In any reflexive model, `□φ → φ` is equivalent to `φ → ⋄φ`. -/
theorem Satisfies.t_box_diamond [instRefl : Std.Refl m.r] : ⇓(m,w ⊨ □φ → φ) ↔ ⇓(m,w ⊨ φ → ⋄φ) := by
  grind [instRefl.refl]

/-- The B axiom, valid for all symmetric models. -/
theorem Satisfies.b {m : Model World Atom} [instSymm : Std.Symm m.r] {w : World}
    (φ : Proposition Atom) : ⇓(m,w ⊨ φ → □⋄φ) := by
  grind [instSymm.symm w]

/-- Any model that admits the axiom B is symmetric. -/
theorem Satisfies.b_symm
    {r : World → World → Prop}
    [instAtomNonempty : Nonempty Atom]
    (h : ∀ {v : World → Atom → Prop} {w : World} {φ : Proposition Atom},
      ⇓(Model.mk r v,w ⊨ φ → □⋄φ)) :
    Std.Symm r where
  symm := by
    intro w₁
    have a := Classical.arbitrary Atom
    let v₁ := fun (w' : World) (a : Atom) => w' = w₁
    let h₁ := h (v := v₁) (w := w₁) (φ := .atom a)
    grind

/-- The 4 axiom, valid for all transitive models. -/
theorem Satisfies.four {m : Model World Atom} [instTrans : IsTrans World m.r] {w : World}
    (φ : Proposition Atom) : ⇓(m,w ⊨ ⋄⋄φ → ⋄φ) := by
  simp only [impl_char]
  intro h
  rcases h with ⟨w', h₁, w'', h₂, hs⟩
  exists w''
  grind [IsTrans]

/-- Any model that admits 4 is transitive. -/
theorem Satisfies.four_trans
    {r : World → World → Prop}
    [instAtomNonempty : Nonempty Atom]
    (h : ∀ {v : World → Atom → Prop} {w : World} {φ : Proposition Atom},
      ⇓(Model.mk r v,w ⊨ ⋄⋄φ → ⋄φ)) :
    IsTrans World r where
  trans := by
    intro w₁ w₂ w₃ h₁ h₂
    have a := Classical.arbitrary Atom
    let v := fun (w' : World) (a : Atom) => w' = w₃
    let h' := h (v := v) (w := w₁) (φ := .atom a)
    grind

/-- The 5 axiom, valid for all Euclidean models. -/
theorem Satisfies.five {m : Model World Atom} [instRightEuclidean : Relation.RightEuclidean m.r]
    {w : World}
    (φ : Proposition Atom) : ⇓(m,w ⊨ ⋄φ → □⋄φ) := by grind [Relation.RightEuclidean]

/-- Any model that admits 5 is Euclidean. -/
theorem Satisfies.five_rightEuclidean
    {r : World → World → Prop}
    [instAtomNonempty : Nonempty Atom]
    (h : ∀ {v : World → Atom → Prop} {w : World} {φ : Proposition Atom},
      ⇓(Model.mk r v,w ⊨ ⋄φ → □⋄φ)) :
    Relation.RightEuclidean r where
  rightEuclidean := by
    intro w₁ w₂ w₃ h₁ h₂
    have a := Classical.arbitrary Atom
    let v := fun (w' : World) (a : Atom) => w' = w₃
    let h' := h (v := v) (w := w₁) (φ := .atom a)
    grind

/-- The D axiom, valid for all serial models. -/
theorem Satisfies.d {m : Model World Atom} [instSerial : Relation.Serial m.r]
    {w : World}
    (φ : Proposition Atom) : ⇓(m,w ⊨ □φ → ⋄φ) := by
  have : ∃ w', m.r w w' := instSerial.serial w
  grind

/-- Any model that admits D is serial. -/
theorem Satisfies.d_serial
    {r : World → World → Prop}
    [instAtomNonempty : Nonempty Atom]
    (h : ∀ {v : World → Atom → Prop} {w : World} {φ : Proposition Atom},
      ⇓(Model.mk r v,w ⊨ □φ → ⋄φ)) :
    Relation.Serial r where
  serial := by
    intro w₁
    have a := Classical.arbitrary Atom
    let v := fun (w' : World) (a : Atom) => w' = w₁
    let h' := h (v := v) (w := w₁) (φ := .atom a)
    grind

/-- A proposition is valid in a class of models `S` (modelled as a set) if it is satisfied under
all models in `S` for all worlds. -/
@[simp, scoped grind =]
def Proposition.valid (S : Set (Model World Atom)) (φ : Proposition Atom) : Prop :=
  ∀ (m : Model World Atom), ∀ (_ : m ∈ S), ∀ (w : World), ⇓(m,w ⊨ φ)

/-- The modal logic of a class of models `S` is the set of all propositions valid in `S`. -/
@[simp, scoped grind =]
def logic (S : Set (Model World Atom)) : Set (Proposition Atom) :=
  {φ | φ.valid S}

end Cslib.Logic.Modal
