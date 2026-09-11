/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Marianna Girlando
-/

module

public import Mathlib.Data.Set.Basic
public import Mathlib.Order.Defs.Unbundled
public import Cslib.Foundations.Relation.Euclidean
public import Cslib.Foundations.Logic.InferenceSystem
public import Cslib.Foundations.Logic.Operators
public import Cslib.Foundations.Relation.Defs
public import Mathlib.Order.BooleanAlgebra.Set

/-! # Modal Logic

Modal logic is a logic for reasoning about relational structures, studying statements about
necessity (`□φ`) and possibility (`◇φ`).

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
  | not (φ : Proposition Atom)
  /-- Conjunction. -/
  | and (φ₁ φ₂ : Proposition Atom)
  /-- Possibility. -/
  | diamond (φ : Proposition Atom)

/-- Utility to coerce atoms into atomic propositions. -/
instance : Coe Atom (Proposition Atom) := ⟨.atom⟩

instance : HasNot (Proposition Atom) := ⟨.not⟩
instance : HasAnd (Proposition Atom) := ⟨.and⟩
instance : HasDiamond (Proposition Atom) := ⟨.diamond⟩

@[scoped grind =]
lemma Proposition.not_def (φ : Proposition Atom) : φ.not = ¬φ := rfl

@[scoped grind =]
lemma Proposition.and_def (φ₁ φ₂ : Proposition Atom) : φ₁.and φ₂ = (φ₁ ∧ φ₂) := rfl

@[scoped grind =]
lemma Proposition.diamond_def (φ : Proposition Atom) : φ.diamond = (◇φ) := rfl

/-- Disjunction. -/
def Proposition.or (φ₁ φ₂ : Proposition Atom) : Proposition Atom := ¬(¬φ₁ ∧ ¬φ₂)

instance : HasOr (Proposition Atom) := ⟨Proposition.or⟩

@[scoped grind =]
lemma Proposition.or_def (φ₁ φ₂ : Proposition Atom) : φ₁.or φ₂ = (φ₁ ∨ φ₂) := rfl

/-- Implication. -/
def Proposition.imp (φ₁ φ₂ : Proposition Atom) : Proposition Atom := ¬φ₁ ∨ φ₂

instance : HasImp (Proposition Atom) := ⟨.imp⟩

@[scoped grind =]
lemma Proposition.imp_def (φ₁ φ₂ : Proposition Atom) : φ₁.imp φ₂ = (φ₁ → φ₂) := rfl

/-- Bi-implication. -/
def Proposition.iff (φ₁ φ₂ : Proposition Atom) : Proposition Atom := (φ₁ → φ₂) ∧ (φ₂ → φ₁)

instance : HasIff (Proposition Atom) := ⟨.iff⟩

@[scoped grind =]
lemma Proposition.iff_def (φ₁ φ₂ : Proposition Atom) :
    φ₁.iff φ₂ = (φ₁ ↔ φ₂) := rfl

/-- Necessity. -/
def Proposition.box (φ : Proposition Atom) : Proposition Atom := ¬◇¬φ

instance : HasBox (Proposition Atom) := ⟨.box⟩

@[scoped grind =]
lemma Proposition.box_def (φ : Proposition Atom) : φ.box = (□φ) := rfl

/-- Satisfaction relation. `Satisfies m w φ` means that, in the model `m`, the world `w` satisfies
the proposition `φ`. -/
def Satisfies (m : Model World Atom) (w : World) : Proposition Atom → Prop
  | .atom p => m.v w p
  | .not φ => ¬Satisfies m w φ
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

@[inherit_doc] scoped notation "Modal[" m "," w " ⊨ " φ "]" => Judgement.mk m w φ

/-- Satisfaction for judgements. This just refers to the unbundled `Satisfies`. -/
def Satisfies.Bundled (j : Judgement World Atom) : Prop := Satisfies j.m j.w j.φ

instance : HasInferenceSystem (Judgement World Atom) := ⟨Satisfies.Bundled⟩

open scoped InferenceSystem Proposition

@[scoped grind =]
theorem derivation_def {m : Model World Atom} {w : World} {φ : Proposition Atom} :
  Satisfies m w φ = ⇓Modal[m,w ⊨ φ] := rfl

@[simp, scoped grind =, modal =]
theorem Satisfies.atom_iff {a : Atom} : ⇓Modal[m,w ⊨ a] ↔ m.v w a := by rfl

/-- A world satisfies a proposition iff it does not satisfy the negation of the proposition. -/
@[scoped grind =, modal =]
theorem Satisfies.not_iff_not : ⇓Modal[m,w ⊨ ¬φ] ↔ ¬⇓Modal[m,w ⊨ φ] := by rfl

@[scoped grind =, modal =]
theorem Satisfies.and_iff_and {m : Model World Atom} :
    ⇓Modal[m,w ⊨ φ₁ ∧ φ₂] ↔ ⇓Modal[m,w ⊨ φ₁] ∧ ⇓Modal[m,w ⊨ φ₂] := by rfl

@[scoped grind =]
theorem Satisfies.diamond_iff_exists {m : Model World Atom} :
    ⇓Modal[m,w ⊨ ◇φ] ↔ ∃ w', m.r w w' ∧ ⇓Modal[m,w' ⊨ φ] := by rfl

/-- Characterisation of the `∨` connective.

Disjunction is defined in terms of the more primitive connectives given in `Proposition`.
This result proves that the definition is correct. -/
@[scoped grind =, modal =]
theorem Satisfies.or_iff_or {m : Model World Atom} :
    ⇓Modal[m,w ⊨ φ₁ ∨ φ₂] ↔ ⇓Modal[m,w ⊨ φ₁] ∨ ⇓Modal[m,w ⊨ φ₂] := by
  grind [=_ Proposition.or_def, Proposition.or]

/-- Characterisation of the `→` connective.

Implication is defined in terms of the more primitive connectives given in `Proposition`.
This result proves that the definition is correct.
-/
@[scoped grind =, modal =]
theorem Satisfies.imp_iff_imp {m : Model World Atom} :
    ⇓Modal[m,w ⊨ φ₁ → φ₂] ↔ (⇓Modal[m,w ⊨ φ₁] → ⇓Modal[m,w ⊨ φ₂]) := by
  grind [=_ Proposition.imp_def, Proposition.imp]

/-- Characterisation of the `↔` connective.

Bi-implication is defined in terms of the more primitive connectives given in `Proposition`.
This result proves that the definition is correct. -/
@[scoped grind =, modal =]
theorem Satisfies.iff_iff_iff {m : Model World Atom} :
    ⇓Modal[m,w ⊨ φ₁ ↔ φ₂] ↔ (⇓Modal[m,w ⊨ φ₁] ↔ ⇓Modal[m,w ⊨ φ₂]) := by
  simp only [HasIff.iff, Proposition.iff]
  grind

/-- Characterisation of the `□` modality.

Necessity is defined in terms of the more primitive connectives given in `Proposition`.
This result proves that the definition is correct. -/
@[scoped grind =]
theorem Satisfies.box_iff_forall {m : Model World Atom} :
    ⇓Modal[m,w ⊨ □φ] ↔ ∀ w', m.r w w' → ⇓Modal[m,w' ⊨ φ] := by
  grind [=_ Proposition.box_def, Proposition.box]

/-- The theory of a world in a model is the set of all propositions that it satisfies. -/
abbrev theory (m : Model World Atom) (w : World) : Set (Proposition Atom) :=
  {φ | ⇓Modal[m,w ⊨ φ]}

/-- Two worlds are theory-equivalent under a model if they have the same theory. -/
abbrev TheoryEq (m : Model World Atom) (w₁ w₂ : World) :=
  theory m w₁ = theory m w₂

theorem TheoryEq.ext_iff : TheoryEq m w₁ w₂ ↔ (∀ φ, φ ∈ theory m w₁ ↔ φ ∈ theory m w₂) := by
  grind

/-- Any proposition satisfied by a world is in the theory of that world. -/
@[scoped grind →]
theorem satisfies_theory (h : ⇓Modal[m,w ⊨ φ]) : φ ∈ theory m w := by grind

/-- If two worlds are not theory equivalent, there exists a distinguishing proposition. -/
lemma not_theoryEq_satisfies (h : ¬TheoryEq m w₁ w₂) :
    ∃ φ, (⇓Modal[m,w₁ ⊨ φ] ∧ ¬⇓Modal[m,w₂ ⊨ φ]) := by grind [=_ Satisfies.not_iff_not]

/-- If two worlds are theory equivalent and the former satisfies a proposition, the latter does as
well. -/
theorem theoryEq_satisfies {m : Model World Atom} (h : TheoryEq m w₁ w₂)
    (hs : Satisfies m w₁ φ) : ⇓Modal[m,w₂ ⊨ φ] := by
  apply TheoryEq.ext_iff.1 at h
  exact (h φ).mp hs

/-- Every accessibility relation induces an inference system tag for proving valid axioms under
the relation. -/
inductive Axiom (r : World → World → Prop)

/-- A proposition `φ` is an axiom under the relation `r` (the 'frame') if it holds for all
valuations and worlds. -/
instance (r : World → World → Prop) : InferenceSystem (Axiom r) (Proposition Atom) where
  derivation φ := ∀ v w, ⇓Modal[⟨r,v⟩,w ⊨ φ]

@[scoped grind ⇒]
theorem Satisfies.axiom_def (r : World → World → Prop) :
    (∀ v w, ⇓Modal[⟨r,v⟩,w ⊨ φ]) ↔ Axiom r⇓φ := by rfl

@[modal .]
theorem Satisfies.der_of_axiom (h : Axiom m.r⇓φ) : ⇓Modal[m,w ⊨ φ] := h m.v w

/-- If a proposition is an axiom under the relation of a model, it is satisfied by every world. -/
@[scoped grind .]
theorem Satisfies.of_axiom (m : Model World Atom) (φ : Proposition Atom) (h : Axiom m.r⇓φ)
    (w : World) : ⇓Modal[m,w ⊨ φ] := h m.v w

/-- The K axiom, valid for all models. -/
@[scoped grind ., modal .]
theorem Satisfies.k (r : World → World → Prop) (φ₁ φ₂ : Proposition Atom) :
    Axiom r⇓(□(φ₁ → φ₂) → (□φ₁ → □φ₂)) := by grind

/-- The dual axiom, valid for all models. -/
theorem Satisfies.dual (r : World → World → Prop) (φ : Proposition Atom) :
    Axiom r⇓(◇φ ↔ ¬□¬φ) := by
  intro _ w
  simp only [Satisfies.iff_iff_iff]
  constructor
  · grind
  · grind only [= not_iff_not, = diamond_iff_exists, = box_iff_forall]

/-- Possibility preserves conjunction in all models. -/
@[modal .]
theorem Satisfies.diamond_and (r : World → World → Prop) (φ₁ φ₂ : Proposition Atom) :
    Axiom r⇓(◇(φ₁ ∧ φ₂) → (◇φ₁ ∧ ◇φ₂)) := by grind

/-- Possibility can be combined with necessity. -/
@[modal .]
theorem Satisfies.diamond_and_box (r : World → World → Prop) (φ₁ φ₂ : Proposition Atom) :
    Axiom r⇓((◇φ₁ ∧ □φ₂) → ◇(φ₁ ∧ φ₂)) := by grind

/-- If `φ₁` is necessary and some successor exists, then some successor satisfies `φ₁`. -/
@[scoped grind ., modal .]
theorem Satisfies.diamond_of_box {φ₁ φ₂ : Proposition Atom} :
    Axiom r⇓(□φ₁ ∧ ◇φ₂ → ◇φ₁) := by grind

/-- The T axiom, valid for all reflexive models. -/
theorem Satisfies.t (r : World → World → Prop) [instRefl : Std.Refl r] (φ : Proposition Atom)
    : Axiom r⇓(φ → ◇φ) := by
  grind [instRefl.refl]

/-- Any model that admits the axiom T is reflexive. -/
theorem Satisfies.t_refl (r : World → World → Prop) [Nonempty Atom]
    (h : ∀ φ : Proposition Atom, Axiom r⇓(φ → ◇φ)) : Std.Refl r where
  refl w := by
    have a := Classical.arbitrary Atom
    let v := fun (w' : World) (a : Atom) => w' = w
    let h' := h (v := v) (w := w) (φ := a)
    grind

/-- In any reflexive model, `□φ → φ` is equivalent to `φ → ◇φ`. -/
theorem Satisfies.t_box_diamond [Std.Refl m.r] : ⇓Modal[m,w ⊨ □φ → φ] ↔ ⇓Modal[m,w ⊨ φ → ◇φ] := by
  have := Std.Refl.refl (r := m.r) w
  grind

/-- The B axiom, valid for all symmetric models. -/
theorem Satisfies.b (r : World → World → Prop) [Std.Symm r] (φ : Proposition Atom) :
    Axiom r⇓(φ → □◇φ) := by
  intro _ w
  have := Std.Symm.symm (r := r) w
  grind

/-- Any model that admits the axiom B is symmetric. -/
theorem Satisfies.b_symm (r : World → World → Prop) [Nonempty Atom]
    (h : ∀ φ : Proposition Atom, Axiom r⇓(φ → □◇φ)) : Std.Symm r where
  symm w₁ := by
    have a := Classical.arbitrary Atom
    let v₁ := fun (w' : World) (a : Atom) => w' = w₁
    let h₁ := h (v := v₁) (w := w₁) (φ := a)
    grind

/-- The 4 axiom, valid for all transitive models. -/
theorem Satisfies.four (r : World → World → Prop) [IsTrans World r]
    (φ : Proposition Atom) : Axiom r⇓(◇◇φ → ◇φ) := by
  intro _ _
  simp only [imp_iff_imp]
  intro h
  rcases h with ⟨w', h₁, w'', h₂, hs⟩
  exact ⟨w'', IsTrans.trans _ _ _ h₁ h₂, hs⟩

/-- Any model that admits 4 is transitive. -/
theorem Satisfies.four_trans (r : World → World → Prop) [Nonempty Atom]
    (h : ∀ (φ : Proposition Atom), Axiom r⇓(◇◇φ → ◇φ)) : IsTrans World r where
  trans w₁ w₂ w₃ h₁ h₂ := by
    have a := Classical.arbitrary Atom
    let v := fun (w' : World) (a : Atom) => w' = w₃
    let h' := h (v := v) (w := w₁) (φ := a)
    grind

/-- The 5 axiom, valid for all Euclidean models. -/
theorem Satisfies.five (r : World → World → Prop) [Relation.RightEuclidean r]
    (φ : Proposition Atom) : Axiom r⇓(◇φ → □◇φ) := by
  have := @Relation.RightEuclidean.rightEuclidean (r := r)
  grind

/-- Any model that admits 5 is Euclidean. -/
theorem Satisfies.five_rightEuclidean (r : World → World → Prop) [Nonempty Atom]
    (h : ∀ φ : Proposition Atom, Axiom r⇓(◇φ → □◇φ)) :
    Relation.RightEuclidean r where
  rightEuclidean {w₁ w₂ w₃} h₁ h₂ := by
    have a := Classical.arbitrary Atom
    let v := fun (w' : World) (a : Atom) => w' = w₃
    let h' := h (v := v) (w := w₁) (φ := a)
    grind

/-- The D axiom, valid for all serial models. -/
theorem Satisfies.d (r : World → World → Prop) [Relation.Serial r] (φ : Proposition Atom) :
    Axiom r⇓(□φ → ◇φ) := by
  intro _ w
  have : ∃ w', r w w' := Relation.Serial.serial w
  grind

/-- Any model that admits D is serial. -/
theorem Satisfies.d_serial (r : World → World → Prop) [Nonempty Atom]
    (h : ∀ φ : Proposition Atom, Axiom r⇓(□φ → ◇φ)) : Relation.Serial r where
  serial w₁ := by
    have a := Classical.arbitrary Atom
    let v := fun (w' : World) (a : Atom) => w' = w₁
    let h' := h (v := v) (w := w₁) (φ := a)
    grind

/-- The L axiom, or Löb's theorem, valid for all transitive and converse well-founded models. -/
theorem Satisfies.l (r : World → World → Prop) [IsTrans World r]
    (hwf : Relation.Terminating r) (φ : Proposition Atom) : Axiom r⇓(□(□φ → φ) → □φ) := by
  intro v w
  let m := Model.mk r v
  simp_rw [Satisfies.imp_iff_imp, Satisfies.box_iff_forall]
  intro h
  refine (hwf.induction (C := fun w' => m.r w w' → ⇓Modal[m,w' ⊨ φ]) · ?_)
  intro w' ih hww'
  have hImp : ⇓Modal[m, w' ⊨ □φ → φ] := h _ hww'
  rw [Satisfies.imp_iff_imp, Satisfies.box_iff_forall] at hImp
  apply hImp
  intro w'' hw'w''
  apply ih _ hw'w''
  exact IsTrans.trans _ _ _ hww' hw'w''

/-- Löb induction, via the L axiom. -/
theorem Satisfies.l_induction (m : Model World Atom) [IsTrans World m.r]
    (hwf : Relation.Terminating m.r) (hstep : ∀ w, ⇓Modal[m,w ⊨ □φ → φ]) (w : World) :
    ⇓Modal[m, w ⊨ φ] := by
  have hl := Satisfies.of_axiom m _ (Satisfies.l m.r hwf φ) w
  /- We use `grind only` here as a memo and test that the `modal` grind set should be able to derive
    (the modal part of) this proof. -/
  grind only [modal, = box_iff_forall]

open Relation in
/-- Axiom .2, valid for all frames with the diamond property. -/
theorem Satisfies.pointTwo (r : World → World → Prop) (h : Diamond r)
    (φ : Proposition Atom) : Axiom r⇓(◇□φ → □◇φ) := by
  simp_rw [← Satisfies.axiom_def, Satisfies.imp_iff_imp, Satisfies.diamond_iff_exists,
    Satisfies.box_iff_forall]
  rintro v w ⟨_, hww₁, _⟩ _ hww₂
  obtain ⟨w₃, hww₃⟩ := h hww₁ hww₂
  grind

open Relation in
/-- Any model that admits axiom .2 has the diamond property. -/
theorem Satisfies.pointTwo_diamond (r : World → World → Prop) [Nonempty Atom]
    (h : ∀ φ : Proposition Atom, Axiom r⇓(◇□φ → □◇φ)) : Diamond r := by
  intro w w₁ w₂ hww₁ hww₂
  specialize h (Classical.arbitrary Atom) (fun w' _ => r w₁ w') w
  grind [Join]

/-- A proposition is valid in a class of models `S` (modelled as a set) if it is satisfied under
all models in `S` for all worlds. -/
@[simp, scoped grind =]
def Proposition.valid (S : Set (Model World Atom)) (φ : Proposition Atom) : Prop :=
  ∀ (m : Model World Atom), ∀ (_ : m ∈ S), ∀ (w : World), ⇓Modal[m,w ⊨ φ]

/-- The modal logic of a class of models `S` is the set of all propositions valid in `S`. -/
@[simp, scoped grind =]
def logic (S : Set (Model World Atom)) : Set (Proposition Atom) :=
  {φ | φ.valid S}

/-- Modal logic is antitone (wrt the class of models). -/
theorem logic_antitone : Antitone (logic (World := World) (Atom := Atom)) :=
  fun _ _ hS₁S₂ _ hφ m hm w => hφ m (hS₁S₂ hm) w

/-- The class of all models generated by a frame (relation). -/
abbrev modelsOfRelation (r : World → World → Prop) : Set (Model World Atom) :=
  {m | m.r = r}

/-- A proposition is an axiom of a frame exactly when it belongs to the logic of all models over
that frame. -/
theorem axiom_iff_mem_logic_modelsOfRelation (r : World → World → Prop) (φ : Proposition Atom) :
    Axiom r⇓φ ↔ φ ∈ logic (modelsOfRelation r) := by
  constructor
  case mp =>
    rintro h m rfl w
    exact h m.v w
  case mpr => grind [Satisfies.axiom_def]

end Cslib.Logic.Modal
