/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Marianna Girlando
-/

module

public import Mathlib.Data.PFunctor.Univariate.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Order.BooleanAlgebra.Set
public import Mathlib.Order.Defs.Unbundled
public import Cslib.Foundations.Relation.Euclidean
public import Cslib.Foundations.Logic.InferenceSystem
public import Cslib.Foundations.Logic.Operators
public import Cslib.Foundations.Relation.Defs
public import Cslib.Foundations.Syntax.HasSubstitution

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

-- class OpFamily (A : Type*) where
--   B : A → Type*

-- def HasPFunctor.toPFunctor (A : Type*) [HasPFunctor A] : PFunctor where
--   A := A
--   B := HasPFunctor.B

structure Frame World (τ : PFunctor) where
  /-- Accessibility relations. -/
  r : (op : τ.A) → World → (τ.B op → World) → Prop

/-- A model consists of a relation between worlds `r` and a valuation `v`. -/
structure Model World (τ : PFunctor) Atom extends Frame World τ where
  /-- Valuation of atoms at a world. -/
  v : World → Atom → Prop

/-- Propositions. -/
inductive Proposition (τ : PFunctor) Atom where
  /-- Atomic proposition. -/
  | atom (p : Atom)
  /-- Negation. -/
  | not (φ : Proposition τ Atom)
  /-- Conjunction. -/
  | and (φ₁ φ₂ : Proposition τ Atom)
  /-- Generalised possibility, or triangle. -/
  | triangle (op : τ.A) (φs : τ.B op → Proposition τ Atom)

/-- A map of propositions for the operator `op` in the polynomial functor `τ`. -/
abbrev PropositionMap τ op Atom := τ.B op → Proposition τ Atom

/-- Utility to coerce atoms into atomic propositions. -/
instance : Coe Atom (Proposition τ Atom) := ⟨.atom⟩

instance {τ : PFunctor} {Atom : Type*} : HasNot (Proposition τ Atom) := ⟨.not⟩
instance {τ : PFunctor} {Atom : Type*} : HasAnd (Proposition τ Atom) := ⟨.and⟩
instance {τ : PFunctor} {Atom : Type*} : HasTriangle (Proposition τ Atom) τ := ⟨.triangle⟩

-- TODO: diamond instance here

@[scoped grind =]
lemma Proposition.not_def (φ : Proposition τ Atom) : φ.not = ¬φ := rfl

-- @[scoped grind =]
-- lemma Proposition.not_all_def (φs : α → Proposition τ Atom) : (fun i => ¬(φs i)) = ¬φs := rfl

@[scoped grind =]
lemma Proposition.and_def (φ₁ φ₂ : Proposition τ Atom) : φ₁.and φ₂ = (φ₁ ∧ φ₂) := rfl

@[scoped grind =]
lemma Proposition.triangle_def {τ : PFunctor} (op : τ.A)
    (φs : τ.B op → Proposition τ Atom) : Proposition.triangle op φs = (Δ[op]φs) := rfl

-- @[scoped grind =]
-- lemma Proposition.diamond_def (φ : Proposition τ Atom) : φ.diamond = (◇φ) := rfl

/-- Disjunction. -/
def Proposition.or (φ₁ φ₂ : Proposition τ Atom) := ¬(¬φ₁ ∧ ¬φ₂)

instance {τ : PFunctor} {Atom : Type*} : HasOr (Proposition τ Atom) := ⟨Proposition.or⟩

@[scoped grind =]
lemma Proposition.or_def (φ₁ φ₂ : Proposition τ Atom) : φ₁.or φ₂ = (φ₁ ∨ φ₂) := rfl

/-- Implication. -/
def Proposition.imp (φ₁ φ₂ : Proposition τ Atom) := ¬φ₁ ∨ φ₂

instance {τ : PFunctor} {Atom : Type*} : HasImp (Proposition τ Atom) := ⟨.imp⟩

@[scoped grind =]
lemma Proposition.imp_def (φ₁ φ₂ : Proposition τ Atom) : φ₁.imp φ₂ = (φ₁ → φ₂) := rfl

/-- Bi-implication. -/
def Proposition.iff (φ₁ φ₂ : Proposition τ Atom) := (φ₁ → φ₂) ∧ (φ₂ → φ₁)

instance {τ : PFunctor} {Atom : Type*} : HasIff (Proposition τ Atom) := ⟨.iff⟩

@[scoped grind =]
lemma Proposition.iff_def (φ₁ φ₂ : Proposition τ Atom) : φ₁.iff φ₂ = (φ₁ ↔ φ₂) := rfl

def PropositionMap.not (φs : PropositionMap τ op Atom) := fun i => ¬φs i

instance {τ : PFunctor} {op : τ.A} {Atom : Type*} : HasNot (PropositionMap τ op Atom) := ⟨.not⟩

def PropositionMap.and (φs₁ φs₂ : PropositionMap τ op Atom) := fun i => φs₁ i ∧ φs₂ i

instance {τ : PFunctor} {op : τ.A} {Atom : Type*} : HasAnd (PropositionMap τ op Atom) := ⟨.and⟩

def PropositionMap.or (φs₁ φs₂ : PropositionMap τ op Atom) := fun i => φs₁ i ∨ φs₂ i

instance {τ : PFunctor} {op : τ.A} {Atom : Type*} : HasOr (PropositionMap τ op Atom) := ⟨.or⟩

def PropositionMap.imp (φs₁ φs₂ : PropositionMap τ op Atom) := fun i => φs₁ i → φs₂ i

instance {τ : PFunctor} {op : τ.A} {Atom : Type*} : HasImp (PropositionMap τ op Atom) := ⟨.imp⟩

def PropositionMap.iff (φs₁ φs₂ : PropositionMap τ op Atom) := fun i => φs₁ i ↔ φs₂ i

instance {τ : PFunctor} {op : τ.A} {Atom : Type*} : HasIff (PropositionMap τ op Atom) := ⟨.iff⟩

/-- Generalised necessity, or nabla (∇), dual of triangle. -/
def Proposition.nabla {τ : PFunctor} (op : τ.A) (φs : τ.B op → Proposition τ Atom) :=
  ¬Δ[op]¬φs

-- /-- Necessity. -/
-- def Proposition.box (φ : Proposition τ Atom) : Proposition τ Atom := ¬◇¬φ

-- instance : HasBox (Proposition τ Atom) := ⟨.box⟩

instance {τ : PFunctor} {Atom : Type*} : HasNabla (Proposition τ Atom) τ := ⟨.nabla⟩

-- @[scoped grind =]
-- lemma Proposition.box_def (φ : Proposition τ Atom) : φ.box = (□φ) := rfl

@[scoped grind =]
lemma Proposition.nabla_def {τ : PFunctor} (op : τ.A)
    (φs : τ.B op → Proposition τ Atom) : Proposition.nabla op φs = (∇[op]φs) := rfl

/-- Satisfaction relation. `Satisfies m w φ` means that, in the model `m`, the world `w` satisfies
the proposition `φ`. -/
def Satisfies (m : Model World τ Atom) (w : World) : Proposition τ Atom → Prop
  | .atom p => m.v w p
  | .not φ => ¬Satisfies m w φ
  | .and φ₁ φ₂ => Satisfies m w φ₁ ∧ Satisfies m w φ₂
  | .triangle op φs => ∃ ws : τ.B op → World, m.r op w ws ∧ ∀ i, Satisfies m (ws i) (φs i)
  -- ∃ w', m.r w w' ∧ Satisfies m w' φ

/-- Judgement, representing the conclusions one reaches in modal logic. -/
structure Judgement World τ Atom where
  /-- Constructs a judgement. -/
  mk ::
  /-- Model. -/
  m : Model World τ Atom
  /-- The world satisfying the proposition `φ`. -/
  w : World
  /-- The proposition satisfied by the world `w`. -/
  φ : Proposition τ Atom

@[inherit_doc] scoped notation "Modal[" m "," w " ⊨ " φ "]" => Judgement.mk m w φ

/-- Satisfaction for judgements. This just refers to the unbundled `Satisfies`. -/
def Satisfies.Bundled (j : Judgement World τ Atom) : Prop := Satisfies j.m j.w j.φ

instance {World : Type*} {τ : PFunctor} {Atom : Type*} :
    HasInferenceSystem (Judgement World τ Atom) := ⟨Satisfies.Bundled⟩

open scoped InferenceSystem Proposition

@[scoped grind =]
theorem derivation_def {m : Model World τ Atom} {w : World} {φ : Proposition τ Atom} :
  Satisfies m w φ = ⇓Modal[m,w ⊨ φ] := rfl

@[simp, scoped grind =, modal =]
theorem Satisfies.atom_iff {a : Atom} : ⇓Modal[m,w ⊨ a] ↔ m.v w a := by rfl

/-- A world satisfies a proposition iff it does not satisfy the negation of the proposition. -/
@[scoped grind =, modal =]
theorem Satisfies.not_iff_not : ⇓Modal[m,w ⊨ ¬φ] ↔ ¬⇓Modal[m,w ⊨ φ] := by rfl

@[scoped grind =, modal =]
theorem Satisfies.and_iff_and {m : Model World τ Atom} :
    ⇓Modal[m,w ⊨ φ₁ ∧ φ₂] ↔ ⇓Modal[m,w ⊨ φ₁] ∧ ⇓Modal[m,w ⊨ φ₂] := by rfl

-- @[scoped grind =]
-- theorem Satisfies.diamond_iff_exists {m : Model World τ Atom} :
--     ⇓Modal[m,w ⊨ ◇φ] ↔ ∃ w', m.r w w' ∧ ⇓Modal[m,w' ⊨ φ] := by rfl

@[scoped grind =]
theorem Satisfies.triangle_iff_exists {m : Model World τ Atom} :
    ⇓Modal[m,w ⊨ Δ[op]φs] ↔ ∃ ws, m.r op w ws ∧ ∀ i, ⇓Modal[m,(ws i) ⊨ (φs i)] := by rfl

@[scoped grind =]
theorem Satisfies.triangle_not_iff_exists_not {φs : τ.B op → Proposition τ Atom}
    {m : Model World τ Atom} : ⇓Modal[m,w ⊨ Δ[op]¬φs] ↔
      ∃ ws, m.r op w ws ∧ ∀ i, ¬⇓Modal[m,(ws i) ⊨ (φs i)] := by
  have : (¬φs) = (fun i => ¬(φs i)) := rfl
  grind

/-- Characterisation of the `∨` connective.

Disjunction is defined in terms of the more primitive connectives given in `Proposition`.
This result proves that the definition is correct. -/
@[scoped grind =, modal =]
theorem Satisfies.or_iff_or {m : Model World τ Atom} :
    ⇓Modal[m,w ⊨ φ₁ ∨ φ₂] ↔ ⇓Modal[m,w ⊨ φ₁] ∨ ⇓Modal[m,w ⊨ φ₂] := by
  grind [=_ Proposition.or_def, Proposition.or]

/-- Characterisation of the `→` connective.

Implication is defined in terms of the more primitive connectives given in `Proposition`.
This result proves that the definition is correct.
-/
@[scoped grind =, modal =]
theorem Satisfies.imp_iff_imp {m : Model World τ Atom} :
    ⇓Modal[m,w ⊨ φ₁ → φ₂] ↔ (⇓Modal[m,w ⊨ φ₁] → ⇓Modal[m,w ⊨ φ₂]) := by
  grind [=_ Proposition.imp_def, Proposition.imp]

/-- Characterisation of the `↔` connective.

Bi-implication is defined in terms of the more primitive connectives given in `Proposition`.
This result proves that the definition is correct. -/
@[scoped grind =, modal =]
theorem Satisfies.iff_iff_iff {m : Model World τ Atom} :
    ⇓Modal[m,w ⊨ φ₁ ↔ φ₂] ↔ (⇓Modal[m,w ⊨ φ₁] ↔ ⇓Modal[m,w ⊨ φ₂]) := by
  simp only [HasIff.iff, Proposition.iff]
  grind

/-- Characterisation of `∇`.

Necessity is defined in terms of the more primitive connectives given in `Proposition`.
This result proves that the definition is correct. -/
@[scoped grind =]
theorem Satisfies.nabla_iff_forall {m : Model World τ Atom} :
    ⇓Modal[m,w ⊨ ∇[op]φs] ↔ ∀ ws, m.r op w ws → ∃ i, ⇓Modal[m,(ws i) ⊨ (φs i)] := by
  grind [=_ Proposition.nabla_def, Proposition.nabla]

-- /-- Characterisation of the `□` modality.

-- Necessity is defined in terms of the more primitive connectives given in `Proposition`.
-- This result proves that the definition is correct. -/
-- @[scoped grind =]
-- theorem Satisfies.box_iff_forall {m : Model World Atom} :
--     ⇓Modal[m,w ⊨ □φ] ↔ ∀ w', m.r w w' → ⇓Modal[m,w' ⊨ φ] := by
--   grind [=_ Proposition.box_def, Proposition.box]

/-- The theory of a world in a model is the set of all propositions that it satisfies. -/
abbrev theory {World : Type*} {τ : PFunctor} {Atom : Type*} (m : Model World τ Atom)
    (w : World) : Set (Proposition τ Atom) := {φ | ⇓Modal[m,w ⊨ φ]}

/-- Two worlds are theory-equivalent under a model if they have the same theory. -/
abbrev TheoryEq (m : Model World τ Atom) (w₁ w₂ : World) :=
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
theorem theoryEq_satisfies {m : Model World τ Atom} (h : TheoryEq m w₁ w₂)
    (hs : Satisfies m w₁ φ) : ⇓Modal[m,w₂ ⊨ φ] := by
  apply TheoryEq.ext_iff.1 at h
  exact (h φ).mp hs

/-- Every accessibility relation induces an inference system tag for proving valid axioms under
the relation. -/
inductive Axiom (f : Frame World τ)

/-- A proposition `φ` is an axiom under the relation `r` (the 'frame') if it holds for all
valuations and worlds. -/
instance {World : Type*} {τ : PFunctor} {Atom : Type*} (f : Frame World τ) :
    InferenceSystem (Axiom f) (Proposition τ Atom) where
  derivation φ := ∀ v w, ⇓Modal[⟨f,v⟩,w ⊨ φ]

@[scoped grind ⇒]
theorem Satisfies.axiom_def (f : Frame World τ) :
    (∀ v w, ⇓Modal[⟨f,v⟩,w ⊨ φ]) ↔ Axiom f⇓φ := by rfl

@[modal .]
theorem Satisfies.der_of_axiom (h : Axiom m.toFrame⇓φ) : ⇓Modal[m,w ⊨ φ] := h m.v w

/-- If a proposition is an axiom under the relation of a model, it is satisfied by every world. -/
@[scoped grind .]
theorem Satisfies.of_axiom (m : Model World τ Atom) (φ : Proposition τ Atom) (h : Axiom m.toFrame⇓φ)
    (w : World) : ⇓Modal[m,w ⊨ φ] := h m.v w

@[scoped grind =]
theorem Satisfies.subst_apply_iff [DecidableEq (τ.B op)] {φs : PropositionMap τ op Atom}
    {i j : τ.B op} {φ : Proposition τ Atom} : ⇓Modal[m,w ⊨ φs[i := φ] j] ↔
      (j = i ∧ ⇓Modal[m,w ⊨ φ]) ∨ (j ≠ i ∧ ⇓Modal[m,w ⊨ φs j]) :=
  Function.pred_update (P := fun _ φ' => Satisfies m w φ') φs i φ j

/-- The K axiom, valid for all models. -/
-- @[scoped grind ., modal .]
-- theorem Satisfies.k (f : Frame World τ) (φ₁ φ₂ : Proposition τ Atom) :
--     Axiom f⇓(□(φ₁ → φ₂) → (□φ₁ → □φ₂)) := by grind
@[scoped grind ., modal .]
theorem Satisfies.k (f : Frame World τ) {φs : PropositionMap τ op Atom} [DecidableEq (τ.B op)]
    {i : τ.B op} {φ₁ φ₂ : Proposition τ Atom} :
    Axiom f⇓(∇[op]φs[i := φ₁ → φ₂] → (∇[op]φs[i := φ₁] → ∇[op]φs[i := φ₂])) := by
  grind

/-- The dual axiom, valid for all models. -/
-- theorem Satisfies.dual {φs : τ.B op → Proposition τ Atom} (f : Frame World τ) :
--     Axiom f⇓(◇φ ↔ ¬□¬φ) := by
--   intro _ w
--   simp only [Satisfies.iff_iff_iff]
--   constructor
--   · grind
--   · grind only [= not_iff_not, = diamond_iff_exists, = box_iff_forall]
theorem Satisfies.dual (f : Frame World τ) {φs : τ.B op → Proposition τ Atom} :
    Axiom f⇓(Δ[op]φs ↔ ¬∇[op]¬φs) := by
  intro _ w
  simp only [Satisfies.iff_iff_iff]
  constructor
  · grind
  · grind only [= not_iff_not, = triangle_iff_exists, = nabla_iff_forall]

/-- Possibility preserves conjunction in all models. -/
@[modal .]
theorem Satisfies.diamond_and (f : Frame World τ) (φ₁ φ₂ : Proposition τ Atom) :
    Axiom f⇓((φ₁ ∧ φ₂) → (◇φ₁ ∧ ◇φ₂)) := by grind

/-- Possibility can be combined with necessity. -/
@[modal .]
theorem Satisfies.diamond_and_box (f : Frame World τ) (φ₁ φ₂ : Proposition τ Atom) :
    Axiom f⇓((◇φ₁ ∧ □φ₂) → ◇(φ₁ ∧ φ₂)) := by grind

/-- If `φ₁` is necessary and some successor exists, then some successor satisfies `φ₁`. -/
@[scoped grind ., modal .]
theorem Satisfies.diamond_of_box {φ₁ φ₂ : Proposition τ Atom} :
    Axiom f⇓(□φ₁ ∧ ◇φ₂ → ◇φ₁) := by grind

/-- The T axiom, valid for all reflexive models. -/
theorem Satisfies.t (f : Frame World τ) [instRefl : Std.Refl r] (φ : Proposition τ Atom)
    : Axiom f⇓(φ → ◇φ) := by
  grind [instRefl.refl]

/-- Any model that admits the axiom T is reflexive. -/
theorem Satisfies.t_refl (f : Frame World τ) [Nonempty Atom]
    (h : ∀ φ : Proposition τ Atom, Axiom f⇓(φ → ◇φ)) : Std.Refl r where
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
theorem Satisfies.b (f : Frame World τ) [Std.Symm r] (φ : Proposition τ Atom) :
    Axiom f⇓(φ → □◇φ) := by
  intro _ w
  have := Std.Symm.symm (r := r) w
  grind

/-- Any model that admits the axiom B is symmetric. -/
theorem Satisfies.b_symm (f : Frame World τ) [Nonempty Atom]
    (h : ∀ φ : Proposition τ Atom, Axiom f⇓(φ → □◇φ)) : Std.Symm r where
  symm w₁ := by
    have a := Classical.arbitrary Atom
    let v₁ := fun (w' : World) (a : Atom) => w' = w₁
    let h₁ := h (v := v₁) (w := w₁) (φ := a)
    grind

/-- The 4 axiom, valid for all transitive models. -/
theorem Satisfies.four (f : Frame World τ) [IsTrans World r]
    (φ : Proposition τ Atom) : Axiom f⇓(◇◇φ → ◇φ) := by
  intro _ _
  simp only [imp_iff_imp]
  intro h
  rcases h with ⟨w', h₁, w'', h₂, hs⟩
  exact ⟨w'', IsTrans.trans _ _ _ h₁ h₂, hs⟩

/-- Any model that admits 4 is transitive. -/
theorem Satisfies.four_trans (f : Frame World τ) [Nonempty Atom]
    (h : ∀ (φ : Proposition τ Atom), Axiom f⇓(◇◇φ → ◇φ)) : IsTrans World r where
  trans w₁ w₂ w₃ h₁ h₂ := by
    have a := Classical.arbitrary Atom
    let v := fun (w' : World) (a : Atom) => w' = w₃
    let h' := h (v := v) (w := w₁) (φ := a)
    grind

/-- The 5 axiom, valid for all Euclidean models. -/
theorem Satisfies.five (f : Frame World τ) [Relation.RightEuclidean r]
    (φ : Proposition τ Atom) : Axiom f⇓(◇φ → □◇φ) := by
  have := @Relation.RightEuclidean.rightEuclidean (r := r)
  grind

/-- Any model that admits 5 is Euclidean. -/
theorem Satisfies.five_rightEuclidean (f : Frame World τ) [Nonempty Atom]
    (h : ∀ φ : Proposition τ Atom, Axiom f⇓(◇φ → □◇φ)) :
    Relation.RightEuclidean r where
  rightEuclidean {w₁ w₂ w₃} h₁ h₂ := by
    have a := Classical.arbitrary Atom
    let v := fun (w' : World) (a : Atom) => w' = w₃
    let h' := h (v := v) (w := w₁) (φ := a)
    grind

/-- The D axiom, valid for all serial models. -/
theorem Satisfies.d (f : Frame World τ) [Relation.Serial r] (φ : Proposition τ Atom) :
    Axiom f⇓(□φ → ◇φ) := by
  intro _ w
  have : ∃ w', r w w' := Relation.Serial.serial w
  grind

/-- Any model that admits D is serial. -/
theorem Satisfies.d_serial (f : Frame World τ) [Nonempty Atom]
    (h : ∀ φ : Proposition τ Atom, Axiom f⇓(□φ → ◇φ)) : Relation.Serial r where
  serial w₁ := by
    have a := Classical.arbitrary Atom
    let v := fun (w' : World) (a : Atom) => w' = w₁
    let h' := h (v := v) (w := w₁) (φ := a)
    grind

/-- The L axiom, or Löb's theorem, valid for all transitive and converse well-founded models. -/
theorem Satisfies.l (f : Frame World τ) [IsTrans World r]
    (hwf : Relation.Terminating r) (φ : Proposition τ Atom) : Axiom f⇓(□(□φ → φ) → □φ) := by
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
theorem Satisfies.pointTwo (f : Frame World τ) (h : Diamond r)
    (φ : Proposition τ Atom) : Axiom f⇓(◇□φ → □◇φ) := by
  simp_rw [← Satisfies.axiom_def, Satisfies.imp_iff_imp, Satisfies.diamond_iff_exists,
    Satisfies.box_iff_forall]
  rintro v w ⟨_, hww₁, _⟩ _ hww₂
  obtain ⟨w₃, hww₃⟩ := h hww₁ hww₂
  grind

open Relation in
/-- Any model that admits axiom .2 has the diamond property. -/
theorem Satisfies.pointTwo_diamond (f : Frame World τ) [Nonempty Atom]
    (h : ∀ φ : Proposition τ Atom, Axiom f⇓(◇□φ → □◇φ)) : Diamond r := by
  intro w w₁ w₂ hww₁ hww₂
  specialize h (Classical.arbitrary Atom) (fun w' _ => r w₁ w') w
  grind [Join]

/-- A proposition is valid in a class of models `S` (modelled as a set) if it is satisfied under
all models in `S` for all worlds. -/
@[simp, scoped grind =]
def Proposition.valid (S : Set (Model World Atom)) (φ : Proposition τ Atom) : Prop :=
  ∀ (m : Model World Atom), ∀ (_ : m ∈ S), ∀ (w : World), ⇓Modal[m,w ⊨ φ]

/-- The modal logic of a class of models `S` is the set of all propositions valid in `S`. -/
@[simp, scoped grind =]
def logic (S : Set (Model World Atom)) : Set (Proposition τ Atom) :=
  {φ | φ.valid S}

/-- Modal logic is antitone (wrt the class of models). -/
theorem logic_antitone : Antitone (logic (World := World) (Atom := Atom)) :=
  fun _ _ hS₁S₂ _ hφ m hm w => hφ m (hS₁S₂ hm) w

/-- The class of all models generated by a frame (relation). -/
abbrev modelsOfRelation (f : Frame World τ) : Set (Model World Atom) :=
  {m | m.r = r}

/-- A proposition is an axiom of a frame exactly when it belongs to the logic of all models over
that frame. -/
theorem axiom_iff_mem_logic_modelsOfRelation (f : Frame World τ) (φ : Proposition τ Atom) :
    Axiom f⇓φ ↔ φ ∈ logic (modelsOfRelation r) := by
  constructor
  case mp =>
    rintro h m rfl w
    exact h m.v w
  case mpr => grind [Satisfies.axiom_def]

end Cslib.Logic.Modal
