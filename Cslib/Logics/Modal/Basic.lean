/-
Copyright (c) 2026 Fabrizio Montesi, Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Marianna Girlando, Benjamin Brast-McKie
-/

module

public import Cslib.Init
public import Cslib.Foundations.Logic.Connectives
public import Cslib.Foundations.Logic.InferenceSystem
public import Mathlib.Data.Set.Basic
public import Mathlib.Order.Defs.Unbundled
public import Cslib.Foundations.Data.Relation
public import Mathlib.Logic.Nonempty

/-! # Modal Logic

Modal logic is a logic for reasoning about relational structures, studying statements about
necessity (`□φ`) and possibility `◇φ`.

## Primitives

The formula type uses `{atom, bot, imp, box}` as primitive constructors. Negation, conjunction,
disjunction, and diamond (possibility) are derived connectives following the Lukasiewicz convention.

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

/-- Propositions. Primitives are atoms, falsum, implication, and necessity (box). -/
inductive Proposition (Atom : Type u) : Type u where
  /-- Atomic proposition. -/
  | atom (p : Atom)
  /-- Falsum / bottom. -/
  | bot
  /-- Implication. -/
  | imp (φ₁ φ₂ : Proposition Atom)
  /-- Necessity / box. -/
  | box (φ : Proposition Atom)
  deriving DecidableEq, BEq

/-- Negation as derived connective: ¬φ := φ → ⊥ -/
abbrev Proposition.neg (φ : Proposition Atom) : Proposition Atom := .imp φ .bot

/-- Verum / top: ⊤ := ⊥ → ⊥ -/
abbrev Proposition.top : Proposition Atom := .imp .bot .bot

/-- Disjunction: φ₁ ∨ φ₂ := ¬φ₁ → φ₂ -/
abbrev Proposition.or (φ₁ φ₂ : Proposition Atom) : Proposition Atom :=
  .imp (.imp φ₁ .bot) φ₂

/-- Conjunction: φ₁ ∧ φ₂ := ¬(φ₁ → ¬φ₂) -/
abbrev Proposition.and (φ₁ φ₂ : Proposition Atom) : Proposition Atom :=
  .imp (.imp φ₁ (.imp φ₂ .bot)) .bot

/-- Possibility / diamond: ◇φ := ¬□¬φ -/
abbrev Proposition.diamond (φ : Proposition Atom) : Proposition Atom :=
  .neg (.box (.neg φ))

/-- Bi-implication. -/
abbrev Proposition.iff (φ₁ φ₂ : Proposition Atom) : Proposition Atom :=
  .and (.imp φ₁ φ₂) (.imp φ₂ φ₁)

instance : Bot (Proposition Atom) := ⟨.bot⟩

@[inherit_doc] scoped prefix:40 "¬" => Proposition.neg
@[inherit_doc] scoped infix:36 " ∧ " => Proposition.and
@[inherit_doc] scoped infix:35 " ∨ " => Proposition.or
@[inherit_doc] scoped infix:30 " → " => Proposition.imp
@[inherit_doc] scoped prefix:40 "□" => Proposition.box
@[inherit_doc] scoped prefix:40 "◇" => Proposition.diamond
@[inherit_doc] scoped infix:30 " ↔ " => Proposition.iff

/-- Register `Modal.Proposition` as an instance of `ModalConnectives`. -/
instance : ModalConnectives (Proposition Atom) where
  bot := .bot
  imp := .imp
  box := .box

/-- Satisfaction relation. `Satisfies m w φ` means that, in the model `m`, the world `w` satisfies
the proposition `φ`. -/
@[scoped grind]
def Satisfies (m : Model World Atom) (w : World) : Proposition Atom → Prop
  | .atom p => m.v w p
  | .bot => False
  | .imp φ₁ φ₂ => Satisfies m w φ₁ → Satisfies m w φ₂
  | .box φ => ∀ w', m.r w w' → Satisfies m w' φ

/-- Satisfaction of negation. -/
theorem Satisfies.neg_iff : Satisfies m w (¬φ) ↔ ¬Satisfies m w φ :=
  ⟨fun h hs => h hs, fun h hs => absurd hs h⟩

/-- Satisfaction of diamond. -/
theorem Satisfies.diamond_iff : Satisfies m w (◇φ) ↔ ∃ w', m.r w w' ∧ Satisfies m w' φ := by
  unfold Proposition.diamond Proposition.neg
  simp only [Satisfies]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    exact h fun w' hr hs => absurd hs (hc w' hr)
  · intro ⟨w', hr, hs⟩ hbox
    exact hbox w' hr hs

/-- Satisfaction of conjunction. -/
theorem Satisfies.and_iff : Satisfies m w (φ₁ ∧ φ₂) ↔ Satisfies m w φ₁ ∧ Satisfies m w φ₂ := by
  change ((Satisfies m w φ₁ → Satisfies m w φ₂ → False) → False) ↔ _
  constructor
  · intro h
    constructor
    · by_contra h1; exact h (fun hs => absurd hs h1)
    · by_contra h2; exact h (fun _ hs => absurd hs h2)
  · intro ⟨h1, h2⟩ hf; exact hf h1 h2

/-- Satisfaction of disjunction. -/
theorem Satisfies.or_iff : Satisfies m w (φ₁ ∨ φ₂) ↔ Satisfies m w φ₁ ∨ Satisfies m w φ₂ := by
  change ((Satisfies m w φ₁ → False) → Satisfies m w φ₂) ↔ _
  constructor
  · intro h
    rcases Classical.em (Satisfies m w φ₁) with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (h h1)
  · intro h hn
    cases h with
    | inl h => exact absurd h hn
    | inr h => exact h

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
@[simp, scoped grind =]
def Satisfies.Bundled (j : Judgement World Atom) : Prop := Satisfies j.m j.w j.φ

instance : HasInferenceSystem (Judgement World Atom) := ⟨Satisfies.Bundled⟩

open scoped InferenceSystem Proposition

@[scoped grind =]
theorem derivation_def {m : Model World Atom} {w : World} {φ : Proposition Atom} :
  ⇓Modal[m,w ⊨ φ] = Satisfies m w φ := rfl

/-- A world satisfies a proposition iff it does not satisfy the negation of the proposition. -/
@[scoped grind =]
theorem neg_satisfies : ⇓Modal[m,w ⊨ ¬φ] ↔ ¬⇓Modal[m,w ⊨ φ] := Satisfies.neg_iff

/-- Characterisation of the `∨` connective. -/
@[scoped grind =]
theorem Satisfies.or_iff_or {m : Model World Atom} :
    ⇓Modal[m,w ⊨ φ₁ ∨ φ₂] ↔ ⇓Modal[m,w ⊨ φ₁] ∨ ⇓Modal[m,w ⊨ φ₂] := Satisfies.or_iff

/-- Characterisation of the `→` connective. -/
@[scoped grind =]
theorem Satisfies.impl_iff_impl {m : Model World Atom} :
    ⇓Modal[m,w ⊨ φ₁ → φ₂] ↔ (⇓Modal[m,w ⊨ φ₁] → ⇓Modal[m,w ⊨ φ₂]) :=
  Iff.rfl

/-- Characterisation of the `□` modality. -/
@[scoped grind =]
theorem Satisfies.box_iff_forall {m : Model World Atom} :
    ⇓Modal[m,w ⊨ □φ] ↔ ∀ w', m.r w w' → ⇓Modal[m,w' ⊨ φ] :=
  Iff.rfl

/-- Characterisation of the `◇` modality. -/
@[scoped grind =]
theorem Satisfies.diamond_iff_exists {m : Model World Atom} :
    ⇓Modal[m,w ⊨ ◇φ] ↔ ∃ w', m.r w w' ∧ ⇓Modal[m,w' ⊨ φ] := Satisfies.diamond_iff

/-- Characterisation of `∧` in terms of satisfaction. -/
@[scoped grind =]
theorem Satisfies.and_iff_and {m : Model World Atom} :
    ⇓Modal[m,w ⊨ φ₁ ∧ φ₂] ↔ ⇓Modal[m,w ⊨ φ₁] ∧ ⇓Modal[m,w ⊨ φ₂] := Satisfies.and_iff

/-- The theory of a world in a model is the set of all propositions that it satifies. -/
abbrev theory (m : Model World Atom) (w : World) : Set (Proposition Atom) :=
  {φ | ⇓Modal[m,w ⊨ φ]}

/-- Two worlds are theory-equivalent under a model if they have the same theory. -/
abbrev TheoryEq (m : Model World Atom) (w₁ w₂ : World) :=
  theory m w₁ = theory m w₂

theorem TheoryEq.ext_iff : TheoryEq m w₁ w₂ ↔ (∀ φ, φ ∈ theory m w₁ ↔ φ ∈ theory m w₂) :=
  Set.ext_iff

/-- Any proposition satisfied by a world is in the theory of that world. -/
@[scoped grind →]
theorem satisfies_theory (h : Satisfies m w φ) : φ ∈ theory m w := h

/-- If two worlds are not theory equivalent, there exists a distinguishing proposition. -/
lemma not_theoryEq_satisfies (h : ¬TheoryEq m w₁ w₂) :
    ∃ φ, (⇓Modal[m,w₁ ⊨ φ] ∧ ¬⇓Modal[m,w₂ ⊨ φ]) := by
  rw [TheoryEq.ext_iff] at h
  push Not at h
  obtain ⟨φ, h⟩ := h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨φ, h1, h2⟩
  · exact ⟨¬φ, neg_satisfies.mpr h1, fun h3 => neg_satisfies.mp h3 h2⟩

/-- If two worlds are theory equivalent and the former satisfies a proposition, the latter does as
well. -/
theorem theoryEq_satisfies {m : Model World Atom} (h : TheoryEq m w₁ w₂)
    (hs : Satisfies m w₁ φ) : ⇓Modal[m,w₂ ⊨ φ] := by
  apply TheoryEq.ext_iff.1 at h
  exact (h φ).mp hs

/-- The K axiom, valid for all models. -/
theorem Satisfies.k : ⇓Modal[m,w ⊨ □(φ₁ → φ₂) → (□φ₁ → □φ₂)] := by
  change Satisfies m w (.imp (.box (.imp φ₁ φ₂)) (.imp (.box φ₁) (.box φ₂)))
  simp only [Satisfies]
  intro h1 h2 w' hr
  exact h1 w' hr (h2 w' hr)

/-- The dual axiom, valid for all models. -/
theorem Satisfies.dual : ⇓Modal[m,w ⊨ ◇φ ↔ ¬□¬φ] := by
  change Satisfies m w (.iff (.diamond φ) (.neg (.box (.neg φ))))
  rw [and_iff]
  exact ⟨id, id⟩

/-- The T axiom, valid for all reflexive models. -/
theorem Satisfies.t {m : Model World Atom} [instRefl : Std.Refl m.r] {w : World}
    (φ : Proposition Atom) : ⇓Modal[m,w ⊨ φ → ◇φ] := by
  change Satisfies m w φ → Satisfies m w (◇φ)
  intro hφ
  rw [diamond_iff]
  exact ⟨w, instRefl.refl w, hφ⟩

/-- Any model that admits the axiom T is reflexive. -/
theorem Satisfies.t_refl {r : World → World → Prop} [Nonempty Atom]
    (h : ∀ {v} {w} {φ : Proposition Atom}, ⇓Modal[⟨r, v⟩,w ⊨ φ → ◇φ]) : Std.Refl r where
  refl w := by
    have a := Classical.arbitrary Atom
    let v : World → Atom → Prop := fun w' _ => w' = w
    have h' := h (v := v) (w := w) (φ := .atom a)
    simp only [derivation_def] at h'
    have hsat : Satisfies ⟨r, v⟩ w (.atom a) := rfl
    have h₂ := h' hsat
    rw [diamond_iff] at h₂
    obtain ⟨w', hr, hv⟩ := h₂
    change w' = w at hv
    rwa [hv] at hr

/-- In any reflexive model, `□φ → φ` is equivalent to `φ → ◇φ`. -/
theorem Satisfies.t_box_diamond [Std.Refl m.r] :
    ⇓Modal[m,w ⊨ □φ → φ] ↔ ⇓Modal[m,w ⊨ φ → ◇φ] := by
  have hrefl := Std.Refl.refl (r := m.r) w
  change ((∀ w', m.r w w' → Satisfies m w' φ) → Satisfies m w φ) ↔
       (Satisfies m w φ → Satisfies m w (◇φ))
  constructor
  · intro h hφ
    rw [diamond_iff]
    exact ⟨w, hrefl, hφ⟩
  · intro h hbox
    have hφ := hbox w hrefl
    exact hφ

/-- The B axiom, valid for all symmetric models. -/
theorem Satisfies.b {m : Model World Atom} [instSymm : Std.Symm m.r] {w : World}
    (φ : Proposition Atom) :
    ⇓Modal[m,w ⊨ φ → □◇φ] := by
  change Satisfies m w φ → ∀ w', m.r w w' → Satisfies m w' (◇φ)
  intro hφ w' hr
  rw [diamond_iff]
  exact ⟨w, instSymm.symm w w' hr, hφ⟩

/-- Any model that admits the axiom B is symmetric. -/
theorem Satisfies.b_symm {World Atom} {r : World → World → Prop} [Nonempty Atom]
    (h : ∀ {v} {w} {φ : Proposition Atom}, ⇓Modal[⟨r, v⟩,w ⊨ φ → □◇φ]) : Std.Symm r where
  symm {w₁ w₂} hr := by
    have a := Classical.arbitrary Atom
    let v₁ := fun (w' : World) (_ : Atom) => w' = w₁
    have h₁ : Satisfies ⟨r, v₁⟩ w₁ (.atom a) →
               ∀ w', r w₁ w' → Satisfies ⟨r, v₁⟩ w' (◇(.atom a)) :=
      h (v := v₁) (w := w₁) (φ := .atom a)
    have hsat : Satisfies ⟨r, v₁⟩ w₁ (.atom a) := rfl
    have h₂ := h₁ hsat w₂ hr
    rw [diamond_iff] at h₂
    obtain ⟨w'', hr', hv⟩ := h₂
    simp only [Satisfies] at hv
    rwa [← hv]

/-- The 4 axiom, valid for all transitive models. -/
theorem Satisfies.four {m : Model World Atom} [IsTrans World m.r] {w : World}
    (φ : Proposition Atom) : ⇓Modal[m,w ⊨ ◇◇φ → ◇φ] := by
  change Satisfies m w (◇◇φ) → Satisfies m w (◇φ)
  rw [diamond_iff, diamond_iff]
  intro ⟨w', hr₁, h'⟩
  rw [diamond_iff] at h'
  obtain ⟨w'', hr₂, hs⟩ := h'
  exact ⟨w'', IsTrans.trans _ _ _ hr₁ hr₂, hs⟩

/-- Any model that admits 4 is transitive. -/
theorem Satisfies.four_trans {r : World → World → Prop} [Nonempty Atom]
    (h : ∀ {v} {w} {φ : Proposition Atom}, ⇓Modal[⟨r, v⟩,w ⊨ ◇◇φ → ◇φ]) : IsTrans World r where
  trans w₁ w₂ w₃ h₁ h₂ := by
    have a := Classical.arbitrary Atom
    let v := fun (w' : World) (_ : Atom) => w' = w₃
    have h' : Satisfies ⟨r, v⟩ w₁ (◇◇(.atom a)) →
              Satisfies ⟨r, v⟩ w₁ (◇(.atom a)) :=
      h (v := v) (w := w₁) (φ := .atom a)
    have hdd : Satisfies ⟨r, v⟩ w₁ (◇◇(.atom a)) := by
      rw [diamond_iff]
      exact ⟨w₂, h₁, by rw [diamond_iff]; exact ⟨w₃, h₂, rfl⟩⟩
    have h₃ := h' hdd
    rw [diamond_iff] at h₃
    obtain ⟨w', hr, hv⟩ := h₃
    simp only [Satisfies] at hv
    rwa [← hv]

/-- The 5 axiom, valid for all Euclidean models. -/
theorem Satisfies.five {m : Model World Atom} [Relation.RightEuclidean m.r]
    {w : World}
    (φ : Proposition Atom) : ⇓Modal[m,w ⊨ ◇φ → □◇φ] := by
  have heuc := @Relation.RightEuclidean.rightEuclidean (r := m.r)
  change Satisfies m w (◇φ) → ∀ w', m.r w w' → Satisfies m w' (◇φ)
  intro hdiam w' hr
  rw [diamond_iff] at hdiam ⊢
  obtain ⟨w'', hr', hs⟩ := hdiam
  exact ⟨w'', heuc hr hr', hs⟩

/-- Any model that admits 5 is Euclidean. -/
theorem Satisfies.five_rightEuclidean {r : World → World → Prop} [Nonempty Atom]
    (h : ∀ {v} {w : World} {φ : Proposition Atom}, ⇓Modal[⟨r, v⟩,w ⊨ ◇φ → □◇φ]) :
    Relation.RightEuclidean r where
  rightEuclidean {w₁ w₂ w₃} h₁ h₂ := by
    have a := Classical.arbitrary Atom
    let v := fun (w' : World) (_ : Atom) => w' = w₃
    have h' : Satisfies ⟨r, v⟩ w₁ (◇(.atom a)) →
              ∀ w', r w₁ w' → Satisfies ⟨r, v⟩ w' (◇(.atom a)) :=
      h (v := v) (w := w₁) (φ := .atom a)
    have hdiam : Satisfies ⟨r, v⟩ w₁ (◇(.atom a)) := by
      rw [diamond_iff]; exact ⟨w₃, h₂, rfl⟩
    have h₂' := h' hdiam w₂ h₁
    rw [diamond_iff] at h₂'
    obtain ⟨w', hr, hv⟩ := h₂'
    simp only [Satisfies] at hv
    rwa [← hv]

/-- The D axiom, valid for all serial models. -/
theorem Satisfies.d {m : Model World Atom} [hSer : Relation.Serial m.r] {w}
    (φ : Proposition Atom) :
    ⇓Modal[m,w ⊨ □φ → ◇φ] := by
  change (∀ w', m.r w w' → Satisfies m w' φ) → Satisfies m w (◇φ)
  intro hbox
  rw [diamond_iff]
  obtain ⟨w', hr⟩ := hSer.serial w
  exact ⟨w', hr, hbox w' hr⟩

/-- Any model that admits D is serial. -/
theorem Satisfies.d_serial {r : World → World → Prop} [Nonempty Atom]
    (h : ∀ {v} {w} {φ : Proposition Atom}, ⇓Modal[⟨r, v⟩,w ⊨ □φ → ◇φ]) : Relation.Serial r where
  serial w₁ := by
    have a := Classical.arbitrary Atom
    let v := fun (_ : World) (_ : Atom) => True
    have h' : (∀ w', r w₁ w' → Satisfies ⟨r, v⟩ w' (.atom a)) →
              Satisfies ⟨r, v⟩ w₁ (◇(.atom a)) :=
      h (v := v) (w := w₁) (φ := .atom a)
    have hbox : ∀ w', r w₁ w' → Satisfies ⟨r, v⟩ w' (.atom a) :=
      fun _ _ => trivial
    have h₃ := h' hbox
    rw [diamond_iff] at h₃
    obtain ⟨w', hr, _⟩ := h₃
    exact ⟨w', hr⟩

/-- A proposition is valid in a class of models `S` (modelled as a set) if it is satisfied under
all models in `S` for all worlds. -/
@[simp, scoped grind =]
def Proposition.valid (S : Set (Model World Atom)) (φ : Proposition Atom) : Prop :=
  ∀ (m : Model World Atom), ∀ (_ : m ∈ S), ∀ (w : World), ⇓Modal[m,w ⊨ φ]

/-- The modal logic of a class of models `S` is the set of all propositions valid in `S`. -/
@[simp, scoped grind =]
def logic (S : Set (Model World Atom)) : Set (Proposition Atom) :=
  {φ | φ.valid S}

end Cslib.Logic.Modal
