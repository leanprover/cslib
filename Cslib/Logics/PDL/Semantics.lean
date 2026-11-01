/-
Copyright (c) 2026 Malvin Gattinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Malvin Gattinger
-/

module

public import Cslib.Foundations.Semantics.Frame.Basic
public import Cslib.Foundations.Semantics.Frame.LTS
public import Cslib.Logics.Modal.Semantics
public import Cslib.Logics.Modal.Unary.Basic
public import Cslib.Logics.PDL.Basic
-- public import Cslib.Foundations.Semantics.LTS.Bisimulation

/-! # Semantics for Propositional Dynamic Logic (PDL) -/

@[expose] public section

namespace Cslib.Logic.Modal.PDL

variable {State Label Atom : Type*}

/-! ## Models -/

/-- A PDL model consists of an `LTS` and a valuation for its states.
The LTS uses all programs as labels, so this type includes irregular frames. -/
structure Model State Label Atom where
  /-- The labelled transition system. -/
  lts : LTS State (Program Label Atom)
  /-- Valuation of atoms at states. -/
  val : State → Atom → Prop

/-- Converts a PDL model into a unary modal model. -/
def Model.toModal (m : Model State Label Atom) :
    Modal.Model State (.mkUnary (Program Label Atom)) Atom :=
  Modal.Model.mk m.lts.toFrame m.val

@[simp, scoped grind =, modal =]
theorem Model.toModal_toFrame (m : Model State Label Atom) :
    m.toModal.toFrame = m.lts.toFrame := rfl

open Cslib.Logic.Modal in
/-- View a PDL formula over the unary signature with one modality per program. -/
def Formula.toUnary :
    Formula Label Atom → Proposition (PFunctor.mkUnary (Program Label Atom)) Atom
  | .atom p => .atom p
  | .false => .false
  | .not φ => .not (toUnary φ)
  | .or φ ψ => .or (toUnary φ) (toUnary ψ)
  | .triangle s φs => .triangle ⟨s, φs ∘ Sum.inl⟩ (fun _ => toUnary (φs (.inr ())))

@[scoped grind =, modal =]
theorem Formula.toUnary_atom (p : Atom) :
    Formula.toUnary (.atom p : Formula Label Atom) = .atom p := rfl

@[scoped grind =, modal =]
theorem Formula.toUnary_bot : (⊥ : Formula Label Atom).toUnary = ⊥ := rfl

@[scoped grind =, modal =]
theorem Formula.toUnary_top : (⊤ : Formula Label Atom).toUnary = ⊤ := rfl

@[scoped grind =, modal =]
theorem Formula.toUnary_not (φ : Formula Label Atom) : (¬φ).toUnary = ¬φ.toUnary := rfl

@[scoped grind =, modal =]
theorem Formula.toUnary_or (φ ψ : Formula Label Atom) :
    (φ ∨ ψ).toUnary = (φ.toUnary ∨ ψ.toUnary) := rfl

@[scoped grind =, modal =]
theorem Formula.toUnary_and (φ ψ : Formula Label Atom) :
    (φ ∧ ψ).toUnary = (φ.toUnary ∧ ψ.toUnary) := rfl

@[scoped grind =, modal =]
theorem Formula.toUnary_imp (φ ψ : Formula Label Atom) :
    (φ → ψ).toUnary = (φ.toUnary → ψ.toUnary) := rfl

@[scoped grind =, modal =]
theorem Formula.toUnary_iff (φ ψ : Formula Label Atom) :
    (φ ↔ ψ).toUnary = (φ.toUnary ↔ ψ.toUnary) := rfl

@[scoped grind =, modal =]
theorem Formula.toUnary_dynDiamond (a : Program Label Atom) (φ : Formula Label Atom) :
    (d⟨a⟩φ).toUnary = d⟨a⟩(φ.toUnary) := rfl

@[scoped grind =, modal =]
theorem Formula.toUnary_dynBox (a : Program Label Atom) (φ : Formula Label Atom) :
    (d[a]φ).toUnary = d[a](φ.toUnary) := rfl

/-- PDL judgement: `φ` holds at `s` in the PDL model `m`. -/
abbrev judgement (m : Model State Label Atom) (s : State) (φ : Formula Label Atom) :
    Modal.Judgement State (.mkUnary (Program Label Atom)) Atom :=
  Modal[m.toModal, s ⊨ φ.toUnary]

/-- Shortcut for `Modal[PDL.Model.toModal m,s ⊨ Formula.toUnary φ]` via `judgement`. -/
scoped notation "PDL[" m "," s " ⊨ " φ "]" => judgement m s φ

open scoped InferenceSystem

/-! ## Regular Frames and Standard Models -/

/-- A frame (i.e. an `LTS`) is *regular* for PDL iff
the transition relations for `∪`, `?'` and `;'` are as expected. -/
structure _root_.Cslib.LTS.IsRegularPDL (lts : LTS State (Program Label Atom)) : Prop where
  seq   : ∀ a b w w', lts.Tr w (a ;' b) w' ↔ ∃ u, lts.Tr w a u ∧ lts.Tr u b w'
  union : ∀ a b w w', lts.Tr w (a ∪ b) w' ↔ lts.Tr w a w' ∨ lts.Tr w b w'
  star  : ∀ a w w', lts.Tr w (a*) w' ↔ Relation.ReflTransGen (lts.Tr · a ·) w w'

/-- A PDL model is *standard* iff its frame is regular and the transition
relation for tests agrees with the semantics (and thus the valuation). -/
structure Model.IsStandard (m : Model State Label Atom) : Prop where
  regular : m.lts.IsRegularPDL
  test    : ∀ ψ w w', m.lts.Tr w (?' ψ) w' ↔ w = w' ∧ ⇓PDL[m, w ⊨ ψ]

/-! ## Standard models from an LTS

An `LTS` labelled by atomic programs together with a valuation can be extended to a standard
model. Because the transitions for tests depend on the truth of formulas, which in turn depends
on the transitions for programs, we define the transition relation of shapes (`Shape.rel`) and
the truth of formulas (`Formula.eval`) together. -/

-- NOTE: It seems a bit funny to have these defs here, as they are almost
-- the standard semantics of PDL over `LTS`. Move them up somehow?

/-- The transition relation of a program shape in the standard model over `lts`,
given the truth sets of the formulas at its test positions. -/
def Shape.rel (lts : LTS State Label) :
    (s : Shape Label) → (Tests s → State → Prop) → State → State → Prop
  | .action n, _, w, w' => lts.Tr w n w'
  | .test, sat, w, w' => w = w' ∧ sat () w
  | .seq a b, sat, w, w' => ∃ u, a.rel lts (sat ∘ .inl) w u ∧ b.rel lts (sat ∘ .inr) u w'
  | .union a b, sat, w, w' => a.rel lts (sat ∘ .inl) w w' ∨ b.rel lts (sat ∘ .inr) w w'
  | .star a, sat, w, w' => Relation.ReflTransGen (a.rel lts sat) w w'

/-- Truth of a formula in the standard model over `lts` with valuation `val`. -/
def Formula.eval (lts : LTS State Label) (val : State → Atom → Prop) :
    Formula Label Atom → State → Prop
  | .atom p, w => val w p
  | .false, _ => False
  | .not φ, w => ¬ eval lts val φ w
  | .or φ ψ, w => eval lts val φ w ∨ eval lts val ψ w
  | .triangle s φs, w => ∃ w', s.rel lts (fun t => eval lts val (φs (.inl t))) w w' ∧
      eval lts val (φs (.inr ())) w'

/-- Extend an `LTS` over atomic programs to all programs, using the valuation `val`
to decide which tests succeed. -/
def _root_.Cslib.LTS.toRegular (lts : LTS State Label) (val : State → Atom → Prop) :
    LTS State (Program Label Atom) where
  Tr w a w' := a.shape.rel lts (fun t => Formula.eval lts val (a.tests t)) w w'

theorem _root_.Cslib.LTS.toRegular_isRegularPDL (lts : LTS State Label)
    (val : State → Atom → Prop) : (lts.toRegular val).IsRegularPDL where
  seq _ _ _ _ := Iff.rfl
  union _ _ _ _ := Iff.rfl
  star _ _ _ := Iff.rfl

/-- The standard model given by an `LTS` over atomic programs and a valuation. -/
def Model.fromLTS (lts : LTS State Label) (val : State → Atom → Prop) : Model State Label Atom :=
  ⟨lts.toRegular val, val⟩

/-- Truth lemma: the modal semantics in `Model.fromLTS` agrees with `Formula.eval`. -/
theorem Model.fromLTS_judgement_iff (lts : LTS State Label) (val : State → Atom → Prop)
    (w : State) (φ : Formula Label Atom) :
    ⇓PDL[Model.fromLTS lts val, w ⊨ φ] ↔ φ.eval lts val w := by
  induction φ using Formula.induction (motive_2 := fun _ => True) generalizing w with
  | atom p => rfl
  | false => rfl
  | not φ ih => exact not_congr (ih w)
  | or φ ψ ihφ ihψ => exact or_congr (ihφ w) (ihψ w)
  | diamond a φ _ ih =>
    rw [judgement, Formula.toUnary_dynDiamond, Satisfies.dynDiamond_iff_exists]
    exact exists_congr fun w' => and_congr Iff.rfl (ih w')
  | action | test | seq | union | star => trivial

theorem Model.fromLTS_IsStandard (lts : LTS State Label) (val : State → Atom → Prop) :
    (Model.fromLTS lts val).IsStandard where
  regular := lts.toRegular_isRegularPDL val
  test ψ w w' := by
    rw [Model.fromLTS_judgement_iff]
    rfl

/-! ## Characterizations (as for HML) -/

open PDL
open scoped PDL.Model Modal.Proposition InferenceSystem Satisfies Frame

variable {m : PDL.Model State Label Atom}

@[scoped grind =, modal =]
theorem Satisfies.pdl_atom_iff {p : Atom} : ⇓PDL[m,s ⊨ p] ↔ m.val s p := by rfl

@[scoped grind =, modal =] --?
theorem Satisfies.pdl_dynDiamond_iff_exists :
    ⇓PDL[m,s ⊨ d⟨μ⟩φ] ↔ ∃ s', m.lts.Tr s μ s' ∧ ⇓PDL[m,s' ⊨ φ] := by grind [modal]

@[scoped grind =, modal =] --?
theorem Satisfies.pdl_dynBox_iff_forall :
    ⇓PDL[m,s ⊨ d[μ]φ] ↔ ∀ s', m.lts.Tr s μ s' → ⇓PDL[m,s' ⊨ φ] := by grind [modal]

@[modal ⇒]
theorem Satisfies.pdl_dynDiamond_intro (htr : m.lts.Tr s μ s')
    (h : ⇓PDL[m,s' ⊨ φ]) : ⇓PDL[m,s ⊨ d⟨μ⟩φ] := by grind [modal]

@[modal ⇒] --?
theorem Satisfies.pdl_dynBox_elim (hbox : ⇓PDL[m,s ⊨ d[μ]φ])
    (htr : m.lts.Tr s μ s') : ⇓PDL[m,s' ⊨ φ] := by grind [modal]

/-! ## Axioms (BRV Def 4.78) -/

-- TODO: should we separate the statement of the axioms from their soundness theorem?

namespace Axioms

variable {State : Type*} (m : Model State Label Atom) (s : State)
  (a b : Program Label Atom) (p q ψ : Formula Label Atom)

/-- (i) K: valid on all frames. -/
theorem K : ⇓PDL[m, s ⊨ d[a](p → q) → (d[a]p → d[a]q)] := by grind [modal]

/-- (ii) Duality: valid on all frames. -/
theorem dual : ⇓PDL[m, s ⊨ d⟨a⟩p ↔ ¬d[a](¬p)] := by grind [modal]

/-- (iii) Composition: valid on frames regular for `;'`. -/
theorem seq (h : m.lts.IsRegularPDL) :
    ⇓PDL[m, s ⊨ d⟨a ;' b⟩p ↔ d⟨a⟩(d⟨b⟩p)] := by
  simp only [judgement, Formula.toUnary_iff, Formula.toUnary_dynDiamond]
  rw [@Satisfies.iff_iff_iff]
  grind [modal, h.seq]

/-- (iv) Choice: valid on frames regular for `∪`. -/
theorem union (h : m.lts.IsRegularPDL) :
    ⇓PDL[m, s ⊨ d⟨a ∪ b⟩p ↔ (d⟨a⟩p ∨ d⟨b⟩p)] := by
  simp only [judgement, Formula.toUnary_iff, Formula.toUnary_dynDiamond]
  rw [@Satisfies.iff_iff_iff]
  grind [modal, h.union]

/-- (v) Mix: valid on frames regular for `*`. -/
theorem mix (h : m.lts.IsRegularPDL) :
    ⇓PDL[m, s ⊨ d⟨a*⟩p ↔ (p ∨ d⟨a⟩(d⟨a*⟩p))] := by
  simp only [judgement, Formula.toUnary_iff, Formula.toUnary_dynDiamond]
  rw [@Satisfies.iff_iff_iff]
  have := @Satisfies.pdl_dynDiamond_iff_exists State Label Atom m s (a*) p
  simp only [judgement, Formula.toUnary_dynDiamond] at this -- having to do this seems sub-optimal
  rw [this]
  clear this
  simp_rw [h.star a] -- using regularity here
  refine ⟨fun lhs => ?_, fun rhs => ?_⟩
  · simp only [Formula.toUnary_or, Formula.toUnary_dynDiamond]
    rw [@Satisfies.or_iff_or]
    rcases lhs with ⟨s', s_to_s', s'_p⟩
    rw [Relation.ReflTransGen.cases_head_iff] at s_to_s'
    rcases s_to_s' with _ | ⟨u, s_to_u, u_to_s'⟩
    · grind
    · right
      have := @Satisfies.pdl_dynDiamond_iff_exists State Label Atom m s a (d⟨a*⟩p)
      simp only [judgement, Formula.toUnary_dynDiamond] at this -- again, this seems annoying
      rw [this]
      clear this
      refine ⟨u, s_to_u, ?_⟩
      have := @Satisfies.pdl_dynDiamond_iff_exists State Label Atom m u (a*) p
      simp only [judgement, Formula.toUnary_dynDiamond] at this -- once more
      rw [this]
      refine ⟨s', ?_, s'_p⟩
      · convert u_to_s'
        simp_rw [h.star a] -- using regularity again
  · sorry

/-- (vi) Induction: valid on frames regular for `*`. -/
theorem ind (h : m.lts.IsRegularPDL) :
    ⇓PDL[m, s ⊨ d[a*](p → d[a]p) → (p → d[a*]p)] := sorry

/-- Test axiom (not in BRV's test-free list): needs a standard model. -/
theorem test (h : m.IsStandard) :
    ⇓PDL[m, s ⊨ d⟨?' ψ⟩p ↔ (ψ ∧ p)] := by
  have := h.test
  grind [modal]

end Axioms

end Cslib.Logic.Modal.PDL
