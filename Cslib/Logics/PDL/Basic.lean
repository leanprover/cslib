module

public import Mathlib.Logic.Equiv.Defs
public import Cslib.Foundations.Data.PFunctor.Basic
public import Cslib.Foundations.Logic.Operators
public import Cslib.Foundations.Semantics.Frame.LTS
public import Cslib.Foundations.Semantics.LTS.Bisimulation
public import Cslib.Logics.Modal.Basic
public import Cslib.Logics.Modal.Semantics

/-! # Propositional Dynamic Logic (PDL) via shapes of programs -/

@[expose] public section

namespace Cslib.Logic.Modal.PDL

open PFunctor

universe u v

variable {Label : Type u}

/-! ## Syntax -/

inductive Shape where
  | action (name : Label)
  | test
  | seq (a b : Shape)
  | union (a b : Shape)
  | star (a : Shape)

def Tests : @Shape Label → Type
  | .action _ => Empty
  | .test => Unit
  | .seq a b => Tests a ⊕ Tests b
  | .union a b => Tests a ⊕ Tests b
  | .star a => Tests a

abbrev signature : PFunctor :=
  ⟨@Shape Label, fun a => Tests a ⊕ Unit⟩

variable {Atom : Type v}

abbrev Formula := Cslib.Logic.Modal.Proposition (@signature Label) Atom

structure Program where
  shape : @Shape Label
  tests : Tests shape → @Formula Label Atom

def action (name : Label) : @Program Label Atom :=
  ⟨.action name, Empty.elim⟩

def test (ψ : @Formula Label Atom) : @Program Label Atom :=
  ⟨.test, fun _ => ψ⟩

def seq (a b : @Program Label Atom) : @Program Label Atom :=
  ⟨.seq a.shape b.shape, Sum.elim a.tests b.tests⟩

def union (a b : @Program Label Atom) : @Program Label Atom :=
  ⟨.union a.shape b.shape, Sum.elim a.tests b.tests⟩

def star (a : @Program Label Atom) : @Program Label Atom :=
  ⟨.star a.shape, a.tests⟩

def diamond (a : @Program Label Atom) (φ : @Formula Label Atom) : @Formula Label Atom :=
  .triangle a.shape (Sum.elim a.tests (fun _ => φ))

instance : HasDynamicDiamond (@Formula Label Atom) (@Program Label Atom) := ⟨diamond⟩

/-- Box as the dual of the diamond (only the target is negated, not the tests). -/
def box (a : @Program Label Atom) (φ : @Formula Label Atom) : @Formula Label Atom :=
  ¬ diamond a (¬ φ)

instance : HasDynamicBox (@Formula Label Atom) (@Program Label Atom) := ⟨box⟩

/-! ## Example and Notation -/

-- ⟨(?p ; a)*⟩q
def exampleFormula : @Formula Nat Nat :=
  diamond (star (seq (test (.atom 0)) (action 0))) (.atom 1)

local notation "?'" ψ:arg => test ψ
local notation a:(arg-1) ";'" b:(arg-1) => seq a b
local notation a:(arg-1) "∪" b:(arg-1) => union a b
local notation a:(arg-1) "*" => star a

instance : OfNat (@Program Nat Atom) k := ⟨action k⟩
instance : OfNat (@Formula Label Nat) k := ⟨.atom k⟩
-- above not needed with this:
instance : Coe Nat (@Program Nat Atom) := ⟨fun k => action k⟩
instance : Coe Nat (@Formula Label Nat) := ⟨fun k => .atom k⟩

def sameExampleFormula (p q : Nat) (a : Nat) : @Formula Nat Nat :=
  d⟨ (?' p ;' a)*⟩ q

/-! ## Formulas as Unary-PFunctor Propositions -/

open Cslib.Logic.Modal in
/-- View a PDL formula over the unary signature with one modality per program. -/
def Formula.toUnary :
    @Formula Label Atom → Proposition (PFunctor.mkUnary (@Program Label Atom)) Atom
  | .atom p => .atom p
  | .false => .false
  | .not φ => .not (toUnary φ)
  | .or φ ψ => .or (toUnary φ) (toUnary ψ)
  | .triangle s φs => .triangle ⟨s, φs ∘ Sum.inl⟩ (fun _ => toUnary (φs (.inr ())))

/-! ## Semantics -/

/-- A PDL model consists of an LTS and a valuation for its states.
Note that the LTS uses all programs as labels, so this type includes irregular frames! -/
structure Model State Label Atom where
  /-- The labelled transition system. -/
  lts : LTS State (@Program Label Atom)
  /-- Valuation of atoms at states. -/
  val : State → Atom → Prop

/-- Converts a PDL model into a unary modal model. -/
def Model.toModal (m : Model State Label Atom) :
    Modal.Model State (.mkUnary (@Program Label Atom)) Atom :=
  Modal.Model.mk m.lts.toFrame m.val

@[simp, scoped grind =, modal =]
theorem Model.toModal_toFrame (m : Model State Label Atom) :
    m.toModal.toFrame = m.lts.toFrame := rfl

-- TODO: somewhere here we should close and reopen the namespace as done in HML file?

/-- Shortcut for `Modal[PDL.Model.toModal m,s ⊨ φ]`. -/
scoped notation "PDL[" m "," s " ⊨ " φ "]" => Modal[PDL.Model.toModal m,s ⊨ Formula.toUnary φ]

open scoped InferenceSystem

/-! ## Regular Frames and Standard Models -/

/-- A frame (i.e. LTS) is regular for PDL iff
the transition relations for `∪`, `?'` and `;'` are as expected. -/
structure _root_.Cslib.LTS.IsRegularPDL (lts : LTS State (@Program Label Atom)) : Prop where
  seq   : ∀ a b w w', lts.Tr w (a ;' b) w' ↔ ∃ u, lts.Tr w a u ∧ lts.Tr u b w'
  union : ∀ a b w w', lts.Tr w (a ∪ b) w' ↔ lts.Tr w a w' ∨ lts.Tr w b w'
  star  : ∀ a w w', lts.Tr w (a*) w' ↔ Relation.ReflTransGen (lts.Tr · a ·) w w'

/-- A PDL model is *standard* iff its frame is regular and the transition
relation for tests agrees with the semantics (and thus the valuation). -/
structure Model.IsStandard (m : Model State Label Atom) : Prop where
  regular : m.lts.IsRegularPDL
  test    : ∀ ψ w w', m.lts.Tr w (?' ψ) w' ↔ w = w' ∧ ⇓PDL[m, w ⊨ ψ]

/-! ## Examples / checks -/

theorem test_check_example (m : Model State Label Atom)
    (h : m.IsStandard) (s : State) :
    ⇓PDL[ m, s ⊨ diamond (?' ⊥ ∪ ?' ⊤) ⊤ ] := by
  refine ⟨fun _ => s, ?_, fun _ => fun h => h⟩
  change m.lts.Tr s (?' ⊥ ∪ ?' ⊤) s
  rw [h.regular.union]
  exact .inr ((h.test _ _ _).2 ⟨rfl, fun h => h⟩)


/-! ## TODO: Characterizations (inspired by HML file) -/

open PDL LTS
open scoped PDL.Model Modal.Proposition InferenceSystem Satisfies Frame LTS

variable {m : PDL.Model State Label Atom}

@[scoped grind =, modal =]
theorem Satisfies.pdl_atom_iff {p : Atom} : ⇓PDL[m,s ⊨ p] ↔ m.val s p := by rfl

theorem Satisfies.pdl_dynDiamond_iff_exists :
    ⇓PDL[m,s ⊨ d⟨μ⟩φ] ↔ ∃ s', m.lts.Tr s μ s' ∧ ⇓PDL[m,s' ⊨ φ] := by
  unfold Formula.toUnary
  -- need lemmas about diamond of toUnary for this? or is there an easier way?
  -- rw [Satisfies.dynDiamond_iff_exists]
  -- simp [HML.Model.toModal]
  sorry

theorem Satisfies.hml_dynBox_iff_forall :
    ⇓PDL[m,s ⊨ d[μ]φ] ↔ ∀ s', m.lts.Tr s μ s' → ⇓PDL[m,s' ⊨ φ] := by
  -- rw [Satisfies.dynBox_iff_forall]
  -- simp [HML.Model.toModal]
  sorry

@[modal ⇒]
theorem Satisfies.hml_dynDiamond_intro (htr : m.lts.Tr s μ s')
    (h : ⇓PDL[m,s' ⊨ φ]) : ⇓PDL[m,s ⊨ d⟨μ⟩φ] := by
  -- grind [modal]
  sorry

@[modal ⇒]
theorem Satisfies.hml_dynBox_elim (hbox : ⇓PDL[m,s ⊨ d[μ]φ])
    (htr : m.lts.Tr s μ s') : ⇓PDL[m,s' ⊨ φ] := by
  -- grind [modal]
  sorry

/-! ## Axioms (BRV Def 4.78) -/

-- TODO: how to separate statement of the axioms from their soundness theorem?

namespace Axioms

variable {State : Type*} (m : Model State Label Atom) (s : State)
  (a b : @Program Label Atom) (p q ψ : @Formula Label Atom)

/-- (i) K: valid on all frames. -/
theorem K : ⇓PDL[m, s ⊨ d[a](p → q) → (d[a]p → d[a]q)] := by
  sorry

/-- (ii) Duality: valid on all frames. -/
theorem dual : ⇓PDL[m, s ⊨ d⟨a⟩p ↔ ¬d[a](¬p)] := sorry

/-- (iii) Composition: valid on frames regular for `;'`. -/
theorem seq (h : m.lts.IsRegularPDL) :
    ⇓PDL[m, s ⊨ d⟨a ;' b⟩p ↔ d⟨a⟩(d⟨b⟩p)] := sorry

/-- (iv) Choice: valid on frames regular for `∪`. -/
theorem union (h : m.lts.IsRegularPDL) :
    ⇓PDL[m, s ⊨ d⟨a ∪ b⟩p ↔ (d⟨a⟩p ∨ d⟨b⟩p)] := sorry

/-- (v) Mix: valid on frames regular for `*`. -/
theorem mix (h : m.lts.IsRegularPDL) :
    ⇓PDL[m, s ⊨ d⟨a*⟩p ↔ (p ∨ d⟨a⟩(d⟨a*⟩p))] := sorry

/-- (vi) Induction: valid on frames regular for `*`. -/
theorem ind (h : m.lts.IsRegularPDL) :
    ⇓PDL[m, s ⊨ d[a*](p → d[a]p) → (p → d[a*]p)] := sorry

/-- Test axiom (not in BRV's test-free list): needs a standard model. -/
theorem test (h : m.IsStandard) :
    ⇓PDL[m, s ⊨ d⟨?' ψ⟩p ↔ (ψ ∧ p)] := sorry

end Axioms

end Cslib.Logic.Modal.PDL
