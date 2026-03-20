/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Languages.CombinatoryLogic.Basic
public import Cslib.Foundations.Semantics.Realizes
public import Mathlib.Data.PFun

@[expose] public section

namespace Cslib.SKI

open Red MRed Relation HasRealizer Realizes

/-! ### Function types

Realizers for a function type `α → β` are defined by a logical relation: `xf ⊩ f` if for every
`xa ⊩ a`, `xf ⬝ xa ⊩ f a`. We provide realizer interpretations for the primitive combinators
`S`,`K` and `I` as well as those from the `BCKW` basis.
-/

/-- A term `xf` encodes a function `f : α → β` if for every `xa ⊩ a : α`, `xf ⬝ a ⊩ f a`. -/
instance instHasRealizerPi (α β : Type*) [hα : HasRealizer α SKI] [hβ : HasRealizer β SKI] :
    HasRealizer (α → β) SKI where
  Realizes z f := ∀ {a : α} {x : SKI}, (x ⊩ a) → (z ⬝ x) ⊩ (f a)

instance instHasRealizerLiftPi (α β : Type*) [hα : HasRealizer α SKI] [hβ : HasRealizerLift β Red] :
    HasRealizerLift (α → β) Red where
  realizes_left_of_red := by
    intro f x y hy h a z hz
    apply HasRealizerLift.realizes_left_of_red (hy hz)
    exact red_head _ _ _ h

instance instHasRealizerDescPi (α β : Type*) [hα : HasRealizer α SKI] [hβ : HasRealizerDesc β Red] :
    HasRealizerDesc (α → β) Red where
  realizes_right_of_red := by
    intro f x y hy h a z hz
    apply HasRealizerDesc.realizes_right_of_red (hy hz)
    exact red_head _ _ _ h

lemma realizes_id {α : Type*} [HasRealizerLift α Red] : I ⊩ (id : α → α) :=
  fun ha => ha.left_of_red <| red_I _

lemma realizes_const {α β : Type*} [HasRealizerLift α Red] [HasRealizer β SKI] :
    K ⊩ (Function.const β : α → β → α) := fun ha _ _ _ => ha.left_of_red <| red_K ..

lemma realizes_S {α β γ : Type*} [HasRealizer α SKI] [HasRealizer β SKI]
    [HasRealizerLift γ Red] : S ⊩ (fun (f : α → β → γ) (g : α → β) (a : α) => f a (g a)) :=
  fun hf _ _ hg _ _ ha => (hf ha (hg ha)).left_of_red <| red_S ..

lemma realizes_comp {α β γ : Type*} [HasRealizer α SKI] [HasRealizer β SKI]
    [HasRealizerLift γ Red] : B ⊩ (Function.comp : (β → γ) → (α → β) → α → γ) :=
  fun hf _ _ hg _ _ ha => (hf <| hg ha).left_of_mRed <| B_def ..

lemma realizes_swap {α β γ : Type*} [HasRealizer α SKI] [HasRealizer β SKI]
    [HasRealizerLift γ Red] : C ⊩ (Function.swap : (α → β → γ) → β → α → γ) :=
  fun hf _ _ hb _ _ ha => (hf ha hb).left_of_mRed <| C_def ..

lemma realizes_diagonal_app {α β : Type*} [HasRealizer α SKI] [HasRealizerLift β Red] :
    W ⊩ (fun (f : α → α → β) (a : α) => f a a) :=
  fun hf _ _ ha => (hf ha ha).left_of_mRed <| W_def ..

/-!
### Booleans

`xu ⊩ u` if `xu` is βη-equivalent to the standard Church boolean.
-/

instance instHasRealizerLiftBool : HasRealizerLift Bool Red where
  Realizes z u := ∀ x y : SKI, (z ⬝ x ⬝ y) ↠ (if u then x else y)
  realizes_left_of_red := by
    intro u x y hu h a b
    trans y ⬝ a ⬝ b
    · apply MRed.head; apply MRed.head; exact ReflTransGen.single h
    · exact hu a b


/-- Standard true: TT := λ x y. x -/
def TT : SKI := K

@[scoped grind .]
theorem realizes_true : TT ⊩ true := fun x y ↦ MRed.K x y

/-- Standard false: FF := λ x y. y -/
def FF : SKI := K ⬝ I

@[scoped grind .]
theorem realizes_false : FF ⊩ false :=
  fun x y ↦ calc
    (FF ⬝ x ⬝ y) ↠ I ⬝ y := by apply ReflTransGen.single; apply red_head; exact red_K I x
    _ ⭢ y := red_I y

/-- Conditional: Cond x y b := if b then x else y -/
protected def Cond : SKI := RotR

lemma cond_def {xu y z} {u : Bool} (hu : xu ⊩ u) :
    (SKI.Cond ⬝ y ⬝ z ⬝ xu) ↠ if u then y else z := by
  cases u
  all_goals {
    trans xu ⬝ y ⬝ z
    · exact rotR_def ..
    · exact hu ..
    }

lemma realizes_cond {α : Type*} [HasRealizerLift α Red] :
    SKI.Cond ⊩ (fun (a b : α) (u : Bool) => if u then a else b) := by
  intro a xa ha b xb hb u xu hu
  cases u
  case false =>
    exact hb.left_of_mRed <| cond_def hu
  case true =>
    exact ha.left_of_mRed <| cond_def hu

/-!
### Pairs

`xp ⊩ ⟨a, b⟩` if `Fst ⬝ xp ⊩ a` and `Snd ⬝ xp ⊩ b`, where `Fst` and `Snd` are the canonical
projections. We note that this breaks the "Church encoding" pattern, which would define encodings
of a product by its recursor, ie `xp ⊩ ⟨a, b⟩` if for every `f`, `xp ⬝ f ↠ f ⬝ xa ⬝ xb` for some
`xa ⊩ a` and `xb ⊩ b`.
-/

/-- MkPair := λ a b. ⟨a,b⟩ -/
def MkPair : SKI := SKI.Cond
/-- First projection -/
def Fst : SKI := R ⬝ TT
/-- Second projection -/
def Snd : SKI := R ⬝ FF

@[scoped grind .]
theorem fst_correct (a b : SKI) : (Fst ⬝ (MkPair ⬝ a ⬝ b)) ↠ a := calc
  _ ↠ SKI.Cond ⬝ a ⬝ b ⬝ TT := R_def _ _
  _ ↠ TT ⬝ a ⬝ b := rotR_def ..
  _ ⭢ a := red_K ..

@[scoped grind .]
theorem snd_correct (a b : SKI) : (Snd ⬝ (MkPair ⬝ a ⬝ b)) ↠ b := by calc
  _ ↠ SKI.Cond ⬝ a ⬝ b ⬝ FF := R_def _ _
  _ ↠ FF ⬝ a ⬝ b := rotR_def ..
  _ ⭢ I ⬝ b := red_head _ _ b <| red_K ..
  _ ⭢ b := red_I b

instance instHasRealizerProd {α β : Type*} [HasRealizer α SKI] [HasRealizer β SKI] :
    HasRealizer (α × β) SKI where
  Realizes x p := ((Fst ⬝ x) ⊩ p.1)  ∧ (Snd ⬝ x) ⊩ p.2

instance instHasRealizerLiftProd {α β : Type*} [HasRealizerLift α Red] [HasRealizerLift β Red] :
    HasRealizerLift (α × β) Red where
  realizes_left_of_red := by
    intro p x y ⟨hp₁, hp₂⟩ h
    constructor
    · apply hp₁.left_of_mRed
      exact ReflTransGen.single <| red_tail Fst _ _ h
    · apply hp₂.left_of_mRed
      exact ReflTransGen.single <| red_tail Snd _ _ h

instance instHasRealizerDescProd {α β : Type*} [HasRealizerDesc α Red] [HasRealizerDesc β Red] :
    HasRealizerDesc (α × β) Red where
  realizes_right_of_red := by
    intro p x y ⟨hp₁, hp₂⟩ h
    constructor
    · apply hp₁.right_of_mRed
      exact ReflTransGen.single <| red_tail Fst _ _ h
    · apply hp₂.right_of_mRed
      exact ReflTransGen.single <| red_tail Snd _ _ h

/-- The pairing term `SKI.MkPair` indeed encodes `Prod.Mk`. -/
lemma realizes_mkPair {α β : Type*} [HasRealizerLift α Red] [HasRealizerLift β Red] :
    SKI.MkPair ⊩ (Prod.mk : α → β → α × β) := by
  intro a xa ha b xb hb
  constructor
  · exact ha.left_of_mRed <| fst_correct ..
  · exact hb.left_of_mRed <| snd_correct ..

lemma realizes_fst {α β : Type*} [HasRealizer α SKI] [HasRealizer β SKI] :
    SKI.Fst ⊩ (Prod.fst : α × β → α) := by
  intro _ _ h
  exact h.1

lemma realizes_snd {α β : Type*} [HasRealizer α SKI] [HasRealizer β SKI] :
    SKI.Snd ⊩ (Prod.snd : α × β → β) := by
  intro _ _ h
  exact h.2

def prodRecPoly : SKI.Polynomial 2 := &0 ⬝' (Fst ⬝' &1) ⬝' (Snd ⬝' &1)
/-- The term which will encode `Prod.rec`. -/
def prodRec := prodRecPoly.toSKI
lemma prodRec_def (xf xp : SKI) : (prodRec ⬝ xf ⬝ xp) ↠ xf ⬝ (Fst ⬝ xp) ⬝ (Snd ⬝ xp) :=
  prodRecPoly.toSKI_correct [xf, xp] (by simp)

theorem realizes_prod_rec {α β γ : Type*} [HasRealizer α SKI] [HasRealizer β SKI]
    [HasRealizerLift γ Red] : prodRec ⊩ (Prod.rec : (α → β → γ) → α × β → γ) := by
  intro f xf hf p xp hp
  exact (hf hp.1 hp.2).left_of_mRed <| prodRec_def ..

/-!
### Sums

`xab ⊩ s : α ⊕ β` if for every `f, g`, `xab ⬝ f ⬝ g` reduces to `f ⬝ xa`, for `s = .inl a` and
`xa ⊩ a`, or `g ⬝ xb`, for `s = .inr b` and `xb ⊩  b`.
-/

def realizesSum {α β : Type*} [HasRealizer α SKI] [HasRealizer β SKI] (x : SKI) : α ⊕ β → Prop
  | .inl a => ∀ f g : SKI, ∃ xa : SKI, (xa ⊩ a) ∧ (x ⬝ f ⬝ g) ↠ f ⬝ xa
  | .inr b => ∀ f g : SKI, ∃ xb : SKI, (xb ⊩ b) ∧ (x ⬝ f ⬝ g) ↠ g ⬝ xb

instance instHasRealizerSum {α β : Type*} [HasRealizer α SKI] [HasRealizer β SKI] :
    HasRealizer (α ⊕ β) SKI where
  Realizes := realizesSum

instance instHasRealizerLiftSum {α β : Type*} [HasRealizerLift α Red] [HasRealizerLift β Red] :
    HasRealizerLift (α ⊕ β) Red where
  realizes_left_of_red := by
    intro ab x y hy h
    cases ab
    case inl a =>
      intro f g
      obtain ⟨xa, ha, hred⟩ := hy f g
      use xa, ha
      exact ReflTransGen.head (red_head _ _ g <| red_head _ _ f h) hred
    case inr b =>
      intro f g
      obtain ⟨xb, hb, hred⟩ := hy f g
      use xb, hb
      exact ReflTransGen.head (red_head _ _ g <| red_head _ _ f h) hred

def inlPoly : SKI.Polynomial 3 := &1 ⬝' &0
protected def Inl : SKI := inlPoly.toSKI
lemma inl_def (a f g : SKI) : (SKI.Inl ⬝ a ⬝ f ⬝ g) ↠ f ⬝ a :=
  inlPoly.toSKI_correct [a, f, g] (by simp)

lemma realizes_sum_inl {α β : Type*} [HasRealizer α SKI] [HasRealizer β SKI] :
    SKI.Inl ⊩ (Sum.inl : α → α ⊕ β) := by
  intro a xa ha f g
  use xa, ha, inl_def ..

def inrPoly : SKI.Polynomial 3 := &2 ⬝' &0
protected def Inr : SKI := inrPoly.toSKI
lemma inr_def (a f g : SKI) : (SKI.Inr ⬝ a ⬝ f ⬝ g) ↠ g ⬝ a :=
  inrPoly.toSKI_correct [a, f, g] (by simp)

lemma realizes_sum_inr {α β : Type*} [HasRealizer α SKI] [HasRealizer β SKI] :
    SKI.Inr ⊩ (Sum.inr : β → α ⊕ β) := by
  intro b xb hb f g
  use xb, hb, inr_def ..

def sumRec : SKI := RotR

theorem realizes_sum_rec {α β γ : Type*} [HasRealizer α SKI] [HasRealizer β SKI]
    [HasRealizerLift γ Red] : sumRec ⊩ (Sum.rec : (α → γ) → (β → γ) → α ⊕ β → γ) := by
  intro f xf hf g xg hg ab xab hab
  cases ab with
  | inl a =>
    obtain ⟨xa, ha, hred⟩ := hab xf xg
    exact (hf ha).left_of_mRed <| (rotR_def ..).trans hred
  | inr b =>
    obtain ⟨xb, hb, hred⟩ := hab xf xg
    exact (hg hb).left_of_mRed <| (rotR_def ..).trans hred

/-!
### Partial values

A term `x` encodes a partial value `o` if `o = Part.none`, or `o = Part.some a` and `x ⊩ a`. We
specialize the definition of realizers for function types to partial functions `a →. β`.
-/

instance instHasRealizerPart {α : Type*} [HasRealizer α SKI] : HasRealizer (Part α) SKI where
  Realizes x o := (h : o.Dom) → x ⊩ (o.get h)

lemma realizes_of_mem {α : Type*} [HasRealizer α SKI] {o : Part α} {x : SKI} (h : x ⊩ o)
    {a : α} (ha : a ∈ o) : x ⊩ a := by
  obtain ⟨hao, ha⟩ := ha
  exact ha ▸ h hao

lemma realizes_some_iff {α : Type*} [HasRealizer α SKI] {a : α} {x : SKI} :
    (x ⊩ Part.some a) ↔ x ⊩ a := by
  refine ⟨?_, ?_⟩
  · intro h; exact h (Part.some_dom a)
  · intro h; exact fun _ => h

lemma realizes_none {α : Type*} [HasRealizer α SKI] (x : SKI) : x ⊩ (Part.none : Part α) :=
  fun h => False.elim (Part.not_none_dom h)

lemma realizes_some {α : Type*} [HasRealizerLift α Red] : I ⊩ (Part.some : α → Part α) := by
  intro a xa ha
  rw [realizes_some_iff]
  exact ha.left_of_red (red_I xa)

instance instHasRealizerLiftPart {α : Type*} [HasRealizerLift α Red] :
    HasRealizerLift (Part α) Red where
  realizes_left_of_red := by
    intro o x y ho h hdom
    exact (ho hdom).left_of_red h

instance instHasRealizerDescPart {α : Type*} [HasRealizerDesc α Red] :
    HasRealizerDesc (Part α) Red where
  realizes_right_of_red := by
    intro o x y ho h hdom
    exact (ho hdom).right_of_red h

instance instHasRealizerPFun (α β : Type*) [HasRealizer α SKI] [HasRealizer β SKI] :
  HasRealizer (α →. β) SKI := inferInstanceAs <| HasRealizer (α → Part β) SKI

instance instHasRealizerLiftPFun (α β : Type*) [hα : HasRealizer α SKI]
    [hβ : HasRealizerLift β Red] : HasRealizerLift (α →. β) Red :=
    inferInstanceAs <| HasRealizerLift (α → Part β) Red

instance instHasRealizerDescPFun (α β : Type*) [hα : HasRealizer α SKI]
    [hβ : HasRealizerDesc β Red] : HasRealizerDesc (α →. β) Red :=
    inferInstanceAs <| HasRealizerDesc (α → Part β) Red

lemma realizes_pfun_iff {α β : Type*} [HasRealizer α SKI] [HasRealizer β SKI] (xf : SKI)
    (f : α →. β) :
    (xf ⊩ f) ↔ ∀ {a : α} (ha : a ∈ f.Dom) {xa : SKI}, (xa ⊩ a) → (xf ⬝ xa) ⊩ f.fn a ha := by
  constructor
  · intro h a ha xa hxa
    exact h hxa ha
  · intro h a xa ha hdom
    exact h hdom ha

end Cslib.SKI
