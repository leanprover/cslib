/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Languages.CombinatoryLogic.Basic
public import Cslib.Foundations.Semantics.Encoded

@[expose] public section

namespace Cslib.SKI

open Red MRed Relation Encoded IsEncoding

/-- A term `xf` encodes a function `f : α → β` if for every `xa ⊩ a : α`, `xf ⬝ a ⊩ f a`. -/
instance instEncodedPi (α β : Type*) [hα : Encoded α SKI] [hβ : Encoded β SKI] :
    Encoded (α → β) SKI where
  IsEncoding f z := ∀ {a : α} {x : SKI}, (x ⊩ a) → (z ⬝ x) ⊩ (f a)

instance instEncodedLiftPi (α β : Type*) [hα : Encoded α SKI] [hβ : EncodedLift β Red] :
    EncodedLift (α → β) Red where
  isEncoding_left_of_red := by
    intro f x y hy h a z hz
    apply EncodedLift.isEncoding_left_of_red (hy hz)
    exact red_head _ _ _ h

instance instEncodedDescPi (α β : Type*) [hα : Encoded α SKI] [hβ : EncodedDesc β Red] :
    EncodedDesc (α → β) Red where
  isEncoding_right_of_red := by
    intro f x y hy h a z hz
    apply EncodedDesc.isEncoding_right_of_red (hy hz)
    exact red_head _ _ _ h

/-!
### Booleans

`xu ⊩ u` if `xu` is βη-equivalent to the standard Church boolean.
-/

instance instEncodedLiftBool : EncodedLift Bool Red where
  IsEncoding u z := ∀ x y : SKI, (z ⬝ x ⬝ y) ↠ (if u then x else y)
  isEncoding_left_of_red := by
    intro u x y hu h a b
    trans y ⬝ a ⬝ b
    · apply MRed.head; apply MRed.head; exact Relation.ReflTransGen.single h
    · exact hu a b


/-- Standard true: TT := λ x y. x -/
def TT : SKI := K

@[scoped grind .]
theorem TT_correct : TT ⊩ true := fun x y ↦ MRed.K x y

/-- Standard false: FF := λ x y. y -/
def FF : SKI := K ⬝ I

@[scoped grind .]
theorem FF_correct : FF ⊩ false :=
  fun x y ↦ calc
    (FF ⬝ x ⬝ y) ↠ I ⬝ y := by apply Relation.ReflTransGen.single; apply red_head; exact red_K I x
    _         ⭢ y := red_I y

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

lemma isEncoding_cond {α : Type*} [EncodedLift α Red] :
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

instance instEncodedProd {α β : Type*} [Encoded α SKI] [Encoded β SKI] : Encoded (α × β) SKI where
  IsEncoding p x := ((Fst ⬝ x) ⊩ p.1)  ∧ (Snd ⬝ x) ⊩ p.2

instance instEncodedLiftProd {α β : Type*} [EncodedLift α Red] [EncodedLift β Red] :
    EncodedLift (α × β) Red where
  isEncoding_left_of_red := by
    intro p x y ⟨hp₁, hp₂⟩ h
    constructor
    · apply hp₁.left_of_mRed
      exact Relation.ReflTransGen.single <| red_tail Fst _ _ h
    · apply hp₂.left_of_mRed
      exact Relation.ReflTransGen.single <| red_tail Snd _ _ h

instance instEncodedDescProd {α β : Type*} [EncodedDesc α Red] [EncodedDesc β Red] :
    EncodedDesc (α × β) Red where
  isEncoding_right_of_red := by
    intro p x y ⟨hp₁, hp₂⟩ h
    constructor
    · apply hp₁.right_of_mRed
      exact Relation.ReflTransGen.single <| red_tail Fst _ _ h
    · apply hp₂.right_of_mRed
      exact Relation.ReflTransGen.single <| red_tail Snd _ _ h

/-- The pairing term `SKI.MkPair` indeed encodes `Prod.Mk`. -/
lemma isEncoding_mkPair {α β : Type*} [EncodedLift α Red] [EncodedLift β Red] :
    SKI.MkPair ⊩ (Prod.mk : α → β → α × β) := by
  intro a xa ha b xb hb
  constructor
  · exact ha.left_of_mRed <| fst_correct ..
  · exact hb.left_of_mRed <| snd_correct ..

lemma isEncoding_fst {α β : Type*} [Encoded α SKI] [Encoded β SKI] :
    SKI.Fst ⊩ (Prod.fst : α × β → α) := by
  intro _ _ h
  exact h.1

lemma isEncoding_snd {α β : Type*} [Encoded α SKI] [Encoded β SKI] :
    SKI.Snd ⊩ (Prod.snd : α × β → β) := by
  intro _ _ h
  exact h.2

def prodRecPoly : SKI.Polynomial 2 := &0 ⬝' (Fst ⬝' &1) ⬝' (Snd ⬝' &1)
/-- The term which will encode `Prod.rec`. -/
def prodRec := prodRecPoly.toSKI
lemma prodRec_def (xf xp : SKI) : (prodRec ⬝ xf ⬝ xp) ↠ xf ⬝ (Fst ⬝ xp) ⬝ (Snd ⬝ xp) :=
  prodRecPoly.toSKI_correct [xf, xp] (by simp)

theorem isEncoding_prod_rec {α β γ : Type*} [Encoded α SKI] [Encoded β SKI]
    [EncodedLift γ Red] : prodRec ⊩ (Prod.rec : (α → β → γ) → α × β → γ) := by
  intro f xf hf p xp hp
  exact (hf hp.1 hp.2).left_of_mRed <| prodRec_def ..

/-!
### Sums

`xab ⊩ s : α ⊕ β` if for every `f, g`, `xab ⬝ f ⬝ g` reduces to `f ⬝ xa`, for `s = .inl a` and
`xa ⊩ a`, or `g ⬝ xb`, for `s = .inr b` and `xb ⊩  b`.
-/

def isEncodingSum {α β : Type*} [Encoded α SKI] [Encoded β SKI] : α ⊕ β → SKI → Prop
  | .inl a, x => ∀ f g : SKI, ∃ xa : SKI, (xa ⊩ a) ∧ (x ⬝ f ⬝ g) ↠ f ⬝ xa
  | .inr b, x => ∀ f g : SKI, ∃ xb : SKI, (xb ⊩ b) ∧ (x ⬝ f ⬝ g) ↠ g ⬝ xb

instance instEncodedSum {α β : Type*} [Encoded α SKI] [Encoded β SKI] : Encoded (α ⊕ β) SKI where
  IsEncoding := isEncodingSum

instance instEncodedLiftSum {α β : Type*} [EncodedLift α Red] [EncodedLift β Red] :
    EncodedLift (α ⊕ β) Red where
  isEncoding_left_of_red := by
    intro ab x y hy h
    cases ab
    case inl a =>
      intro f g
      obtain ⟨xa, ha, hred⟩ := hy f g
      use xa, ha
      exact Relation.ReflTransGen.head (red_head _ _ g <| red_head _ _ f h) hred
    case inr b =>
      intro f g
      obtain ⟨xb, hb, hred⟩ := hy f g
      use xb, hb
      exact Relation.ReflTransGen.head (red_head _ _ g <| red_head _ _ f h) hred

def inlPoly : SKI.Polynomial 3 := &1 ⬝' &0
protected def Inl : SKI := inlPoly.toSKI
lemma inl_def (a f g : SKI) : (SKI.Inl ⬝ a ⬝ f ⬝ g) ↠ f ⬝ a :=
  inlPoly.toSKI_correct [a, f, g] (by simp)

lemma isEncoding_sum_inl {α β : Type*} [Encoded α SKI] [Encoded β SKI] :
    SKI.Inl ⊩ (Sum.inl : α → α ⊕ β) := by
  intro a xa ha f g
  use xa, ha, inl_def ..

def inrPoly : SKI.Polynomial 3 := &2 ⬝' &0
protected def Inr : SKI := inrPoly.toSKI
lemma inr_def (a f g : SKI) : (SKI.Inr ⬝ a ⬝ f ⬝ g) ↠ g ⬝ a :=
  inrPoly.toSKI_correct [a, f, g] (by simp)

lemma isEncoding_sum_inr {α β : Type*} [Encoded α SKI] [Encoded β SKI] :
    SKI.Inr ⊩ (Sum.inr : β → α ⊕ β) := by
  intro b xb hb f g
  use xb, hb, inr_def ..

def sumRec : SKI := RotR

theorem isEncoding_sum_rec {α β γ : Type*} [Encoded α SKI] [Encoded β SKI] [EncodedLift γ Red] :
    sumRec ⊩ (Sum.rec : (α → γ) → (β → γ) → α ⊕ β → γ) := by
  intro f xf hf g xg hg ab xab hab
  cases ab with
  | inl a =>
    obtain ⟨xa, ha, hred⟩ := hab xf xg
    exact (hf ha).left_of_mRed <| (rotR_def ..).trans hred
  | inr b =>
    obtain ⟨xb, hb, hred⟩ := hab xf xg
    exact (hg hb).left_of_mRed <| (rotR_def ..).trans hred

end Cslib.SKI
