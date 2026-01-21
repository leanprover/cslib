/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.Syntax.HasSubstitution
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Fsub.Basic

@[expose] public section

set_option linter.unusedDecidableInType false

/-! # λ-calculus

The λ-calculus with polymorphism and subtyping, with a locally nameless representation of syntax.
This file defines opening, local closure, and substitution.

## References

* [A. Chargueraud, *The Locally Nameless Representation*][Chargueraud2012]
* See also <https://www.cis.upenn.edu/~plclub/popl08-tutorial/code/>, from which
  this is adapted

-/

namespace Cslib

variable {Var : Type*} [HasFresh Var] [DecidableEq Var]

namespace LambdaCalculus.LocallyNameless.Fsub

namespace Ty

/-- Variable opening (type opening to type) of the ith bound variable. -/
@[scoped grind =]
def openRec (X : ℕ) (δ : Ty Var) : Ty Var → Ty Var
| top => top
| bvar Y => if X = Y then δ else bvar Y
| fvar X => fvar X
| arrow σ τ => arrow (openRec X δ σ) (openRec X δ τ)
| all σ τ => all (openRec X δ σ) (openRec (X + 1) δ τ)
| sum σ τ => sum (openRec X δ σ) (openRec X δ τ)

@[inherit_doc]
scoped notation:68 γ "⟦" X " ↝ " δ "⟧ᵞ"=> openRec X δ γ

/-- Variable opening (type opening to type) of the closest binding. -/
@[scoped grind =]
def open' (γ δ : Ty Var) := openRec 0 δ γ

@[inherit_doc]
scoped infixr:80 " ^ᵞ " => open'

/-- Locally closed types. -/
inductive LC : Ty Var → Prop
  | top : LC top
  | var : LC (fvar X)
  | arrow : LC σ → LC τ → LC (arrow σ τ)
  | all (L : Finset Var) : LC σ → (∀ X ∉ L, LC (τ ^ᵞ fvar X)) → LC (all σ τ)
  | sum : LC σ → LC τ → LC (sum σ τ)

attribute [scoped grind .] LC.top LC.var LC.arrow LC.sum

/-- Type substitution. -/
@[scoped grind =]
def subst (X : Var) (δ : Ty Var) : Ty Var → Ty Var
| top => top
| bvar J => bvar J
| fvar Y => if Y = X then δ else fvar Y
| arrow σ τ => arrow (subst X δ σ) (subst X δ τ)
| all σ τ => all (subst X δ σ) (subst X δ τ)
| sum σ τ => sum (subst X δ σ) (subst X δ τ)

instance : HasSubstitution (Ty Var) Var (Ty Var) where
  subst γ X δ := Ty.subst X δ γ

variable {σ τ δ γ : Ty Var}

omit [HasFresh Var] [DecidableEq Var] in
/-- An opening appearing in both sides of an equality of types can be removed. -/
lemma openRec_neq_eq {σ τ γ : Ty Var} (neq : X ≠ Y) (h : σ⟦Y ↝ τ⟧ᵞ = σ⟦Y ↝ τ⟧ᵞ⟦X ↝ γ⟧ᵞ) :
    σ = σ⟦X ↝ γ⟧ᵞ := by induction σ generalizing Y X <;> grind

/-- A locally closed type is unchanged by opening. -/
lemma openRec_lc {σ τ : Ty Var} (lc : σ.LC) : σ = σ⟦X ↝ τ⟧ᵞ := by
  induction lc generalizing X with
  | all => grind [fresh_exists <| free_union Var, openRec_neq_eq]
  | _ => grind

omit [HasFresh Var] in
@[scoped grind _=_]
lemma subst_def : Ty.subst (X : Var) (δ : Ty Var) (γ : Ty Var) = γ[X := δ] := by rfl

omit [HasFresh Var] in
/-- Substitution of a free variable not present in a type leaves it unchanged. -/
lemma subst_fresh (nmem : X ∉ γ.fv) (δ : Ty Var) : γ = γ[X := δ] := by
  induction γ <;> grind

/-- Substitution of a locally closed type distributes with opening. -/
lemma openRec_subst (Y : ℕ) (σ τ : Ty Var) (lc : δ.LC) (X : Var) :
    (σ⟦Y ↝ τ⟧ᵞ)[X := δ] = σ[X := δ]⟦Y ↝ τ[X := δ]⟧ᵞ := by
  induction σ generalizing Y <;> grind [openRec_lc]

/-- Specialize `Ty.openRec_subst` to the first opening. -/
lemma open_subst (σ τ : Ty Var) (lc : δ.LC) (X : Var) : (σ ^ᵞ τ)[X := δ] = σ[X := δ] ^ᵞ τ[X := δ]
  := openRec_subst 0 σ τ lc X

/-- Specialize `Ty.subst_open` to free variables. -/
lemma open_subst_var (σ : Ty Var) (neq : Y ≠ X) (lc : δ.LC) :
    (σ ^ᵞ fvar Y)[X := δ] = (σ[X := δ]) ^ᵞ fvar Y := by grind [open_subst]

omit [HasFresh Var] in
/-- Opening to a type is equivalent to opening to a free variable and substituting. -/
lemma openRec_subst_intro (Y : ℕ) (δ : Ty Var) (nmem : X ∉ γ.fv) :
    γ⟦Y ↝ δ⟧ᵞ = (γ⟦Y ↝ fvar X⟧ᵞ)[X := δ] := by
  induction γ generalizing δ Y <;> grind

omit [HasFresh Var] in
/-- Specialize `Ty.openRec_subst_intro` to the first opening. -/
lemma open_subst_intro (δ : Ty Var) (nmem : X ∉ γ.fv) : γ ^ᵞ δ = (γ ^ᵞ fvar X)[X := δ] :=
  openRec_subst_intro _ _ nmem

lemma subst_lc (σ_lc : σ.LC) (τ_lc : τ.LC) (X : Var) : σ[X := τ].LC := by
  induction σ_lc with
  | all => grind [LC.all (free_union Var), openRec_subst]
  | _ => grind [openRec_subst]

omit [HasFresh Var] in
lemma nmem_fv_openRec (nmem : X ∉ (σ⟦k ↝ γ⟧ᵞ).fv) : X ∉ σ.fv := by
  induction σ generalizing k <;> grind

omit [HasFresh Var] in
lemma nmem_fv_open (nmem : X ∉ (σ ^ᵞ γ).fv) : X ∉ σ.fv :=
  Ty.nmem_fv_openRec (k := 0) nmem

end Ty

namespace Term

open scoped Ty

/-- Variable opening (term opening to type) of the ith bound variable. -/
@[scoped grind =]
def openRec_ty (X : ℕ) (δ : Ty Var) : Term Var → Term Var
| bvar x => bvar x
| fvar x => fvar x
| abs σ t₁ => abs (σ⟦X ↝ δ⟧ᵞ) (openRec_ty X δ t₁)
| app t₁ t₂ => app (openRec_ty X δ t₁) (openRec_ty X δ t₂)
| tabs σ t₁ => tabs (σ⟦X ↝ δ⟧ᵞ) (openRec_ty (X + 1) δ t₁)
| tapp t₁ σ => tapp (openRec_ty X δ t₁) (σ⟦X ↝ δ⟧ᵞ)
| let' t₁ t₂ => let' (openRec_ty X δ t₁) (openRec_ty X δ t₂)
| inl t₁ => inl (openRec_ty X δ t₁)
| inr t₂ => inr (openRec_ty X δ t₂)
| case t₁ t₂ t₃ => case (openRec_ty X δ t₁) (openRec_ty X δ t₂) (openRec_ty X δ t₃)

@[inherit_doc]
scoped notation:68 t "⟦" X " ↝ " δ "⟧ᵗᵞ"=> openRec_ty X δ t

/-- Variable opening (term opening to type) of the closest binding. -/
@[scoped grind =]
def open_ty (t : Term Var) (δ : Ty Var) := openRec_ty 0 δ t

@[inherit_doc]
scoped infixr:80 " ^ᵗᵞ " => open_ty

/-- Variable opening (term opening to term) of the ith bound variable. -/
@[scoped grind =]
def openRec_tm (x : ℕ) (s : Term Var) : Term Var → Term Var
| bvar y => if x = y then s else (bvar y)
| fvar x => fvar x
| abs σ t₁ => abs σ (openRec_tm (x + 1) s t₁)
| app t₁ t₂ => app (openRec_tm x s t₁) (openRec_tm x s t₂)
| tabs σ t₁ => tabs σ (openRec_tm x s t₁)
| tapp t₁ σ => tapp (openRec_tm x s t₁) σ
| let' t₁ t₂ => let' (openRec_tm x s t₁) (openRec_tm (x + 1) s t₂)
| inl t₁ => inl (openRec_tm x s t₁)
| inr t₂ => inr (openRec_tm x s t₂)
| case t₁ t₂ t₃ => case (openRec_tm x s t₁) (openRec_tm (x + 1) s t₂) (openRec_tm (x + 1) s t₃)

@[inherit_doc]
scoped notation:68 t "⟦" x " ↝ " s "⟧ᵗᵗ"=> openRec_tm x s t

/-- Variable opening (term opening to term) of the closest binding. -/
@[scoped grind =]
def open_tm (t₁ t₂ : Term Var) := openRec_tm 0 t₂ t₁

@[inherit_doc]
scoped infixr:80 " ^ᵗᵗ " => open_tm

/-- Locally closed terms. -/
inductive LC : Term Var → Prop
  | var : LC (fvar x)
  | abs (L : Finset Var) : σ.LC → (∀ x ∉ L, LC (t₁ ^ᵗᵗ fvar x)) → LC (abs σ t₁)
  | app : LC t₁ → LC t₂ → LC (app t₁ t₂)
  | tabs (L : Finset Var) : σ.LC → (∀ X ∉ L, LC (t₁ ^ᵗᵞ .fvar X)) → LC (tabs σ t₁)
  | tapp : LC t₁ → σ.LC → LC (tapp t₁ σ)
  | let' (L : Finset Var) : LC t₁ → (∀ x ∉ L, LC (t₂ ^ᵗᵗ fvar x)) → LC (let' t₁ t₂)
  | inl : LC t₁ → LC (inl t₁)
  | inr : LC t₁ → LC (inr t₁)
  | case (L : Finset Var) :
      LC t₁ →
      (∀ x ∉ L, LC (t₂ ^ᵗᵗ fvar x)) →
      (∀ x ∉ L, LC (t₃ ^ᵗᵗ fvar x)) →
      LC (case t₁ t₂ t₃)

attribute [scoped grind .] LC.var LC.app LC.inl LC.inr LC.tapp

variable {t : Term Var} {δ : Ty Var}

omit [HasFresh Var] [DecidableEq Var] in
/-- An opening (term to type) appearing in both sides of an equality of terms can be removed. -/
lemma openRec_ty_neq_eq (neq : X ≠ Y) (eq : t⟦Y ↝ σ⟧ᵗᵞ = t⟦Y ↝ σ⟧ᵗᵞ⟦X ↝ τ⟧ᵗᵞ) :
    t = t⟦X ↝ τ⟧ᵗᵞ := by
  induction t generalizing X Y <;> grind [Ty.openRec_neq_eq]

omit [HasFresh Var] [DecidableEq Var] in
/-- Elimination of mixed term and type opening. -/
@[scoped grind .]
lemma openRec_tm_ty_eq (eq : t⟦x ↝ s⟧ᵗᵗ = t⟦x ↝ s⟧ᵗᵗ⟦y ↝ δ⟧ᵗᵞ) : t = t⟦y ↝ δ⟧ᵗᵞ
  := by induction t generalizing x y <;> grind

/-- A locally closed term is unchanged by type opening. -/
@[scoped grind =_]
lemma openRec_ty_lc {t : Term Var} (lc : t.LC) : t = t⟦X ↝ σ⟧ᵗᵞ := by
  induction lc generalizing X with
  | let' | case | tabs | abs =>
    grind [fresh_exists <| free_union Var, Ty.openRec_lc, openRec_ty_neq_eq]
  | _ => grind [Ty.openRec_lc]

/-- Substitution of a type within a term. -/
@[scoped grind =]
def subst_ty (X : Var) (δ : Ty Var) : Term Var → Term Var
| bvar x => bvar x
| fvar x => fvar x
| abs σ t₁ => abs (σ [X := δ]) (subst_ty X δ t₁)
| app t₁ t₂ => app (subst_ty X δ t₁) (subst_ty X δ t₂)
| tabs σ t₁ => tabs (σ [X := δ]) (subst_ty X δ t₁)
| tapp t₁ σ => tapp (subst_ty X δ t₁) (σ[X := δ])
| let' t₁ t₂ => let' (subst_ty X δ t₁) (subst_ty X δ t₂)
| inl t₁ => inl (subst_ty X δ t₁)
| inr t₁ => inr (subst_ty X δ t₁)
| case t₁ t₂ t₃ => case (subst_ty X δ t₁) (subst_ty X δ t₂) (subst_ty X δ t₃)

instance : HasSubstitution (Term Var) Var (Ty Var) where
  subst t X δ := Term.subst_ty X δ t

omit [HasFresh Var] in
@[scoped grind _=_]
lemma subst_ty_def : subst_ty (X : Var) (δ : Ty Var) (t : Term Var) = t[X := δ] := by rfl

omit [HasFresh Var] in
/-- Substitution of a free type variable not present in a term leaves it unchanged. -/
lemma subst_ty_fresh (nmem : X ∉ t.fv_ty) (δ : Ty Var) : t = t [X := δ] :=
  by induction t <;> grind [Ty.subst_fresh]

/-- Substitution of a locally closed type distributes with term opening to a type . -/
lemma openRec_ty_subst_ty (Y : ℕ) (t : Term Var) (σ : Ty Var) (lc : δ.LC) (X : Var) :
    (t⟦Y ↝ σ⟧ᵗᵞ)[X := δ] = (t[X := δ])⟦Y ↝  σ[X := δ]⟧ᵗᵞ := by
  induction t generalizing Y <;> grind [Ty.openRec_subst]

/-- Specialize `Term.openRec_ty_subst` to the first opening. -/
lemma open_ty_subst_ty (t : Term Var) (σ : Ty Var) (lc : δ.LC) (X : Var) :
     (t ^ᵗᵞ σ)[X := δ] = t[X := δ] ^ᵗᵞ σ[X := δ] := openRec_ty_subst_ty 0 t σ lc X

/-- Specialize `Term.open_ty_subst` to free type variables. -/
lemma open_ty_subst_ty_var (t : Term Var) (neq : Y ≠ X) (lc : δ.LC) :
    (t ^ᵗᵞ .fvar Y)[X := δ] = t[X := δ] ^ᵗᵞ .fvar Y := by grind [open_ty_subst_ty]

omit [HasFresh Var]

/-- Opening a term to a type is equivalent to opening to a free variable and substituting. -/
lemma openRec_ty_subst_ty_intro (Y : ℕ) (t : Term Var) (nmem : X ∉ t.fv_ty) :
  t⟦Y ↝ δ⟧ᵗᵞ = (t⟦Y ↝ Ty.fvar X⟧ᵗᵞ)[X := δ] := by
  induction t generalizing X δ Y <;> grind [Ty.openRec_subst_intro]

/-- Specialize `Term.openRec_ty_subst_ty_intro` to the first opening. -/
lemma open_ty_subst_ty_intro (t : Term Var) (δ : Ty Var) (nmem : X ∉ t.fv_ty) :
    t ^ᵗᵞ δ = (t ^ᵗᵞ Ty.fvar X)[X := δ] := openRec_ty_subst_ty_intro _ _ nmem

/-- Substitution of a term within a term. -/
@[scoped grind =]
def subst_tm (x : Var) (s : Term Var) : Term Var → Term Var
| bvar x => bvar x
| fvar y => if y = x then s else fvar y
| abs σ t₁ => abs σ (subst_tm x s t₁)
| app t₁ t₂ => app (subst_tm x s t₁) (subst_tm x s t₂)
| tabs σ t₁ => tabs σ (subst_tm x s t₁)
| tapp t₁ σ => tapp (subst_tm x s t₁) σ
| let' t₁ t₂ => let' (subst_tm x s t₁) (subst_tm x s t₂)
| inl t₁ => inl (subst_tm x s t₁)
| inr t₁ => inr (subst_tm x s t₁)
| case t₁ t₂ t₃ => case (subst_tm x s t₁) (subst_tm x s t₂) (subst_tm x s t₃)

instance : HasSubstitution (Term Var) Var (Term Var) where
  subst t x s := Term.subst_tm x s t

@[scoped grind _=_]
lemma subst_tm_def : subst_tm (x : Var) (s : Term Var) (t : Term Var) = t[x := s] := by rfl

omit [DecidableEq Var] in
/-- An opening (term to term) appearing in both sides of an equality of terms can be removed. -/
lemma openRec_tm_neq_eq (neq : x ≠ y) (eq : t⟦y ↝ s₁⟧ᵗᵗ = t⟦y ↝ s₁⟧ᵗᵗ⟦x ↝ s₂⟧ᵗᵗ) :
    t = t⟦x ↝ s₂⟧ᵗᵗ := by
  induction t generalizing x y <;> grind

omit [DecidableEq Var] in
/-- Elimination of mixed term and type opening. -/
lemma openRec_ty_tm_eq (eq : t⟦Y ↝ σ⟧ᵗᵞ = t⟦Y ↝ σ⟧ᵗᵞ⟦x ↝ s⟧ᵗᵗ) : t = t⟦x ↝ s⟧ᵗᵗ := by
  induction t generalizing x Y <;> grind

variable [HasFresh Var]

/-- A locally closed term is unchanged by term opening. -/
@[scoped grind =_]
lemma openRec_tm_lc (lc : t.LC) : t = t⟦x ↝ s⟧ᵗᵗ := by
  induction lc generalizing x with
  | let' | case | tabs | abs =>
    grind [fresh_exists <| free_union Var, openRec_tm_neq_eq, openRec_ty_tm_eq]
  | _ => grind

variable {t s : Term Var} {δ : Ty Var} {x : Var}

omit [HasFresh Var] in
/-- Substitution of a free term variable not present in a term leaves it unchanged. -/
lemma subst_tm_fresh (nmem : x ∉ t.fv_tm) (s : Term Var) : t = t[x := s] := by
  induction t <;> grind

/-- Substitution of a locally closed term distributes with term opening to a term. -/
lemma openRec_tm_subst_tm (y : ℕ) (t₁ t₂ : Term Var) (lc : s.LC) (x : Var) :
    (t₁⟦y ↝ t₂⟧ᵗᵗ)[x := s] = (t₁[x := s])⟦y ↝  t₂[x := s]⟧ᵗᵗ := by
  induction t₁ generalizing y <;> grind

/-- Specialize `Term.openRec_tm_subst_tm` to the first opening. -/
lemma open_tm_subst_tm (t₁ t₂ : Term Var) (lc : s.LC) (x : Var) :
    (t₁ ^ᵗᵗ t₂)[x := s] = (t₁[x := s]) ^ᵗᵗ t₂[x := s] := openRec_tm_subst_tm 0 t₁ t₂ lc x

/-- Specialize `Term.openRec_tm_subst_tm` to free term variables. -/
lemma open_tm_subst_tm_var (t : Term Var) (neq : y ≠ x) (lc : s.LC) :
     (t ^ᵗᵗ fvar y)[x := s] = (t[x := s]) ^ᵗᵗ fvar y := by grind [open_tm_subst_tm]

/-- Substitution of a locally closed type distributes with term opening to a term. -/
lemma openRec_tm_subst_ty (y : ℕ) (t₁ t₂ : Term Var) (δ : Ty Var) (X : Var) :
    (t₁⟦y ↝ t₂⟧ᵗᵗ)[X := δ] = (t₁[X := δ])⟦y ↝  t₂[X := δ]⟧ᵗᵗ := by
  induction t₁ generalizing y <;> grind

/-- Specialize `Term.openRec_tm_subst_ty` to the first opening -/
lemma open_tm_subst_ty (t₁ t₂ : Term Var) (δ : Ty Var) (X : Var) :
    (t₁ ^ᵗᵗ t₂)[X := δ] = (t₁[X := δ]) ^ᵗᵗ t₂[X := δ] := openRec_tm_subst_ty 0 t₁ t₂ δ X

/-- Specialize `Term.open_tm_subst_ty` to free term variables -/
lemma open_tm_subst_ty_var (t₁ : Term Var) (δ : Ty Var) (X y : Var) :
    (t₁ ^ᵗᵗ fvar y)[X := δ] = (t₁[X := δ]) ^ᵗᵗ fvar y := by grind [open_tm_subst_ty]

/-- Substitution of a locally closed term distributes with term opening to a type. -/
lemma openRec_ty_subst_tm (Y : ℕ) (t : Term Var) (δ : Ty Var) (lc : s.LC) (x : Var) :
    (t⟦Y ↝ δ⟧ᵗᵞ)[x := s] = t[x := s]⟦Y ↝ δ⟧ᵗᵞ := by
  induction t generalizing Y <;> grind

/-- Specialize `Term.openRec_ty_subst_tm` to the first opening. -/
lemma open_ty_subst_tm (t : Term Var) (δ : Ty Var) (lc : s.LC) (x : Var) :
    (t ^ᵗᵞ δ)[x := s] = t[x := s] ^ᵗᵞ δ := openRec_ty_subst_tm 0 t δ lc x

/-- Specialize `Term.open_ty_subst_tm` to free type variables. -/
lemma open_ty_subst_tm_var (t : Term Var) (lc : s.LC) (x Y : Var) :
    (t ^ᵗᵞ .fvar Y)[x := s] = t[x := s] ^ᵗᵞ .fvar Y := open_ty_subst_tm _ _ lc _

omit [HasFresh Var]

/-- Opening a term to a term is equivalent to opening to a free variable and substituting. -/
lemma openRec_tm_subst_tm_intro (y : ℕ) (t s : Term Var) (nmem : x ∉ t.fv_tm) :
    t⟦y ↝ s⟧ᵗᵗ = (t⟦y ↝ fvar x⟧ᵗᵗ)[x := s] := by
  induction t generalizing y <;> grind

/-- Specialize `Term.openRec_tm_subst_tm_intro` to the first opening. -/
lemma open_tm_subst_tm_intro (t s : Term Var) (nmem : x ∉ t.fv_tm) :
    t ^ᵗᵗs = (t ^ᵗᵗ fvar x)[x := s] := openRec_tm_subst_tm_intro _ _ _ nmem

variable [HasFresh Var]

lemma subst_ty_lc (t_lc : t.LC) (δ_lc : δ.LC) (X : Var) : t[X := δ].LC := by
  induction t_lc
  case' abs  => apply LC.abs (free_union Var)
  case' tabs => apply LC.tabs (free_union Var)
  case' let' => apply LC.let' (free_union Var)
  case' case => apply LC.case (free_union Var)
  all_goals grind [Ty.subst_lc, open_tm_subst_ty_var, openRec_ty_subst_ty]

lemma subst_tm_lc (t_lc : t.LC) (s_lc : s.LC) (x : Var) : t[x := s].LC := by
  induction t_lc
  case' abs  => apply LC.abs (free_union Var)
  case' let' => apply LC.let' (free_union Var)
  case' case => apply LC.case (free_union Var)
  case' tabs => apply LC.tabs (free_union Var)
  all_goals grind [open_tm_subst_tm_var, open_ty_subst_tm_var]

end Term

namespace Binding

omit [HasFresh Var]

/-- Binding substitution of types. -/
@[scoped grind =]
def subst (X : Var) (δ : Ty Var) : Binding Var → Binding Var
| sub γ => sub <| γ[X := δ]
| ty  γ => ty  <| γ[X := δ]

instance : HasSubstitution (Binding Var) Var (Ty Var) where
  subst γ X δ := Binding.subst X δ γ

variable {δ γ : Ty Var} {X : Var}

@[scoped grind _=_]
lemma subst_sub : (sub γ)[X := δ] = sub (γ[X := δ]) := by rfl

@[scoped grind _=_]
lemma subst_ty : (ty γ)[X := δ] = ty (γ[X := δ]) := by rfl

open scoped Ty in
/-- Substitution of a free variable not present in a binding leaves it unchanged. -/
lemma subst_fresh {γ : Binding Var} (nmem : X ∉ γ.fv) (δ : Ty Var) : γ = γ[X := δ] := by
  induction γ <;> grind [Ty.subst_fresh]

end Binding

end LambdaCalculus.LocallyNameless.Fsub

end Cslib
