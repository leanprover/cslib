/-
Copyright (c) 2026 Matt Hunzinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Hunzinger
-/

module

public import Cslib.Foundations.Data.HasFresh
public import Cslib.Foundations.Syntax.HasSubstitution
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Coc.Basic

@[expose] public section

/-! # Calculus of Constructions

The Calculus of Constructions

## References

* [T. Coquand, *An algorithm for type-checking dependent types*][Coquand1996]

* [A. Chargueraud, *The Locally Nameless Representation*][Chargueraud2012]

-/

set_option linter.unusedDecidableInType false

namespace Cslib

universe u

namespace LambdaCalculus.LocallyNameless.Coc

namespace Term

/-- Variable opening of the ith bound variable. -/
@[scoped grind =]
def openRec (i : ℕ) (s : Term Var) : Term Var → Term Var
  | .bvar y => if i = y then s else (bvar y)
  | .fvar x => fvar x
  | .app f a => .app (openRec i s f) (openRec i s a)
  | .abs σ t₁ => abs (openRec i s σ) (openRec (i + 1) s t₁)
  | .pi σ t₁ => .pi (openRec i s σ) (openRec (i + 1) s t₁)
  | .type s => .type s

/-- Variable opening of the closest binding. -/
@[scoped grind =]
def open' (s : Term Var) (t : Term Var) : Term Var := openRec 0 t s

@[inherit_doc]
scoped infixr:80 " ^ᵗ " => open'

@[inherit_doc]
scoped notation:68 γ "⟦" X " ↝ " δ "⟧"=> openRec X δ γ

/--
Capture-avoiding substitution.
`m.subst x r` replaces the free occurrences of variable `x` in `m` with `r`.
-/
@[scoped grind =]
def subst [DecidableEq Var] (m : Term Var) (x : Var) (r : Term Var) : Term Var :=
  match m with
  | .bvar n => .bvar n
  | .fvar z => if z = x then r else .fvar z
  | .app f a => .app (f.subst x r) (a.subst x r)
  | .abs t b => .abs (t.subst x r) (b.subst x r)
  | .pi t b => .pi (t.subst x r) (b.subst x r)
  | .type s => .type s

/-- `Term.subst` is a substitution for λ-terms. Gives access to the notation `m[x := n]`. -/
instance instHasSubstitutionTerm [DecidableEq Var] :
    HasSubstitution (Term Var) Var (Term Var) where
  subst := Term.subst

@[scoped grind _=_]
lemma subst_def [DecidableEq Var] :
    Term.subst (m : Term Var) (x : Var) (r : Term Var) = m[x := r] := rfl

/-- Substitution of a free variable not present in a term leaves it unchanged. -/
lemma subst_fresh [DecidableEq Var] {γ : Term Var}
    (nmem : X ∉ γ.fv) (δ : Term Var) : γ = γ[X := δ] := by
  induction γ <;> grind

/-- An opening appearing in both sides of an equality of terms can be removed. -/
lemma openRec_neq_eq (neq : x ≠ y) (eq : t⟦y ↝ s₁⟧ = t⟦y ↝ s₁⟧⟦x ↝ s₂⟧) :
    t = t⟦x ↝ s₂⟧ := by
  induction t generalizing x y <;> grind

/-- Locally closed terms. -/
inductive LC : Term Var → Prop
  | var : LC (.fvar x)
  | app : LC t₁ → LC t₂ → LC (app t₁ t₂)
  | abs (L : Finset Var) : t₁.LC → (∀ x ∉ L, LC (t₂ ^ᵗ fvar x)) → LC (abs t₁ t₂)
  | pi (L : Finset Var) : t₁.LC → (∀ x ∉ L, LC (t₂ ^ᵗ fvar x)) → LC (pi t₁ t₂)
  | type : LC (.type _)

attribute [scoped grind .] LC.var LC.app LC.type

/-- Predicate for being a locally closed body of an abstraction. -/
@[scoped grind =]
def body (t : Term Var) := ∃ L : Finset Var, ∀ x ∉ L, LC (t ^ᵗ fvar x)

/-- A locally closed term is unchanged by opening. -/
lemma openRec_lc [DecidableEq Var] [HasFresh Var] {σ τ : Term Var} (lc : σ.LC) : σ = σ⟦X ↝ τ⟧ := by
  induction lc generalizing X with
  | abs | pi => grind [fresh_exists <| free_union Var, openRec_neq_eq]
  | _ => grind

/-- Substitution of a locally closed type distributes with opening. -/
lemma openRec_subst [DecidableEq Var] [HasFresh Var] {δ : Term Var}
    (Y : ℕ) (t₁ t₂ : Term Var) (lc : δ.LC) (X : Var) :
    (t₁⟦Y ↝ t₂⟧)[X := δ] = t₁[X := δ]⟦Y ↝ t₂[X := δ]⟧ := by
  induction t₁ generalizing Y <;> grind [openRec_lc]

/-- Specialize `openRec_subst` to the first opening. -/
lemma open_subst [DecidableEq Var] [HasFresh Var] {δ : Term Var}
    (σ τ : Term Var) (lc : δ.LC) (X : Var) :
    (σ ^ᵗ τ)[X := δ] = σ[X := δ] ^ᵗ τ[X := δ]
  := openRec_subst 0 σ τ lc X

/-- A locally closed term remains locally closed after substitution. -/
lemma subst_lc [DecidableEq Var] [HasFresh Var] {t₁ t₂ : Term Var}
    (t₁_lc : t₁.LC) (t₂_lc : t₂.LC) (X : Var) : t₁[X := t₂].LC := by
  induction t₁_lc with
  | abs => grind [LC.abs (free_union Var), openRec_subst]
  | pi => grind [LC.pi (free_union Var), openRec_subst]
  | _ => grind [openRec_subst]

/-- Opening to a type is equivalent to opening to a free variable and substituting. -/
lemma openRec_subst_intro [DecidableEq Var] (Y : ℕ) (δ : Term Var) (nmem : X ∉ γ.fv) :
    γ⟦Y ↝ δ⟧ = (γ⟦Y ↝ fvar X⟧)[X := δ] := by
  induction γ generalizing δ Y <;> grind

/-- Opening to a term `t` is equivalent to opening to a free variable and substituting for `t`. -/
lemma subst_intro [DecidableEq Var] (x : Var) (t e : Term Var) (mem : x ∉ e.fv) :
    e ^ᵗ t = (e ^ᵗ fvar x) [ x := t ] := by grind [openRec_subst_intro]

/-- Substitution and opening by a fresh variable commute. -/
lemma subst_open_var [DecidableEq Var] [HasFresh Var]
    (x y : Var) (u e : Term Var) (neq : y ≠ x) (lc : u.LC) :
    e.subst x u ^ᵗ fvar y = (e ^ᵗ fvar y).subst x u := by
  change e[x:=u] ^ᵗ fvar y = (e ^ᵗ fvar y)[x:=u]
  rw [open_subst e (fvar y) lc x]; grind [subst]

end Term

end LambdaCalculus.LocallyNameless.Coc

end Cslib
