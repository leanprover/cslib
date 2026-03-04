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

-/

namespace Cslib

universe u

namespace LambdaCalculus.LocallyNameless.Coc

namespace Term

/-- Variable opening of the ith bound variable. -/
@[scoped grind =]
def openingRec (i : ℕ) (s : Term Var) : Term Var → Term Var
  | .bvar y => if i = y then s else (bvar y)
  | .fvar x => fvar x
  | .app f a => .app (openingRec i s f) (openingRec i s a)
  | .abs σ t₁ => abs (openingRec i s σ) (openingRec (i + 1) s t₁)
  | .pi σ t₁ => .pi (openingRec i s σ) (openingRec (i + 1) s t₁)
  | .type => .type

/-- Variable opening of the closest binding. -/
@[scoped grind =]
def opening (s : Term Var) (t : Term Var) : Term Var := openingRec 0 t s

@[inherit_doc]
scoped infixr:80 " ^ᵗ " => opening

@[inherit_doc]
scoped notation:68 γ "⟦" X " ↝ " δ "⟧"=> openingRec X δ γ

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
  | .type => .type

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
lemma openingRec_neq_eq (neq : x ≠ y) (eq : t⟦y ↝ s₁⟧ = t⟦y ↝ s₁⟧⟦x ↝ s₂⟧) :
    t = t⟦x ↝ s₂⟧ := by
  induction t generalizing x y <;> grind

/-- Locally closed terms. -/
inductive LC : Term Var → Prop
  | var : LC (.fvar x)
  | app : LC t₁ → LC t₂ → LC (app t₁ t₂)
  | abs (L : Finset Var) : σ.LC → (∀ x ∉ L, LC (t₁ ^ᵗ fvar x)) → LC (abs σ t₁)
  | pi (L : Finset Var) : σ.LC → (∀ x ∉ L, LC (t₁ ^ᵗ fvar x)) → LC (pi σ t₁)
  | type : LC .type

attribute [scoped grind .] LC.var LC.app LC.type

/-- A locally closed term is unchanged by opening. -/
lemma openingRec_lc [HasFresh Var] {σ τ : Term Var} (lc : σ.LC) : σ = σ⟦X ↝ τ⟧ := by
  classical
  induction lc generalizing X with
  | abs | pi => grind [fresh_exists <| free_union Var, openingRec_neq_eq]
  | _ => grind

/-- Substitution of a locally closed type distributes with opening. -/
lemma openingRec_subst [DecidableEq Var] [HasFresh Var] {δ : Term Var}
    (Y : ℕ) (σ τ : Term Var) (lc : δ.LC) (X : Var) :
    (σ⟦Y ↝ τ⟧)[X := δ] = σ[X := δ]⟦Y ↝ τ[X := δ]⟧ := by
  induction σ generalizing Y <;> grind [openingRec_lc]

/-- A locally closed term remains locally closed after substitution. -/
lemma subst_lc [DecidableEq Var] [HasFresh Var] {σ τ : Term Var}
    (σ_lc : σ.LC) (τ_lc : τ.LC) (X : Var) : σ[X := τ].LC := by
  induction σ_lc with
  | abs => grind [LC.abs (free_union Var), openingRec_subst]
  | pi => grind [LC.pi (free_union Var), openingRec_subst]
  | _ => grind [openingRec_subst]

end Term

end LambdaCalculus.LocallyNameless.Coc

end Cslib
