/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Mathlib.Logic.Relation

/-! # λ-calculus

The simply typed λ-calculus, with an intrinsic representation of syntax.

## References

-/

@[expose] public section

namespace Cslib

namespace LambdaCalculus.Intrinsic.StlcProd

inductive Ty (G : Type) where
  | unit : Ty G
  | ground : G → Ty G
  | arr : Ty G → Ty G → Ty G
  | prod : Ty G → Ty G → Ty G
  deriving DecidableEq, Repr

infixr:60 " ⇒ " => Ty.arr
infixr:55 " × " => Ty.prod

abbrev Ctx (G : Type) := List (Ty G)

abbrev Var {G : Type} (Γ : Ctx G) (A : Ty G) := { i : Fin Γ.length // Γ[i] = A }

infix:40 " ∋ " => Var

inductive Tm {G : Type} : Ctx G → Ty G → Type where
  | var : Var Γ A → Tm Γ A
  | lam {Γ : Ctx G} {A B : Ty G} : Tm (A :: Γ) B → Tm Γ (A ⇒ B)
  | app : Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  | pair : Tm Γ A → Tm Γ B → Tm Γ (A × B)
  | fst : Tm Γ (A × B) → Tm Γ A
  | snd : Tm Γ (A × B) → Tm Γ B
  | unit : Tm Γ .unit

infix:40 " ⊢ " => Tm

namespace Var

variable {G : Type}

def zero {Γ : Ctx G} {A : Ty G} : Var (A :: Γ) A := ⟨0, rfl⟩

def succ {Γ : Ctx G} {A B : Ty G} (x : Var Γ A) : Var (B :: Γ) A :=
  ⟨Fin.succ x.1, x.2⟩

@[elab_as_elim]
def rec {motive : ∀ {Γ A}, Var Γ A → Sort u}
    (zero : ∀ {Γ A}, motive (@Var.zero G Γ A))
    (succ : ∀ {Γ A B} (x : Var Γ A), motive x → motive (@Var.succ G Γ A B x)) :
    ∀ {Γ A} (x : Var Γ A), motive x
  | [], _, x => Fin.elim0 x.1
  | _ :: _, _, ⟨⟨0, _⟩, h⟩ => by
      cases h
      exact zero
  | B :: Γ, A, ⟨⟨n + 1, hlt⟩, h⟩ => by
      let x : Var Γ A := ⟨⟨n, Nat.lt_of_succ_lt_succ hlt⟩, h⟩
      exact succ x (rec zero succ x)

@[elab_as_elim]
abbrev cases {Γ : Ctx G} {B : Ty G} {motive : ∀ {A}, Var (B :: Γ) A → Sort u}
    (zero : motive (@Var.zero G Γ B))
    (succ : ∀ {A} (x : Var Γ A), motive (@Var.succ G Γ A B x)) :
    ∀ {A} (x : Var (B :: Γ) A), motive x
  | _, ⟨⟨0, _⟩, h⟩ => by
      cases h
      exact zero
  | A, ⟨⟨n + 1, hlt⟩, h⟩ =>
      succ ⟨⟨n, Nat.lt_of_succ_lt_succ hlt⟩, h⟩

def count (Γ : Ctx G) (i : Fin Γ.length) : Γ ∋ Γ[i] := ⟨i, rfl⟩

def Ren (Γ Δ : Ctx G) := ∀ {A}, Γ ∋ A → Δ ∋ A

def ext (ρ : Ren Γ Δ) : Ren (B :: Γ) (B :: Δ)
  | _, ⟨⟨0, _⟩, h⟩ => by
      cases h
      exact .zero
  | A, ⟨⟨n + 1, hlt⟩, h⟩ =>
      .succ (ρ (A := A) ⟨⟨n, Nat.lt_of_succ_lt_succ hlt⟩, h⟩)

@[simp] theorem ext_zero (ρ : Ren Γ Δ) :
    ext (B := B) ρ (.zero : B :: Γ ∋ B) = .zero := rfl

@[simp] theorem ext_succ (ρ : Ren Γ Δ) (x : Γ ∋ A) :
    ext (B := B) ρ (.succ x) = .succ (ρ x) := rfl

end Var

namespace Tm

variable {G : Type}

def bvar {Γ : Ctx G} (i : Fin Γ.length) : Γ ⊢ Γ[i] :=
  .var (Var.count Γ i)

def rename (ρ : Var.Ren Γ Δ) : Γ ⊢ A → Δ ⊢ A
  | .var x => .var (ρ x)
  | .lam body => .lam (rename (Var.ext ρ) body)
  | .app f a => .app (rename ρ f) (rename ρ a)
  | .pair l r => .pair (rename ρ l) (rename ρ r)
  | .fst p => .fst (rename ρ p)
  | .snd p => .snd (rename ρ p)
  | .unit => .unit

def Sub (Γ Δ : Ctx G) := ∀ {A}, Γ ∋ A → Δ ⊢ A

def exts (σ : Sub Γ Δ) : Sub (B :: Γ) (B :: Δ)
  | _, ⟨⟨0, _⟩, h⟩ => by
      cases h
      exact .var .zero
  | A, ⟨⟨n + 1, hlt⟩, h⟩ =>
      rename (fun x => .succ x)
        (σ (A := A) ⟨⟨n, Nat.lt_of_succ_lt_succ hlt⟩, h⟩)

@[simp] theorem exts_zero (σ : Sub Γ Δ) :
    exts (B := B) σ (.zero : B :: Γ ∋ B) = .var .zero := rfl

@[simp] theorem exts_succ (σ : Sub Γ Δ) (x : Γ ∋ A) :
    exts (B := B) σ (.succ x) = rename (fun x => .succ x) (σ x) := rfl

def subst (σ : Sub Γ Δ) : Γ ⊢ A → Δ ⊢ A
  | .var x => σ x
  | .lam body => .lam (subst (exts σ) body)
  | .app f a => .app (subst σ f) (subst σ a)
  | .pair l r => .pair (subst σ l) (subst σ r)
  | .fst p => .fst (subst σ p)
  | .snd p => .snd (subst σ p)
  | .unit => .unit

def single (arg : Γ ⊢ B) : Sub (B :: Γ) Γ
  | _, ⟨⟨0, _⟩, h⟩ => by
      cases h
      exact arg
  | A, ⟨⟨n + 1, hlt⟩, h⟩ =>
      .var ⟨⟨n, Nat.lt_of_succ_lt_succ hlt⟩, h⟩

@[simp] theorem single_zero (arg : Γ ⊢ B) :
    single arg (.zero : B :: Γ ∋ B) = arg := rfl

@[simp] theorem single_succ (arg : Γ ⊢ B) (x : Γ ∋ A) :
    single arg (.succ x) = .var x := rfl

def inst (body : B :: Γ ⊢ A) (arg : Γ ⊢ B) : Γ ⊢ A :=
  subst (single arg) body

end Tm

notation:80 N " [ " M " ]" => Tm.inst N M

inductive Step {G : Type} : {Γ : Ctx G} → {A : Ty G} → Γ ⊢ A → Γ ⊢ A → Prop where
  | lam : Step N N' → Step (.lam N) (.lam N')
  | app₁ : Step f f' → Step (.app f a) (.app f' a)
  | app₂ : Step a a' → Step (.app f a) (.app f a')
  | betaLam : Step (.app (.lam N) a) (N [ a ])
  | pair₁ : Step l l' → Step (.pair l r) (.pair l' r)
  | pair₂ : Step r r' → Step (.pair l r) (.pair l r')
  | fst : Step p p' → Step (.fst p) (.fst p')
  | snd : Step p p' → Step (.snd p) (.snd p')
  | betaFst : Step (.fst (.pair l r)) l
  | betaSnd : Step (.snd (.pair l r)) r
  | etaLam (f : Γ ⊢ X ⇒ Y) : Step (.lam (.app (Tm.rename (fun x => .succ x) f) (.var .zero))) f
  | etaPair (p : Γ ⊢ X × Y) : Step (.pair (.fst p) (.snd p)) p
  | etaUnit (t : Γ ⊢ .unit) : Step t .unit

abbrev BetaEta (t u : Γ ⊢ A) : Prop := Relation.EqvGen Step t u

infix:40 " =βη " => BetaEta

theorem betaEta_map {G : Type} {Γ Δ : Ctx G} {A B : Ty G} (F : (Γ ⊢ A) → (Δ ⊢ B))
    (hF : ∀ {t u}, Step t u → Step (F t) (F u)) {t u : Γ ⊢ A} :
    t =βη u → F t =βη F u := by
  intro h
  induction h with
  | rel _ _ h => exact .rel _ _ (hF h)
  | refl x => exact Relation.EqvGen.refl (F x)
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

theorem betaEta_lam {N N' : A :: Γ ⊢ B} (h : N =βη N') :
    Tm.lam N =βη Tm.lam N' :=
  betaEta_map Tm.lam .lam h

theorem betaEta_app_left {f f' : Γ ⊢ A ⇒ B} (h : f =βη f') (a : Γ ⊢ A) :
    Tm.app f a =βη Tm.app f' a :=
  betaEta_map (flip .app a) .app₁ h

theorem betaEta_app_right (f : Γ ⊢ A ⇒ B) {a a' : Γ ⊢ A} (h : a =βη a') :
    Tm.app f a =βη Tm.app f a' :=
  betaEta_map (Tm.app f) .app₂ h

theorem betaEta_app {f f' : Γ ⊢ A ⇒ B} {a a' : Γ ⊢ A}
    (hf : f =βη f') (ha : a =βη a') : Tm.app f a =βη Tm.app f' a' :=
  .trans _ _ _ (betaEta_app_left hf a) (betaEta_app_right f' ha)

theorem betaEta_pair {l l' : Γ ⊢ A} {r r' : Γ ⊢ B}
    (hl : l =βη l') (hr : r =βη r') : Tm.pair l r =βη Tm.pair l' r' :=
  .trans _ _ _
    (betaEta_map (flip .pair r) .pair₁ hl)
    (betaEta_map (Tm.pair l') .pair₂ hr)

theorem betaEta_fst {p p' : Γ ⊢ A × B} (h : p =βη p') :
    Tm.fst p =βη Tm.fst p' :=
  betaEta_map Tm.fst .fst h

theorem betaEta_snd {p p' : Γ ⊢ A × B} (h : p =βη p') :
    Tm.snd p =βη Tm.snd p' :=
  betaEta_map Tm.snd .snd h

end LambdaCalculus.Intrinsic.StlcProd

end Cslib
