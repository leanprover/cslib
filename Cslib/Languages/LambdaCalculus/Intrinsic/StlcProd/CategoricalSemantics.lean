/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Languages.LambdaCalculus.Intrinsic.StlcProd.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian

/-! # λ-calculus

The simply typed λ-calculus, with an intrinsic representation of syntax.

## References

-/

@[expose] public section

namespace Cslib

namespace LambdaCalculus.Intrinsic.StlcProd

variable {G : Type}

def ClosedTm (A : Ty G) := [] ⊢ A

instance closedSetoid (A : Ty G) : Setoid (ClosedTm A) where
  r t u := t =βη u
  iseqv := Relation.EqvGen.is_equivalence Step

def SynHom (A B : Ty G) := Quotient (closedSetoid (A ⇒ B))

def emptyRen (Γ : Ctx G) : Var.Ren [] Γ := fun x => Fin.elim0 x.1

def ClosedTm.weaken (t : ClosedTm A) (Γ : Ctx G) : Γ ⊢ A :=
  Tm.rename (emptyRen Γ) t

theorem ext_comp (ρ : Var.Ren Γ Δ) (τ : Var.Ren Δ Θ) {A B : Ty G}
    (x : B :: Γ ∋ A) : Var.ext τ (Var.ext ρ x) = Var.ext (fun x => τ (ρ x)) x := by
  induction x using Var.cases <;> rfl

theorem rename_comp (ρ : Var.Ren Γ Δ) (τ : Var.Ren Δ Θ) (t : Γ ⊢ A) :
    Tm.rename τ (Tm.rename ρ t) = Tm.rename (fun x => τ (ρ x)) t := by
  induction t generalizing Δ Θ with
  | var x => rfl
  | @lam Γ X Y N ih =>
      simp only [Tm.rename]
      rw [ih]
      have he : (fun {Z} x => Var.ext (B := X) τ (Var.ext (B := X) ρ x) :
          Var.Ren (X :: Γ) (X :: Θ)) =
          (fun {Z} x => Var.ext (B := X) (fun x => τ (ρ x)) x) := by
        funext Z x
        exact ext_comp ρ τ x
      rw [he]
  | app f a ihf iha => simp only [Tm.rename, ihf, iha]
  | pair l r ihl ihr => simp only [Tm.rename, ihl, ihr]
  | fst p ih => simp only [Tm.rename, ih]
  | snd p ih => simp only [Tm.rename, ih]
  | unit => rfl

theorem rename_id (t : Γ ⊢ A) : Tm.rename (fun x => x) t = t := by
  induction t with
  | var x => rfl
  | @lam Γ X Y N ih =>
      simp only [Tm.rename]
      have he : (fun {Z} x => Var.ext (B := X) (fun x => x) x :
          Var.Ren (X :: Γ) (X :: Γ)) = (fun {_} x => x) := by
        funext Z x
        induction x using Var.cases <;> rfl
      rw [he, ih]
  | app f a ihf iha => simp only [Tm.rename, ihf, iha]
  | pair l r ihl ihr => simp only [Tm.rename, ihl, ihr]
  | fst p ih => simp only [Tm.rename, ih]
  | snd p ih => simp only [Tm.rename, ih]
  | unit => rfl

theorem rename_weaken (ρ : Var.Ren Γ Δ) (t : ClosedTm A) :
    Tm.rename ρ (t.weaken Γ) = t.weaken Δ := by
  unfold ClosedTm.weaken
  calc
    Tm.rename ρ (Tm.rename (emptyRen Γ) t) =
        Tm.rename (fun x => ρ (emptyRen Γ x)) t := rename_comp _ _ _
    _ = Tm.rename (emptyRen Δ) t := by
      congr 1
      funext X x
      exact Fin.elim0 x.1

theorem weaken_one (t : ClosedTm (A ⇒ B)) :
    t.weaken [A] = Tm.rename (.succ (B := A)) t := by
  unfold ClosedTm.weaken
  congr 1
  funext X x
  exact Fin.elim0 x.1

@[simp]
theorem ClosedTm.weaken_lam (t : [A] ⊢ B) (Γ : Ctx G) :
    ClosedTm.weaken (.lam t) Γ =
      .lam (Tm.rename (Var.ext (emptyRen Γ)) t) := rfl

theorem rename_exts (ρ : Var.Ren Δ Θ) (σ : Tm.Sub Γ Δ) {A B : Ty G}
    (x : B :: Γ ∋ A) :
    Tm.rename (Var.ext ρ) (Tm.exts σ x) = Tm.exts (fun x => Tm.rename ρ (σ x)) x := by
  induction x using Var.cases with
  | zero => rfl
  | succ x =>
      simp only [Tm.exts_succ]
      calc
        Tm.rename (Var.ext ρ) (Tm.rename .succ (σ x)) =
            Tm.rename (fun y => Var.ext ρ (.succ y)) (σ x) := rename_comp _ _ _
        _ = Tm.rename (fun y => .succ (ρ y)) (σ x) := rfl
        _ = Tm.rename .succ (Tm.rename ρ (σ x)) :=
          (rename_comp _ _ _).symm

theorem rename_subst (ρ : Var.Ren Δ Θ) (σ : Tm.Sub Γ Δ) (t : Γ ⊢ A) :
    Tm.rename ρ (Tm.subst σ t) = Tm.subst (fun x => Tm.rename ρ (σ x)) t := by
  induction t generalizing Δ Θ with
  | var x => rfl
  | @lam Γ X Y N ih =>
      simp only [Tm.subst, Tm.rename]
      rw [ih (Var.ext ρ)]
      have he : (fun {Z} x => Tm.rename (Var.ext ρ) (Tm.exts σ x) :
          Tm.Sub (X :: Γ) (X :: Θ)) =
          (fun {Z} x => Tm.exts (fun x => Tm.rename ρ (σ x)) x) := by
        funext Z x
        exact rename_exts ρ σ x
      rw [he]
  | app f a ihf iha => simp only [Tm.subst, Tm.rename, ihf, iha]
  | pair l r ihl ihr => simp only [Tm.subst, Tm.rename, ihl, ihr]
  | fst p ih => simp only [Tm.subst, Tm.rename, ih]
  | snd p ih => simp only [Tm.subst, Tm.rename, ih]
  | unit => rfl

theorem exts_ext (σ : Tm.Sub Δ Θ) (ρ : Var.Ren Γ Δ) {A B : Ty G}
    (x : B :: Γ ∋ A) :
    Tm.exts σ (Var.ext ρ x) = Tm.exts (fun x => σ (ρ x)) x := by
  induction x using Var.cases <;> rfl

theorem subst_rename (σ : Tm.Sub Δ Θ) (ρ : Var.Ren Γ Δ) (t : Γ ⊢ A) :
    Tm.subst σ (Tm.rename ρ t) = Tm.subst (fun x => σ (ρ x)) t := by
  induction t generalizing Δ Θ with
  | var x => rfl
  | @lam Γ X Y N ih =>
      simp only [Tm.rename, Tm.subst]
      rw [ih]
      have he : (fun {Z} x => Tm.exts σ (Var.ext ρ x) :
          Tm.Sub (X :: Γ) (X :: Θ)) =
          (fun {Z} x => Tm.exts (fun x => σ (ρ x)) x) := by
        funext Z x
        exact exts_ext σ ρ x
      rw [he]
  | app f a ihf iha => simp only [Tm.rename, Tm.subst, ihf, iha]
  | pair l r ihl ihr => simp only [Tm.rename, Tm.subst, ihl, ihr]
  | fst p ih => simp only [Tm.rename, Tm.subst, ih]
  | snd p ih => simp only [Tm.rename, Tm.subst, ih]
  | unit => rfl

theorem subst_vars (ρ : Var.Ren Γ Δ) (t : Γ ⊢ A) :
    Tm.subst (fun x => .var (ρ x)) t = Tm.rename ρ t := by
  induction t generalizing Δ with
  | var x => rfl
  | @lam Γ X Y N ih =>
      simp only [Tm.subst, Tm.rename]
      have he : (Tm.exts (B := X) (fun x => .var (ρ x)) :
          Tm.Sub (X :: Γ) (X :: Δ)) =
          ((fun {Z : Ty _} (x : X :: Γ ∋ Z) =>
            Tm.var (Var.ext (B := X) ρ x)) : Tm.Sub (X :: Γ) (X :: Δ)) := by
        funext Z x
        induction x using Var.cases <;> rfl
      rw [he, ih]
  | app f a ihf iha => simp only [Tm.subst, Tm.rename, ihf, iha]
  | pair l r ihl ihr => simp only [Tm.subst, Tm.rename, ihl, ihr]
  | fst p ih => simp only [Tm.subst, Tm.rename, ih]
  | snd p ih => simp only [Tm.subst, Tm.rename, ih]
  | unit => rfl

theorem subst_exts_comp (τ : Tm.Sub Δ Θ) (σ : Tm.Sub Γ Δ) {A B : Ty G}
    (x : B :: Γ ∋ A) :
    Tm.subst (Tm.exts τ) (Tm.exts σ x) =
      Tm.exts (fun x => Tm.subst τ (σ x)) x := by
  induction x using Var.cases with
  | zero => rfl
  | succ x =>
      rw [Tm.exts_succ σ x, Tm.exts_succ (fun x => Tm.subst τ (σ x)) x]
      rw [subst_rename (Tm.exts τ) .succ (σ x)]
      rw [rename_subst .succ τ (σ x)]
      congr 1

theorem subst_comp (τ : Tm.Sub Δ Θ) (σ : Tm.Sub Γ Δ) (t : Γ ⊢ A) :
    Tm.subst τ (Tm.subst σ t) = Tm.subst (fun x => Tm.subst τ (σ x)) t := by
  induction t generalizing Δ Θ with
  | var x => rfl
  | @lam Γ X Y body ih =>
      simp only [Tm.subst]
      rw [ih]
      have he : ((fun {Z} x => Tm.subst (Tm.exts τ) (Tm.exts σ x)) :
          Tm.Sub (X :: Γ) (X :: Θ)) =
          (Tm.exts (B := X) (fun {Z} (x : Γ ∋ Z) => Tm.subst τ (σ x)) :
            Tm.Sub (X :: Γ) (X :: Θ)) := by
        funext Z x
        exact subst_exts_comp τ σ x
      rw [he]
  | app f a ihf iha => simp only [Tm.subst, ihf, iha]
  | pair l r ihl ihr => simp only [Tm.subst, ihl, ihr]
  | fst p ih => simp only [Tm.subst, ih]
  | snd p ih => simp only [Tm.subst, ih]
  | unit => rfl

theorem rename_inst (ρ : Var.Ren Γ Δ) (body : A :: Γ ⊢ B) (arg : Γ ⊢ A) :
    Tm.rename ρ (body [ arg ]) = (Tm.rename (Var.ext ρ) body) [ Tm.rename ρ arg ] := by
  unfold Tm.inst
  rw [rename_subst, subst_rename]
  congr 1
  funext X x
  induction x using Var.cases <;> rfl

@[simp]
theorem inst_weaken (t : ClosedTm B) (arg : Γ ⊢ A) :
    (t.weaken (A :: Γ)) [ arg ] = t.weaken Γ := by
  unfold Tm.inst ClosedTm.weaken
  rw [subst_rename (Tm.single arg) (emptyRen (A :: Γ)) t]
  have he : (fun {X} x => Tm.single arg (emptyRen (A :: Γ) x) : Tm.Sub [] Γ) =
      (fun {X} x => .var (emptyRen Γ x)) := by
    funext X x
    exact Fin.elim0 x.1
  rw [he]
  exact subst_vars (emptyRen Γ) t

@[simp]
theorem subst_single_weaken (t : ClosedTm B) (arg : Γ ⊢ A) :
    Tm.subst (Tm.single arg) (t.weaken (A :: Γ)) = t.weaken Γ :=
  inst_weaken t arg

@[simp]
theorem subst_weaken_closed (σ : Tm.Sub Γ Δ) (t : ClosedTm A) :
    Tm.subst σ (t.weaken Γ) = t.weaken Δ := by
  unfold ClosedTm.weaken
  rw [subst_rename σ (emptyRen Γ) t]
  have he : (fun {X} x => σ (emptyRen Γ x) : Tm.Sub [] Δ) =
      (fun {X} x => .var (emptyRen Δ x)) := by
    funext X x
    exact Fin.elim0 x.1
  rw [he]
  exact subst_vars (emptyRen Δ) t

theorem rename_step (ρ : Var.Ren Γ Δ) {t u : Γ ⊢ A} (h : Step t u) :
    Step (Tm.rename ρ t) (Tm.rename ρ u) := by
  induction h generalizing Δ with
  | lam h ih => exact .lam (ih (Var.ext ρ))
  | app₁ h ih => exact .app₁ (ih ρ)
  | app₂ h ih => exact .app₂ (ih ρ)
  | betaLam =>
      simp only [Tm.rename]
      rw [rename_inst]
      exact .betaLam
  | pair₁ h ih => exact .pair₁ (ih ρ)
  | pair₂ h ih => exact .pair₂ (ih ρ)
  | fst h ih => exact .fst (ih ρ)
  | snd h ih => exact .snd (ih ρ)
  | betaFst => exact .betaFst
  | betaSnd => exact .betaSnd
  | @etaLam Γ A B f =>
      simp only [Tm.rename]
      have he : Tm.rename (Var.ext (B := A) ρ)
          (Tm.rename (.succ (B := A)) f) =
          Tm.rename (.succ (B := A)) (Tm.rename ρ f) :=
        calc
          _ = Tm.rename (fun x => Var.ext (B := A) ρ (.succ x)) f :=
            rename_comp _ _ _
          _ = Tm.rename (fun x => .succ (ρ x)) f := rfl
          _ = _ := (rename_comp _ _ _).symm
      rw [he]
      exact .etaLam _
  | etaPair p => exact .etaPair _
  | etaUnit t => exact .etaUnit _

theorem betaEta_weaken {t u : ClosedTm A} (h : t =βη u) (Γ : Ctx G) :
    t.weaken Γ =βη u.weaken Γ := by
  exact betaEta_map (fun t : ClosedTm A => ClosedTm.weaken t Γ)
    (fun h => rename_step (emptyRen Γ) h) h

def idTerm (A : Ty G) : ClosedTm (A ⇒ A) := .lam (.var .zero)

def compTerm (f : ClosedTm (A ⇒ B)) (g : ClosedTm (B ⇒ C)) : ClosedTm (A ⇒ C) :=
  .lam (.app (g.weaken [A]) (.app (f.weaken [A]) (.var .zero)))

theorem weaken_compTerm (f : ClosedTm (A ⇒ B)) (g : ClosedTm (B ⇒ C)) (Γ : Ctx G) :
    (compTerm f g).weaken Γ =
      .lam (.app (g.weaken (A :: Γ)) (.app (f.weaken (A :: Γ)) (.var .zero))) := by
  unfold compTerm
  rw [ClosedTm.weaken_lam]
  simp only [Tm.rename]
  rw [rename_weaken, rename_weaken]
  rfl

theorem compTerm_congr {f f' : ClosedTm (A ⇒ B)} {g g' : ClosedTm (B ⇒ C)}
    (hf : f =βη f') (hg : g =βη g') : compTerm f g =βη compTerm f' g' :=
  betaEta_lam (betaEta_app (betaEta_weaken hg _) <|
    betaEta_app (betaEta_weaken hf _) (Relation.EqvGen.refl _))

theorem compTerm_id (f : ClosedTm (A ⇒ B)) : compTerm f (idTerm B) =βη f := by
  unfold compTerm idTerm
  rw [weaken_one f]
  simp only [ClosedTm.weaken, Tm.rename]
  exact Relation.EqvGen.trans _ _ _
    (.rel _ _ (.lam .betaLam)) (.rel _ _ (.etaLam _))

/-- Currying on representatives of morphisms in the syntactic category. -/
def curryTerm (f : ClosedTm ((A × B) ⇒ C)) : ClosedTm (B ⇒ (A ⇒ C)) :=
  .lam (.lam (.app (f.weaken [A, B])
    (.pair (.var .zero) (.var (.succ .zero)))))

/-- Uncurrying on representatives of morphisms in the syntactic category. -/
def uncurryTerm (f : ClosedTm (B ⇒ (A ⇒ C))) : ClosedTm ((A × B) ⇒ C) :=
  .lam (.app (.app (f.weaken [A × B]) (.snd (.var .zero)))
    (.fst (.var .zero)))

theorem curryTerm_congr {f f' : ClosedTm ((A × B) ⇒ C)} (h : f =βη f') :
    curryTerm f =βη curryTerm f' :=
  betaEta_lam (betaEta_lam (betaEta_app (betaEta_weaken h _) (.refl _)))

theorem uncurryTerm_congr {f f' : ClosedTm (B ⇒ (A ⇒ C))} (h : f =βη f') :
    uncurryTerm f =βη uncurryTerm f' :=
  betaEta_lam (betaEta_app
    (betaEta_app (betaEta_weaken h _) (.refl _)) (.refl _))

theorem weaken_curryTerm (f : ClosedTm ((A × B) ⇒ C)) (Γ : Ctx G) :
    (curryTerm f).weaken Γ =
      .lam (.lam (.app (f.weaken (A :: B :: Γ))
        (.pair (.var .zero) (.var (.succ .zero))))) := by
  unfold curryTerm
  rw [ClosedTm.weaken_lam]
  simp only [Tm.rename]
  rw [rename_weaken]
  rfl

theorem uncurry_curryTerm (f : ClosedTm ((A × B) ⇒ C)) :
    uncurryTerm (curryTerm f) =βη f := by
  unfold uncurryTerm
  rw [weaken_curryTerm]
  apply Relation.EqvGen.trans _ _ _ (.rel _ _ (Step.lam (Step.app₁ Step.betaLam)))
  apply Relation.EqvGen.trans _ _ _ (.rel _ _ (Step.lam Step.betaLam))
  simp only [Tm.inst, Tm.subst, Tm.single_zero,
    Tm.exts_zero, Tm.exts_succ, Tm.rename,
    subst_weaken_closed]
  apply Relation.EqvGen.trans _ _ _
    (betaEta_lam (betaEta_app (.refl _) (.rel _ _ (.etaPair _))))
  rw [weaken_one]
  exact .rel _ _ (.etaLam f)

theorem weaken_uncurryTerm (f : ClosedTm (B ⇒ (A ⇒ C))) (Γ : Ctx G) :
    (uncurryTerm f).weaken Γ =
      .lam (.app (.app (f.weaken ((A × B) :: Γ)) (.snd (.var .zero)))
        (.fst (.var .zero))) := by
  unfold uncurryTerm
  rw [ClosedTm.weaken_lam]
  simp only [Tm.rename]
  rw [rename_weaken]
  rfl

theorem curry_uncurryTerm (f : ClosedTm (B ⇒ (A ⇒ C))) :
    curryTerm (uncurryTerm f) =βη f := by
  unfold curryTerm
  rw [weaken_uncurryTerm]
  apply Relation.EqvGen.trans _ _ _
    (.rel _ _ (Step.lam (Step.lam Step.betaLam)))
  simp only [Tm.inst, Tm.subst, Tm.single_zero,
    subst_weaken_closed]
  apply Relation.EqvGen.trans _ _ _
    (.rel _ _ (.lam (.lam (.app₁ (.app₂ .betaSnd)))))
  apply Relation.EqvGen.trans _ _ _
    (.rel _ _ (.lam (.lam (.app₂ .betaFst))))
  rw [← rename_weaken .succ f]
  let q : [B] ⊢ A ⇒ C := .app (f.weaken [B]) (.var .zero)
  apply Relation.EqvGen.trans _ _ _ (.rel _ _ (.lam (.etaLam q)))
  dsimp [q]
  rw [weaken_one]
  exact .rel _ _ (.etaLam f)

def curryEquiv (A B C : Ty G) : SynHom (A × B) C ≃ SynHom B (A ⇒ C) where
  toFun f := Quotient.liftOn f (fun f => Quotient.mk' (curryTerm f))
    (fun _ _ h => Quotient.sound (curryTerm_congr h))
  invFun f := Quotient.liftOn f (fun f => Quotient.mk' (uncurryTerm f))
    (fun _ _ h => Quotient.sound (uncurryTerm_congr h))
  left_inv f := by
    induction f using Quotient.inductionOn with
    | _ f => exact Quotient.sound (uncurry_curryTerm f)
  right_inv f := by
    induction f using Quotient.inductionOn with
    | _ f => exact Quotient.sound (curry_uncurryTerm f)

@[simp]
theorem curryEquiv_apply_mk (f : ClosedTm ((A × B) ⇒ C)) :
    curryEquiv A B C (Quotient.mk' f) = Quotient.mk' (curryTerm f) := rfl

@[simp]
theorem curryEquiv_symm_apply_mk (f : ClosedTm (B ⇒ (A ⇒ C))) :
    (curryEquiv A B C).symm (Quotient.mk' f) = Quotient.mk' (uncurryTerm f) := rfl

def ihomMapTerm (A : Ty G) (f : ClosedTm (B ⇒ C)) : ClosedTm ((A ⇒ B) ⇒ (A ⇒ C)) :=
  .lam (.lam (.app (f.weaken [A, A ⇒ B])
    (.app (.var (.succ .zero)) (.var .zero))))

theorem ihomMapTerm_congr (A : Ty G) {f f' : ClosedTm (B ⇒ C)} (h : f =βη f') :
    ihomMapTerm A f =βη ihomMapTerm A f' :=
  betaEta_lam (betaEta_lam (betaEta_app (betaEta_weaken h _) (.refl _)))

theorem weaken_ihomMapTerm (A : Ty G) (f : ClosedTm (B ⇒ C)) (Γ : Ctx G) :
    (ihomMapTerm A f).weaken Γ =
      .lam (.lam (.app (f.weaken (A :: (A ⇒ B) :: Γ))
        (.app (.var (.succ .zero)) (.var .zero)))) := by
  unfold ihomMapTerm
  rw [ClosedTm.weaken_lam]
  simp only [Tm.rename]
  rw [rename_weaken]
  rfl

theorem ihomMapTerm_id (A B : Ty G) : ihomMapTerm A (idTerm B) =βη idTerm (A ⇒ B) := by
  unfold ihomMapTerm idTerm
  simp only [ClosedTm.weaken, Tm.rename]
  apply Relation.EqvGen.trans _ _ _ (.rel _ _ (.lam (.lam .betaLam)))
  simp only [Tm.inst, Tm.subst]
  exact .rel _ _ (.lam (.etaLam ((.var .zero) : [A ⇒ B] ⊢ A ⇒ B)))

theorem ihomMapTerm_comp (A : Ty G) (f : ClosedTm (B ⇒ C)) (g : ClosedTm (C ⇒ D)) :
    ihomMapTerm A (compTerm f g) =βη
      compTerm (ihomMapTerm A f) (ihomMapTerm A g) := by
  let n : ClosedTm ((A ⇒ B) ⇒ (A ⇒ D)) :=
    .lam (.lam (.app (g.weaken [A, A ⇒ B])
      (.app (f.weaken [A, A ⇒ B])
        (.app (.var (.succ .zero)) (.var .zero)))))
  apply Relation.EqvGen.trans _ n _
  · unfold ihomMapTerm
    rw [weaken_compTerm]
    apply Relation.EqvGen.trans _ _ _
      (.rel _ _ (Step.lam (Step.lam Step.betaLam)))
    simp only [Tm.inst, Tm.subst, Tm.single_zero,
      subst_weaken_closed]
    exact .refl _
  · apply Relation.EqvGen.symm _ _
    unfold compTerm
    rw [weaken_ihomMapTerm, weaken_ihomMapTerm]
    apply Relation.EqvGen.trans _ _ _ (.rel _ _ (.lam (.app₂ .betaLam)))
    apply Relation.EqvGen.trans _ _ _ (.rel _ _ (.lam .betaLam))
    simp only [Tm.inst, Tm.subst, Tm.single_zero,
      Tm.exts_zero, Tm.exts_succ, Tm.rename,
      subst_weaken_closed]
    apply Relation.EqvGen.trans _ _ _ (.rel _ _ (.lam (.lam (.app₂ .betaLam))))
    simp only [Tm.inst, Tm.subst]
    rw [subst_rename]
    have hs : (fun {X} (x : [A, A ⇒ B] ∋ X) =>
        Tm.single (.var .zero) (Var.ext .succ x)) =
        ((fun {_} x => Tm.var x) : Tm.Sub [A, A ⇒ B]
          [A, A ⇒ B]) := by
      funext X x
      induction x using Var.cases <;> rfl
    rw [hs]
    have ht := subst_vars
      (fun {_} x => x : Var.Ren [A, A ⇒ B] [A, A ⇒ B])
      (f.weaken [A, A ⇒ B])
    rw [rename_id] at ht
    rw [ht]
    exact .refl _

theorem curryTerm_comp (f : ClosedTm ((A × B) ⇒ C)) (g : ClosedTm (C ⇒ D)) :
    curryTerm (compTerm f g) =βη
      compTerm (curryTerm f) (ihomMapTerm A g) := by
  let n : ClosedTm (B ⇒ (A ⇒ D)) :=
    .lam (.lam (.app (g.weaken [A, B])
      (.app (f.weaken [A, B])
        (.pair (.var .zero) (.var (.succ .zero))))))
  apply Relation.EqvGen.trans _ n _
  · unfold curryTerm
    rw [weaken_compTerm]
    apply Relation.EqvGen.trans _ _ _
      (.rel _ _ (Step.lam (Step.lam Step.betaLam)))
    simp only [Tm.inst, Tm.subst, Tm.single_zero,
      subst_weaken_closed]
    exact .refl _
  · apply Relation.EqvGen.symm _ _
    unfold compTerm
    rw [weaken_curryTerm, weaken_ihomMapTerm]
    apply Relation.EqvGen.trans _ _ _ (.rel _ _ (.lam (.app₂ .betaLam)))
    apply Relation.EqvGen.trans _ _ _ (.rel _ _ (.lam .betaLam))
    simp only [Tm.inst, Tm.subst, Tm.single_zero,
      Tm.exts_zero, Tm.exts_succ, Tm.rename,
      subst_weaken_closed]
    apply Relation.EqvGen.trans _ _ _ (.rel _ _ (.lam (.lam (.app₂ .betaLam))))
    simp only [Tm.inst, Tm.subst]
    rw [subst_rename]
    have hs : (fun {X} (x : [A, B] ∋ X) =>
        Tm.single (.var .zero) (Var.ext .succ x)) =
        ((fun {_} x => Tm.var x) : Tm.Sub [A, B] [A, B]) := by
      funext X x
      induction x using Var.cases <;> rfl
    rw [hs]
    have ht := subst_vars
      (fun {_} x => x : Var.Ren [A, B] [A, B])
      (f.weaken [A, B])
    rw [rename_id] at ht
    rw [ht]
    exact .refl _

theorem compTerm_assoc (f : ClosedTm (W ⇒ X)) (g : ClosedTm (X ⇒ Y))
    (h : ClosedTm (Y ⇒ Z)) :
    compTerm (compTerm f g) h =βη compTerm f (compTerm g h) := by
  rw [show compTerm (compTerm f g) h =
      Tm.lam (.app (h.weaken [W])
        (.app ((compTerm f g).weaken [W]) (.var .zero))) from rfl,
    show compTerm f (compTerm g h) =
      Tm.lam (.app ((compTerm g h).weaken [W])
        (.app (f.weaken [W]) (.var .zero))) from rfl]
  rw [weaken_compTerm, weaken_compTerm]
  let n := Tm.lam (.app (h.weaken [W])
      (.app (g.weaken [W])
        (.app (f.weaken [W]) (.var .zero))))
  have hl : Step
      (.lam (.app (h.weaken [W])
        (.app (.lam (.app (g.weaken [W, W])
          (.app (f.weaken [W, W]) (.var .zero))))
            (.var .zero)))) n := by
    dsimp [n]
    apply Step.lam
    apply Step.app₂
    simpa only [Tm.inst, Tm.subst, Tm.single_zero, Tm.single_succ,
      subst_single_weaken] using
      (Step.betaLam : Step
      (Tm.app (Tm.lam (Tm.app (g.weaken [W, W])
        (Tm.app (f.weaken [W, W]) (.var .zero))))
          (.var .zero)) _)
  have hr : Step
      (.lam (.app (.lam (.app (h.weaken [X, W])
        (.app (g.weaken [X, W]) (.var .zero))))
        (.app (f.weaken [W]) (.var .zero)))) n := by
    dsimp [n]
    apply Step.lam
    simpa only [Tm.inst, Tm.subst, Tm.single_zero, Tm.single_succ,
      subst_single_weaken] using
      (Step.betaLam : Step
      (Tm.app (Tm.lam (Tm.app (h.weaken [X, W])
        (Tm.app (g.weaken [X, W]) (.var .zero))))
          (.app (f.weaken [W]) (.var .zero))) _)
  exact Relation.EqvGen.trans _ _ _ (.rel _ _ hl)
    (Relation.EqvGen.symm _ _ (.rel _ _ hr))

instance SynObj.instCategoryTy : CategoryTheory.Category (Ty G) where
  Hom X Y := SynHom X Y
  id X := Quotient.mk' (idTerm X)
  comp f g := Quotient.liftOn₂ f g
    (fun f g => Quotient.mk' (compTerm f g))
    (fun _ _ _ _ hf hg => Quotient.sound (compTerm_congr hf hg))
  id_comp f := by
    induction f using Quotient.inductionOn with
    | _ f =>
      apply Quotient.sound
      unfold compTerm idTerm
      rw [weaken_one f]
      simp only [ClosedTm.weaken, Tm.rename]
      exact Relation.EqvGen.trans _ _ _
        (.rel _ _ (.lam (.app₂ .betaLam))) (.rel _ _ (.etaLam _))
  comp_id f := by
    induction f using Quotient.inductionOn with
    | _ f =>
      apply Quotient.sound
      unfold compTerm idTerm
      rw [weaken_one f]
      simp only [ClosedTm.weaken, Tm.rename]
      exact Relation.EqvGen.trans _ _ _
        (.rel _ _ (.lam .betaLam)) (.rel _ _ (.etaLam _))
  assoc {W X Y Z} f g h := by
    induction f using Quotient.inductionOn with
    | _ f =>
      induction g using Quotient.inductionOn with
      | _ g =>
        induction h using Quotient.inductionOn with
        | _ h =>
          exact Quotient.sound (compTerm_assoc f g h)

def terminalTerm (A : Ty G) : ClosedTm (A ⇒ .unit) := .lam .unit

def fstTerm (A B : Ty G) : ClosedTm ((A × B) ⇒ A) := .lam (.fst (.var .zero))

def sndTerm (A B : Ty G) : ClosedTm ((A × B) ⇒ B) := .lam (.snd (.var .zero))

def pairTerm (f : ClosedTm (A ⇒ B)) (g : ClosedTm (A ⇒ C)) : ClosedTm (A ⇒ (B × C)) :=
  .lam (.pair (.app (f.weaken [A]) (.var .zero))
    (.app (g.weaken [A]) (.var .zero)))

@[simp] theorem weaken_fstTerm (A B : Ty G) (Γ : Ctx G) :
    (fstTerm A B).weaken Γ = .lam (.fst (.var .zero)) := rfl

@[simp] theorem weaken_sndTerm (A B : Ty G) (Γ : Ctx G) :
    (sndTerm A B).weaken Γ = .lam (.snd (.var .zero)) := rfl

theorem weaken_pairTerm (f : ClosedTm (A ⇒ B)) (g : ClosedTm (A ⇒ C)) (Γ : Ctx G) :
    (pairTerm f g).weaken Γ =
      .lam (.pair (.app (f.weaken (A :: Γ)) (.var .zero))
        (.app (g.weaken (A :: Γ)) (.var .zero))) := by
  unfold pairTerm
  rw [ClosedTm.weaken_lam]
  simp only [Tm.rename]
  rw [rename_weaken, rename_weaken]
  rfl

theorem terminalTerm_unique (f : ClosedTm (A ⇒ .unit)) : f =βη terminalTerm A := by
  apply Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (.rel _ _ (.etaLam f)))
  exact .rel _ _ (.lam (.etaUnit _))

theorem pairTerm_fst (f : ClosedTm (A ⇒ B)) (g : ClosedTm (A ⇒ C)) :
    compTerm (pairTerm f g) (fstTerm B C) =βη f := by
  unfold compTerm
  rw [weaken_fstTerm, weaken_pairTerm]
  apply Relation.EqvGen.trans _ _ _ (.rel _ _ (.lam .betaLam))
  apply Relation.EqvGen.trans _ _ _
    (.rel _ _ (by
      apply Step.lam
      apply Step.fst
      simpa only [Tm.inst, Tm.subst, Tm.single_zero, Tm.single_succ,
        subst_single_weaken] using
        (Step.betaLam : Step
          (Tm.app (Tm.lam (.pair
            (.app (f.weaken [A, A]) (.var .zero))
            (.app (g.weaken [A, A]) (.var .zero)))) (.var .zero)) _)))
  apply Relation.EqvGen.trans _ _ _ (.rel _ _ (.lam .betaFst))
  exact .rel _ _ (by
    simpa only [Tm.inst, Tm.subst, Tm.single_zero, Tm.single_succ,
      Tm.exts_zero, Tm.exts_succ, Tm.rename,
      subst_single_weaken, weaken_one] using Step.etaLam f)

theorem pairTerm_snd (f : ClosedTm (A ⇒ B)) (g : ClosedTm (A ⇒ C)) :
    compTerm (pairTerm f g) (sndTerm B C) =βη g := by
  unfold compTerm
  rw [weaken_sndTerm, weaken_pairTerm]
  apply Relation.EqvGen.trans _ _ _ (.rel _ _ (.lam .betaLam))
  apply Relation.EqvGen.trans _ _ _
    (.rel _ _ (by
      apply Step.lam
      apply Step.snd
      simpa only [Tm.inst, Tm.subst, Tm.single_zero, Tm.single_succ,
        subst_single_weaken] using
        (Step.betaLam : Step
          (Tm.app (Tm.lam (.pair
            (.app (f.weaken [A, A]) (.var .zero))
            (.app (g.weaken [A, A]) (.var .zero)))) (.var .zero)) _)))
  apply Relation.EqvGen.trans _ _ _ (.rel _ _ (.lam .betaSnd))
  exact .rel _ _ (by simpa only [weaken_one] using Step.etaLam g)

theorem pairTerm_unique (f : ClosedTm (A ⇒ (B × C)))
    (l : ClosedTm (A ⇒ B)) (r : ClosedTm (A ⇒ C))
    (hl : compTerm f (fstTerm B C) =βη l)
    (hr : compTerm f (sndTerm B C) =βη r) : f =βη pairTerm l r := by
  have hc : pairTerm (compTerm f (fstTerm B C)) (compTerm f (sndTerm B C)) =βη
      pairTerm l r := betaEta_lam (betaEta_pair
        (betaEta_app (betaEta_weaken hl _) (.refl _))
        (betaEta_app (betaEta_weaken hr _) (.refl _)))
  apply Relation.EqvGen.trans _ _ _ _ hc
  apply Relation.EqvGen.symm _ _
  unfold pairTerm
  rw [weaken_compTerm, weaken_compTerm, weaken_fstTerm, weaken_sndTerm]
  apply Relation.EqvGen.trans _ _ _ (.rel _ _ (.lam (.pair₁ .betaLam)))
  apply Relation.EqvGen.trans _ _ _ (.rel _ _ (.lam (.pair₁ .betaLam)))
  apply Relation.EqvGen.trans _ _ _ (.rel _ _ (.lam (.pair₂ .betaLam)))
  apply Relation.EqvGen.trans _ _ _ (.rel _ _ (.lam (.pair₂ .betaLam)))
  apply Relation.EqvGen.trans _ _ _ (.rel _ _ (.lam (.etaPair _)))
  exact .rel _ _ (by
    simpa only [Tm.inst, Tm.subst, Tm.single_zero, Tm.single_succ,
      Tm.exts_zero, Tm.exts_succ, Tm.rename,
      subst_single_weaken, weaken_one] using Step.etaLam f)

namespace SynObj

open CategoryTheory
open Limits MonoidalCategory

def terminalCone : LimitCone (Functor.empty.{0} (Ty G)) where
  cone := asEmptyCone Ty.unit
  isLimit := {
    lift := fun s => Quotient.mk' (terminalTerm s.pt)
    fac := by rintro s ⟨j⟩; exact j.elim
    uniq := by
      intro s m _
      induction m using Quotient.inductionOn with
      | _ f => exact Quotient.sound (terminalTerm_unique f) }

def productFan (X Y : Ty G) : BinaryFan X Y :=
  BinaryFan.mk (Quotient.mk' (fstTerm X Y))
    (Quotient.mk' (sndTerm X Y))

def productIsLimit (X Y : Ty G) : IsLimit (productFan X Y) :=
  BinaryFan.IsLimit.mk (productFan X Y)
    (fun {T} f g => Quotient.liftOn₂ f g
      (fun f g => Quotient.mk' (pairTerm f g))
      (by
        intro f f' g g' hf hg
        exact Quotient.sound (betaEta_lam (betaEta_pair
          (betaEta_app (betaEta_weaken hf _) (.refl _))
          (betaEta_app (betaEta_weaken hg _) (.refl _))))))
    (by
      intro T f g
      induction f using Quotient.inductionOn with
      | _ f =>
        induction g using Quotient.inductionOn with
        | _ g => exact Quotient.sound (pairTerm_fst f g))
    (by
      intro T f g
      induction f using Quotient.inductionOn with
      | _ f =>
        induction g using Quotient.inductionOn with
        | _ g => exact Quotient.sound (pairTerm_snd f g))
    (by
      intro T f g m hl hr
      induction f using Quotient.inductionOn with
      | _ f =>
        induction g using Quotient.inductionOn with
        | _ g =>
          induction m using Quotient.inductionOn with
          | _ m => exact Quotient.sound (pairTerm_unique m f g
              (Quotient.exact hl) (Quotient.exact hr)))

def productCone (X Y : Ty G) : LimitCone (pair X Y) :=
  ⟨productFan X Y, productIsLimit X Y⟩

noncomputable instance : CartesianMonoidalCategory (Ty G) :=
  .ofChosenFiniteProducts terminalCone productCone

def ihomFunctor (A : Ty G) : Functor (Ty G) (Ty G) where
  obj B := A ⇒ B
  map f := Quotient.liftOn f (fun f => Quotient.mk' (ihomMapTerm A f))
    (fun _ _ h => Quotient.sound (ihomMapTerm_congr A h))
  map_id B := Quotient.sound (ihomMapTerm_id A B)
  map_comp f g := by
    induction f using Quotient.inductionOn with
    | _ f =>
      induction g using Quotient.inductionOn with
      | _ g => exact Quotient.sound (ihomMapTerm_comp A f g)

@[simp]
theorem comp_mk (f : ClosedTm (A ⇒ B)) (g : ClosedTm (B ⇒ C)) :
    @CategoryStruct.comp (Ty G) SynObj.instCategoryTy.toCategoryStruct A B C
      (Quotient.mk' f) (Quotient.mk' g) = Quotient.mk' (compTerm f g) := rfl

def tensorLeftTerm (A : Ty G) (f : ClosedTm (B ⇒ C)) :
    ClosedTm ((A × B) ⇒ (A × C)) :=
  pairTerm (fstTerm A B) (compTerm (sndTerm A B) f)

theorem whiskerLeft_mk_def (A : Ty G) (f : ClosedTm (B ⇒ C)) :
    A ◁ (Quotient.mk' f : B ⟶ C) =
      Quotient.mk' (pairTerm (compTerm (fstTerm A B) (idTerm A))
        (compTerm (sndTerm A B) f)) := rfl

theorem whiskerLeft_mk (A : Ty G) (f : ClosedTm (B ⇒ C)) :
    A ◁ (Quotient.mk' f : B ⟶ C) = Quotient.mk' (tensorLeftTerm A f) := by
  rw [whiskerLeft_mk_def]
  apply Quotient.sound
  exact betaEta_lam (betaEta_pair
    (betaEta_app (betaEta_weaken (compTerm_id (fstTerm A B)) _) (.refl _))
    (.refl _))

theorem tensorLeftTerm_app (A : Ty G) (f : ClosedTm (B ⇒ C)) (p : Γ ⊢ A × B) :
    .app ((tensorLeftTerm A f).weaken Γ) p =βη
      .pair (.fst p) (.app (f.weaken Γ) (.snd p)) := by
  unfold tensorLeftTerm
  rw [weaken_pairTerm]
  apply Relation.EqvGen.trans _ _ _ (.rel _ _ .betaLam)
  simp only [Tm.inst, Tm.subst, Tm.single_zero,
    subst_weaken_closed]
  apply betaEta_pair
  · rw [weaken_fstTerm]
    apply Relation.EqvGen.trans _ _ _ (.rel _ _ .betaLam)
    simp only [Tm.inst, Tm.subst, Tm.single_zero]
    exact .refl _
  · rw [weaken_compTerm]
    apply Relation.EqvGen.trans _ _ _ (.rel _ _ .betaLam)
    simp only [Tm.inst, Tm.subst, Tm.single_zero,
      subst_weaken_closed]
    apply betaEta_app (.refl _)
    rw [weaken_sndTerm]
    apply Relation.EqvGen.trans _ _ _ (.rel _ _ .betaLam)
    simp only [Tm.inst, Tm.subst, Tm.single_zero]
    exact .refl _

theorem uncurryTerm_comp (f : ClosedTm (B ⇒ C))
    (g : ClosedTm (C ⇒ (A ⇒ D))) :
    uncurryTerm (compTerm f g) =βη
      compTerm (tensorLeftTerm A f) (uncurryTerm g) := by
  let n : ClosedTm ((A × B) ⇒ D) :=
    .lam (.app (.app (g.weaken [A × B])
      (.app (f.weaken [A × B]) (.snd (.var .zero))))
      (.fst (.var .zero)))
  apply Relation.EqvGen.trans _ n _
  · unfold uncurryTerm
    rw [weaken_compTerm]
    apply Relation.EqvGen.trans _ _ _ (.rel _ _ (.lam (.app₁ .betaLam)))
    simp only [Tm.inst, Tm.subst, Tm.single_zero,
      subst_weaken_closed]
    exact .refl _
  · apply Relation.EqvGen.symm _ _
    unfold compTerm
    rw [weaken_uncurryTerm]
    apply Relation.EqvGen.trans _ _ _ (.rel _ _ (.lam .betaLam))
    simp only [Tm.inst, Tm.subst, Tm.single_zero,
      subst_weaken_closed]
    let p : [A × B] ⊢ A × B := .var .zero
    let q : [A × B] ⊢ A × C :=
      Tm.app ((tensorLeftTerm A f).weaken [A × B]) p
    have hq : q =βη .pair (.fst p) (.app (f.weaken [A × B]) (.snd p)) :=
      tensorLeftTerm_app A f p
    have hs : .snd q =βη .app (f.weaken [A × B]) (.snd p) :=
      Relation.EqvGen.trans _ _ _ (betaEta_snd hq) (.rel _ _ .betaSnd)
    have hf : .fst q =βη .fst p :=
      Relation.EqvGen.trans _ _ _ (betaEta_fst hq) (.rel _ _ .betaFst)
    exact betaEta_lam (betaEta_app (betaEta_app (.refl _) hs) hf)

theorem curryEquiv_naturality_left_symm_mk (A : Ty G)
    (f : ClosedTm (B' ⇒ B)) (g : ClosedTm (B ⇒ (A ⇒ C))) :
    (curryEquiv A B' C).symm
        (@CategoryStruct.comp (Ty G) SynObj.instCategoryTy.toCategoryStruct
          B' B (A ⇒ C) (Quotient.mk' f) (Quotient.mk' g)) =
      @CategoryStruct.comp (Ty G) SynObj.instCategoryTy.toCategoryStruct
        (A × B') (A × B) C (A ◁ (Quotient.mk' f : B' ⟶ B))
          (Quotient.mk' (uncurryTerm g)) := by
  rw [comp_mk, curryEquiv_symm_apply_mk, whiskerLeft_mk, comp_mk]
  exact Quotient.sound (uncurryTerm_comp f g)

noncomputable def syntacticCoreHomEquiv (A : Ty G) :
    Adjunction.CoreHomEquiv (tensorLeft A) (ihomFunctor A) where
    homEquiv := fun B C => curryEquiv A B C
    homEquiv_naturality_left_symm := by
      intro B' B C f g
      induction f using Quotient.inductionOn with
      | _ f =>
        induction g using Quotient.inductionOn with
        | _ g => exact curryEquiv_naturality_left_symm_mk A f g
    homEquiv_naturality_right := by
      intro B C C' f g
      induction f using Quotient.inductionOn with
      | _ f =>
        induction g using Quotient.inductionOn with
        | _ g => exact Quotient.sound (curryTerm_comp f g)

noncomputable instance syntacticClosed (A : Ty G) : Closed A where
  rightAdj := ihomFunctor A
  adj := Adjunction.mkOfHomEquiv (syntacticCoreHomEquiv A)

noncomputable instance : MonoidalClosed (Ty G) where
  closed A := syntacticClosed A

theorem lift_mk (f : ClosedTm (A ⇒ B)) (g : ClosedTm (A ⇒ C)) :
    CartesianMonoidalCategory.lift
      (T := A) (X := B) (Y := C)
      (Quotient.mk' f : A ⟶ B) (Quotient.mk' g : A ⟶ C) =
      (Quotient.mk' (pairTerm f g) : A ⟶ (B × C)) := by
  rfl

theorem toUnit_mk (A : Ty G) :
    CartesianMonoidalCategory.toUnit A =
      (Quotient.mk' (terminalTerm A) : A ⟶ Ty.unit) := by
  rfl

theorem curry_mk (f : ClosedTm ((A × B) ⇒ C)) :
    @MonoidalClosed.curry (Ty G) _ _ A C B (syntacticClosed A)
      (Quotient.mk' f : (A × B) ⟶ C) =
      (Quotient.mk' (curryTerm f) : B ⟶ (A ⇒ C)) := by
  unfold MonoidalClosed.curry
  dsimp only [ihom.adjunction, ihom, Closed.adj, Closed.rightAdj, syntacticClosed]
  rw [Adjunction.mkOfHomEquiv_homEquiv]
  exact curryEquiv_apply_mk f

theorem curry_mk_heq (f : ClosedTm ((A × B) ⇒ C)) :
    (@MonoidalClosed.curry (Ty G) _ _ A C B (syntacticClosed A)
      (Quotient.mk' f : (A × B) ⟶ C))
      ≍ (Quotient.mk' (curryTerm f) : B ⟶ (A ⇒ C)) := by
  exact heq_of_eq (curry_mk f)

theorem ev_mk_heq (A B : Ty G) :
    (syntacticClosed A).adj.counit.app B ≍
      (Quotient.mk' (uncurryTerm (idTerm (A ⇒ B))) : (A × (A ⇒ B)) ⟶ B) := by
  with_unfolding_all
    exact heq_of_eq (curryEquiv_symm_apply_mk (idTerm (A ⇒ B)))

end SynObj

/-! Categorical semantics of STLC following Pitts, `notes.pdf`, Sections 3–5. -/

open CategoryTheory
open Category MonoidalCategory CartesianMonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [MonoidalClosed C] (M : G → C)

noncomputable def Ty.denote : Ty G → C
  | .ground g => M g
  | .unit => 𝟙_ C
  | .prod A B => denote A ⊗ denote B
  | .arr A B => ihom (denote A) |>.obj (denote B)

notation:max M:arg "⟦" A "⟧" => Ty.denote M A

noncomputable def Ctx.denote : Ctx G → C
  | [] => 𝟙_ C
  | A :: Γ => denote Γ ⊗ M⟦A⟧

notation:max M:arg "⟦" Γ "⟧" => Ctx.denote M Γ

noncomputable def Var.denote (x : Γ ∋ A) : M⟦Γ⟧ ⟶ M⟦A⟧ :=
  Var.rec (snd _ _) (fun _ f => fst _ _ ≫ f) x

notation:max M:arg "⟦" x "⟧" => Var.denote M x

@[simp] theorem Var.denote_zero {Γ : Ctx G} {A : Ty G} : M⟦(.zero : A :: Γ ∋ A)⟧ = snd _ _ := rfl

@[simp] theorem Var.denote_succ (x : Γ ∋ A) : M⟦.succ (B := B) x⟧ = fst _ _ ≫ M⟦x⟧ := rfl

noncomputable def Tm.denote : Γ ⊢ A → (M⟦Γ⟧ ⟶ M⟦A⟧)
  | .var x => M⟦x⟧
  | .lam body =>
      MonoidalClosed.curry
        (lift (CartesianMonoidalCategory.snd _ _)
          (CartesianMonoidalCategory.fst _ _) ≫ denote body)
  | .app f a =>
      lift (denote a) (denote f) ≫
        (ihom.ev _).app _
  | .pair l r => lift (denote l) (denote r)
  | .fst p => denote p ≫ CartesianMonoidalCategory.fst _ _
  | .snd p => denote p ≫ CartesianMonoidalCategory.snd _ _
  | .unit => toUnit _

notation:max M:arg "⟦" t "⟧" => Tm.denote M t

noncomputable def Tm.Sub.denote : {Γ Δ : Ctx G} → Tm.Sub Γ Δ →
    (M⟦Δ⟧ ⟶ M⟦Γ⟧)
  | [], _, _ => toUnit _
  | _ :: _, _, σ => lift (denote (fun x => σ (.succ x))) M⟦σ .zero⟧

notation:max M:arg "⟦" σ "⟧" => Tm.Sub.denote M σ

noncomputable def Var.Ren.denote : {Γ Δ : Ctx G} → Var.Ren Γ Δ →
    (M⟦Δ⟧ ⟶ M⟦Γ⟧)
  | [], _, _ => toUnit _
  | _ :: _, _, ρ => lift (Var.Ren.denote (fun {_} x => ρ (.succ x))) M⟦ρ .zero⟧

notation:max M:arg "⟦" ρ "⟧" => Var.Ren.denote M ρ

theorem denote_ren_var {Γ Δ : Ctx G} (ρ : Var.Ren Γ Δ) {A : Ty G} (x : Γ ∋ A) :
    M⟦ρ⟧ ≫ M⟦x⟧ = M⟦ρ x⟧ := by
  induction x using Var.rec with
  | zero =>
      exact lift_snd
        M⟦fun {_} x => ρ (.succ x)⟧ M⟦ρ .zero⟧
  | @succ Γ A B x ih =>
      let ρ' : Var.Ren Γ Δ := fun x => ρ (.succ x)
      calc
        M⟦ρ⟧ ≫ M⟦.succ x⟧
        _ = lift M⟦ρ'⟧ M⟦ρ .zero⟧ ≫ (fst _ _ ≫ M⟦x⟧) := rfl
        _ = M⟦ρ'⟧ ≫ M⟦x⟧ := by rw [← assoc, lift_fst]
        _ = M⟦ρ' x⟧ := ih ρ'
        _ = M⟦ρ (.succ x)⟧ := rfl

theorem denote_ren_lift {Γ Δ : Ctx G} (ρ : Var.Ren Γ Δ) (B : Ty G) :
    M⟦(fun {_} x => Var.succ (ρ x) : Var.Ren Γ (B :: Δ))⟧ =
      CartesianMonoidalCategory.fst _ _ ≫ M⟦ρ⟧ := by
  induction Γ with
  | nil => apply toUnit_unique
  | cons A Γ ih =>
      simp only [Var.Ren.denote, Var.denote_succ]
      rw [ih (fun {_} x => ρ (.succ x))]
      exact (comp_lift (fst _ _) M⟦fun x => ρ (.succ x)⟧ M⟦ρ .zero⟧).symm

theorem denote_ren_ext {Γ Δ : Ctx G} (ρ : Var.Ren Γ Δ) (B : Ty G) :
    M⟦Var.ext (B := B) ρ⟧ =
      lift (CartesianMonoidalCategory.fst _ _ ≫ M⟦ρ⟧)
        (CartesianMonoidalCategory.snd _ _) := by
  simp only [Var.Ren.denote, Var.ext_zero, Var.ext_succ]
  rw [denote_ren_lift]
  rfl

theorem denote_rename {Γ Δ : Ctx G} (ρ : Var.Ren Γ Δ) {A : Ty G} (t : Γ ⊢ A) :
    M⟦Tm.rename ρ t⟧ = M⟦ρ⟧ ≫ M⟦t⟧ := by
  induction t generalizing Δ with
  | var x => exact (denote_ren_var M ρ x).symm
  | @lam Γ X Y N ih =>
      simp only [Tm.rename, Tm.denote]
      rw [ih, denote_ren_ext]
      apply MonoidalClosed.uncurry_injective
      rw [MonoidalClosed.uncurry_curry]
      let F := M⟦ρ⟧
      rw [show M⟦ρ⟧ = F from rfl]
      dsimp only [Ctx.denote, Ty.denote]
      rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry]
      let L := lift (snd M⟦X⟧ M⟦Δ⟧) (fst M⟦X⟧ M⟦Δ⟧)
      let E := lift (fst M⟦Δ⟧ M⟦X⟧ ≫ F) (snd M⟦Δ⟧ M⟦X⟧)
      let R := M⟦X⟧ ◁ F
      let S := lift (snd M⟦X⟧ M⟦Γ⟧) (fst M⟦X⟧ M⟦Γ⟧)
      have h : L ≫ E = R ≫ S := by apply hom_ext <;> dsimp [L, E, R, S] <;> simp
      calc
        L ≫ (E ≫ M⟦N⟧)
        _ = (L ≫ E) ≫ M⟦N⟧ := (assoc _ _ _).symm
        _ = (R ≫ S) ≫ M⟦N⟧ := congrArg (fun k => k ≫ M⟦N⟧) h
        _ = R ≫ (S ≫ M⟦N⟧) := assoc _ _ _
  | @app Γ X Y f a ihf iha =>
      simp only [Tm.rename, Tm.denote, ihf, iha]
      let F := M⟦ρ⟧
      let E := (ihom.ev M⟦X⟧).app M⟦Y⟧
      calc
        lift (F ≫ M⟦a⟧) (F ≫ M⟦f⟧) ≫ E
        _ = (F ≫ lift M⟦a⟧ M⟦f⟧) ≫ E := by rw [comp_lift]
        _ = F ≫ (lift M⟦a⟧ M⟦f⟧ ≫ E) := assoc _ _ _
  | pair l r ihl ihr =>
      simp only [Tm.rename, Tm.denote, ihl, ihr]
      exact (comp_lift _ _ _).symm
  | fst p ih => simp only [Tm.rename, Tm.denote, ih]; exact assoc _ _ _
  | snd p ih => simp only [Tm.rename, Tm.denote, ih]; exact assoc _ _ _
  | unit => exact (comp_toUnit _).symm

theorem denote_ren_id (Γ : Ctx G) :
    M⟦(fun {_} x => x : Var.Ren Γ Γ)⟧ = 𝟙 M⟦Γ⟧ := by
  induction Γ with
  | nil => apply toUnit_unique
  | cons A Γ ih =>
      simp only [Var.Ren.denote, Var.denote_zero]
      have h := denote_ren_lift M (fun {_} x => x : Var.Ren Γ Γ) A
      rw [ih, comp_id] at h
      rw [h]
      exact lift_fst_snd

theorem denote_ren_succ (Γ : Ctx G) (B : Ty G) :
    M⟦(.succ : Var.Ren Γ (B :: Γ))⟧ = fst M⟦Γ⟧ M⟦B⟧ := by
  have h := denote_ren_lift M (fun x => x : Var.Ren Γ Γ) B
  rw [denote_ren_id, comp_id] at h
  exact h

theorem denote_sub_lift {Γ Δ : Ctx G} (σ : Tm.Sub Γ Δ) (B : Ty G) :
    M⟦(fun x => Tm.rename .succ (σ x) : Tm.Sub Γ (B :: Δ))⟧ = fst _ _ ≫ M⟦σ⟧ := by
  induction Γ with
  | nil => apply toUnit_unique
  | cons A Γ ih =>
      simp only [Tm.Sub.denote]
      rw [ih (fun {_} x => σ (.succ x))]
      have h := denote_rename M (.succ : Var.Ren Δ (B :: Δ)) (σ .zero)
      rw [denote_ren_succ] at h
      rw [h]
      exact (comp_lift (fst _ _) M⟦fun {_} x => σ (.succ x)⟧ M⟦σ .zero⟧).symm

theorem denote_exts {Γ Δ : Ctx G} (σ : Tm.Sub Γ Δ) (B : Ty G) :
    M⟦Tm.exts (B := B) σ⟧ = lift (fst _ _ ≫ M⟦σ⟧) (snd _ _) := by
  simp only [Tm.Sub.denote, Tm.exts_zero, Tm.exts_succ]
  rw [denote_sub_lift]
  rfl

theorem denote_sub_var {Γ Δ : Ctx G} (σ : Tm.Sub Γ Δ) {A : Ty G} (x : Γ ∋ A) :
    M⟦σ⟧ ≫ M⟦x⟧ = M⟦σ x⟧ := by
  induction x using Var.rec with
  | zero =>
      exact lift_snd M⟦fun x => σ (.succ x)⟧ M⟦σ .zero⟧
  | @succ Γ A B x ih =>
      let σ' : Tm.Sub Γ Δ := fun x => σ (.succ x)
      calc
        M⟦σ⟧ ≫ M⟦.succ x⟧
        _ = lift M⟦σ'⟧ M⟦σ .zero⟧ ≫ (fst _ _ ≫ M⟦x⟧) := rfl
        _ = M⟦σ'⟧ ≫ M⟦x⟧ := by rw [← assoc, lift_fst]
        _ = M⟦σ' x⟧ := ih σ'
        _ = M⟦σ (.succ x)⟧ := rfl

theorem denote_subst {Γ Δ : Ctx G} (σ : Tm.Sub Γ Δ) {A : Ty G} (t : Γ ⊢ A) :
    M⟦Tm.subst σ t⟧ = M⟦σ⟧ ≫ M⟦t⟧ := by
  induction t generalizing Δ with
  | var x => exact (denote_sub_var M σ x).symm
  | @lam Γ X Y N ih =>
      simp only [Tm.subst, Tm.denote]
      rw [ih, denote_exts]
      apply MonoidalClosed.uncurry_injective
      rw [MonoidalClosed.uncurry_curry]
      let F := M⟦σ⟧
      rw [show M⟦σ⟧ = F from rfl]
      dsimp only [Ctx.denote, Ty.denote]
      rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry]
      let L := lift (snd M⟦X⟧ M⟦Δ⟧) (fst M⟦X⟧ M⟦Δ⟧)
      let E := lift (fst M⟦Δ⟧ M⟦X⟧ ≫ F) (snd M⟦Δ⟧ M⟦X⟧)
      let R := M⟦X⟧ ◁ F
      let S := lift (snd M⟦X⟧ M⟦Γ⟧) (fst M⟦X⟧ M⟦Γ⟧)
      have h : L ≫ E = R ≫ S := by apply hom_ext <;> dsimp [L, E, R, S] <;> simp
      calc
        L ≫ (E ≫ M⟦N⟧) = (L ≫ E) ≫ M⟦N⟧ :=
          (assoc _ _ _).symm
        _ = (R ≫ S) ≫ M⟦N⟧ := congrArg (fun k => k ≫ M⟦N⟧) h
        _ = R ≫ (S ≫ M⟦N⟧) := assoc _ _ _
  | @app Γ X Y f a ihf iha =>
      simp only [Tm.subst, Tm.denote, ihf, iha]
      let F := M⟦σ⟧
      let E := (ihom.ev M⟦X⟧).app M⟦Y⟧
      calc
        lift (F ≫ M⟦a⟧) (F ≫ M⟦f⟧) ≫ E =
            (F ≫ lift M⟦a⟧ M⟦f⟧) ≫ E := by rw [comp_lift]
        _ = F ≫ (lift M⟦a⟧ M⟦f⟧ ≫ E) := assoc _ _ _
  | pair l r ihl ihr =>
      simp only [Tm.subst, Tm.denote, ihl, ihr]
      exact (comp_lift _ _ _).symm
  | fst p ih => simp only [Tm.subst, Tm.denote, ih]; exact assoc _ _ _
  | snd p ih => simp only [Tm.subst, Tm.denote, ih]; exact assoc _ _ _
  | unit => exact (comp_toUnit _).symm

theorem denote_sub_id (Γ : Ctx G) :
    M⟦(fun {_} x => .var x : Tm.Sub Γ Γ)⟧ = 𝟙 M⟦Γ⟧ := by
  induction Γ with
  | nil => apply toUnit_unique
  | cons A Γ ih =>
      simp only [Tm.Sub.denote, Tm.denote]
      have h := denote_sub_lift M (fun {_} x => .var x : Tm.Sub Γ Γ) A
      rw [ih, comp_id] at h
      have h' : M⟦(fun {_} x => .var (.succ x) : Tm.Sub Γ (A :: Γ))⟧ = fst _ _ := by
        simpa only [Tm.rename] using h
      rw [h']
      exact lift_fst_snd

theorem denote_single {Γ : Ctx G} {B : Ty G} (arg : Γ ⊢ B) :
    M⟦Tm.single arg⟧ = lift (𝟙 _) M⟦arg⟧ := by
  simp only [Tm.single_zero, Tm.single_succ, Tm.Sub.denote]
  rw [denote_sub_id]

theorem denote_inst {Γ : Ctx G} {A B : Ty G} (body : B :: Γ ⊢ A) (arg : Γ ⊢ B) :
    M⟦body [ arg ]⟧ =
      lift (𝟙 _) M⟦arg⟧ ≫ M⟦body⟧ := by
  unfold Tm.inst
  rw [denote_subst, denote_single]
  rfl

theorem beta_lam_semantics {Γ : Ctx G} {A B : Ty G} (body : A :: Γ ⊢ B) (arg : Γ ⊢ A) :
    M⟦Tm.app (Tm.lam body) arg⟧ = M⟦body [ arg ]⟧ := by
  simp only [Tm.denote, denote_inst]
  let X := M⟦A⟧
  let D := M⟦Γ⟧
  let g := lift (snd X D)
    (fst X D) ≫ M⟦body⟧
  rw [show lift (snd M⟦A⟧ M⟦Γ⟧) (fst M⟦A⟧ M⟦Γ⟧) ≫
    M⟦body⟧ = g from rfl]
  have hc := MonoidalClosed.whiskerLeft_curry_ihom_ev_app (A := X) (g := g)
  dsimp only [X, D, g] at hc
  have hp :
      lift M⟦arg⟧ (MonoidalClosed.curry g) =
        lift (𝟙 D) M⟦arg⟧ ≫
          lift (snd D X)
            (fst D X) ≫
          (X ◁ MonoidalClosed.curry g) := by
    apply hom_ext <;> dsimp [X, D] <;> simp
  dsimp only [Ctx.denote, Ty.denote]
  rw [hp]
  simp only [assoc]
  rw [hc]
  dsimp [g, X, D]
  let q := lift (𝟙 M⟦Γ⟧) M⟦arg⟧
  let s := lift (snd M⟦Γ⟧ M⟦A⟧) (fst M⟦Γ⟧ M⟦A⟧)
  let r := lift (snd M⟦A⟧ M⟦Γ⟧) (fst M⟦A⟧ M⟦Γ⟧)
  have hs : s ≫ r = 𝟙 _ := by apply hom_ext <;> dsimp [s, r] <;> simp
  let b : M⟦Γ⟧ ⊗ M⟦A⟧ ⟶ M⟦B⟧ := M⟦body⟧
  calc
    q ≫ (s ≫ (r ≫ b)) = q ≫ ((s ≫ r) ≫ b) := by
      rw [assoc]
    _ = q ≫ (𝟙 _ ≫ b) := by rw [hs]
    _ = q ≫ b := by rw [id_comp]

theorem eta_lam_semantics {Γ : Ctx G} {A B : Ty G} (f : Γ ⊢ A ⇒ B) :
    M⟦Tm.lam (.app (Tm.rename .succ f) (.var .zero))⟧ =
      M⟦f⟧ := by
  simp only [Tm.denote]
  have hr := denote_rename M (.succ : Var.Ren Γ (A :: Γ)) f
  rw [denote_ren_succ] at hr
  rw [hr]
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_curry]
  let X := M⟦A⟧
  let D := M⟦Γ⟧
  let F := M⟦f⟧
  let L := lift (snd X D) (fst X D)
  let E := lift (snd D X) (fst D X ≫ F)
  have hp : L ≫ E = X ◁ F := by apply hom_ext <;> dsimp [L, E, X, D, F] <;> simp
  let ev := (ihom.ev X).app M⟦B⟧
  calc
    L ≫ (E ≫ ev) = (L ≫ E) ≫ ev := (assoc _ _ _).symm
    _ = (X ◁ F) ≫ ev := by rw [hp]

theorem step_soundness {Γ : Ctx G} {A : Ty G} {t u : Γ ⊢ A} :
  Step t u → M⟦t⟧ = M⟦u⟧ := by
  intro h
  induction h with
  | lam h ih => simp only [Tm.denote, ih]; rfl
  | app₁ h ih => simp only [Tm.denote, ih]
  | app₂ h ih => simp only [Tm.denote, ih]
  | betaLam => exact beta_lam_semantics M _ _
  | pair₁ h ih => simp only [Tm.denote, ih]; rfl
  | pair₂ h ih => simp only [Tm.denote, ih]; rfl
  | fst h ih => simp only [Tm.denote, ih]
  | snd h ih => simp only [Tm.denote, ih]
  | betaFst => simp only [Tm.denote]; exact lift_fst _ _
  | betaSnd => simp only [Tm.denote]; exact lift_snd _ _
  | etaLam f => exact eta_lam_semantics M f
  | etaPair p =>
      simp only [Tm.denote]
      exact lift_comp_fst_snd _
  | etaUnit t => apply toUnit_unique

/-- Pitts's Theorem 6.2: categorical semantics is sound for βη-equivalence. -/
theorem soundness {Γ : Ctx G} {A : Ty G} {t u : Γ ⊢ A} :
    t =βη u → M⟦t⟧ = M⟦u⟧ := by
  intro h
  induction h with
  | rel _ _ h => exact step_soundness M h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def CtxTy : Ctx G → Ty G
  | [] => .unit
  | A :: Γ => CtxTy Γ × A

def pack : (Γ : Ctx G) → Γ ⊢ CtxTy Γ
  | [] => .unit
  | _ :: Γ => .pair (Tm.rename .succ (pack Γ)) (.var .zero)

def project (p : Δ ⊢ CtxTy Γ) (x : Γ ∋ A) : Δ ⊢ A :=
  Var.rec (fun p => .snd p) (fun _ project p => project (.fst p)) x p

@[simp] theorem project_succ (p : Δ ⊢ CtxTy (B :: Γ)) (x : Γ ∋ A) :
    project p (.succ (B := B) x) = project (.fst p) x := rfl

def unpack (Γ : Ctx G) : Tm.Sub Γ [CtxTy Γ] :=
  fun x => project (.var .zero) x

def plug (Γ : Ctx G) : Tm.Sub [CtxTy Γ] Γ := fun x =>
  Var.cases (pack Γ) (fun x => Fin.elim0 x.1) x

def close (t : Γ ⊢ A) : ClosedTm (CtxTy Γ ⇒ A) :=
  .lam (Tm.subst (unpack Γ) t)

theorem project_rename (ρ : Var.Ren Δ Θ) (p : Δ ⊢ CtxTy Γ) (x : Γ ∋ A) :
    project (Tm.rename ρ p) x = Tm.rename ρ (project p x) := by
  induction x using Var.rec generalizing Δ Θ with
  | zero => rfl
  | succ x ih => exact ih ρ (.fst p)

theorem project_betaEta {p q : Δ ⊢ CtxTy Γ} (h : p =βη q) (x : Γ ∋ A) :
    project p x =βη project q x := by
  induction x using Var.rec with
  | zero => exact betaEta_snd h
  | succ x ih => exact ih (betaEta_fst h)

theorem project_pack (x : Γ ∋ A) : project (pack Γ) x =βη Tm.var x := by
  induction x using Var.rec with
  | @zero Γ A => exact .rel _ _ .betaSnd
  | @succ Γ A B x ih =>
      apply Relation.EqvGen.trans _ _ _
        (project_betaEta (.rel _ _ (.betaFst : Step (.fst (pack (B :: Γ))) _)) x)
      rw [project_rename (ρ := .succ)]
      exact betaEta_map (Tm.rename .succ)
        (fun h => rename_step .succ h) ih

theorem project_subst (σ : Tm.Sub Δ Θ) (p : Δ ⊢ CtxTy Γ) (x : Γ ∋ A) :
    Tm.subst σ (project p x) = project (Tm.subst σ p) x := by
  induction x using Var.rec with
  | zero => rfl
  | succ x ih => exact ih (.fst p)

theorem unpack_pack (x : Γ ∋ A) :
    Tm.subst (plug Γ) (unpack Γ x) =βη Tm.var x := by
  unfold unpack
  rw [project_subst]
  simp only [Tm.subst, plug]
  exact project_pack x

theorem subst_betaEta (t : Γ ⊢ A) {σ τ : Tm.Sub Γ Δ}
    (h : ∀ {B} (x : Γ ∋ B), σ x =βη τ x) :
    Tm.subst σ t =βη Tm.subst τ t := by
  induction t generalizing Δ with
  | var x => exact h x
  | @lam Γ X Y body ih =>
      apply betaEta_lam
      apply ih
      intro B x
      induction x using Var.cases with
      | zero => exact .refl _
      | succ x =>
          exact betaEta_map (Tm.rename .succ)
            (fun h => rename_step .succ h) (h x)
  | app f a ihf iha => exact betaEta_app (ihf h) (iha h)
  | pair l r ihl ihr => exact betaEta_pair (ihl h) (ihr h)
  | fst p ih => exact betaEta_fst (ih h)
  | snd p ih => exact betaEta_snd (ih h)
  | unit => exact .refl _

theorem reopen (t : Γ ⊢ A) :
    Tm.app ((close t).weaken Γ) (pack Γ) =βη t := by
  unfold close
  simp only [ClosedTm.weaken, Tm.rename]
  apply Relation.EqvGen.trans _ _ _ (.rel _ _ .betaLam)
  simp only [Tm.inst]
  rw [subst_rename]
  have he : ((fun {B} (x : [CtxTy Γ] ∋ B) =>
      Tm.single (pack Γ) (Var.ext (emptyRen Γ) x)) :
        Tm.Sub [CtxTy Γ] Γ) =
      (plug Γ : Tm.Sub [CtxTy Γ] Γ) := by
    funext B x
    induction x using Var.cases with
    | zero => rfl
    | succ x => exact Fin.elim0 x.1
  rw [he]
  rw [subst_comp]
  apply Relation.EqvGen.trans _ _ _ (subst_betaEta t (fun x => unpack_pack x))
  have hv := subst_vars (fun {_} x => x : Var.Ren Γ Γ) t
  rw [rename_id] at hv
  rw [hv]
  exact .refl _

theorem ty_denote (A : Ty G) : Ty.ground⟦A⟧ = A := by
  induction A with
  | unit | ground => rfl
  | prod A B ihA ihB => simp only [Ty.denote]; rw [ihA, ihB]; rfl
  | arr A B ihA ihB => simp only [Ty.denote]; rw [ihA, ihB]; rfl

theorem ctx_denote (Γ : Ctx G) : Ty.ground⟦Γ⟧ = CtxTy Γ := by
  induction Γ with
  | nil => rfl
  | cons A Γ ih => simp only [Ctx.denote, CtxTy]; rw [ih, ty_denote]; rfl

theorem fst_heq (Γ : Ctx G) (A : Ty G) :
    (fst
      Ty.ground⟦Γ⟧ Ty.ground⟦A⟧)
      ≍ (Quotient.mk' (fstTerm (CtxTy Γ) A) : SynHom (CtxTy Γ × A) (CtxTy Γ)) := by
  have hΓ := ctx_denote Γ
  have hA := ty_denote A
  revert hΓ hA
  generalize Ty.ground⟦Γ⟧ = X
  generalize Ty.ground⟦A⟧ = Y
  intro hΓ hA
  cases hΓ
  cases hA
  rfl

theorem snd_heq (Γ : Ctx G) (A : Ty G) :
    (snd
      Ty.ground⟦Γ⟧ Ty.ground⟦A⟧)
      ≍ (Quotient.mk' (sndTerm (CtxTy Γ) A) : SynHom (CtxTy Γ × A) A) := by
  have hΓ := ctx_denote Γ
  have hA := ty_denote A
  revert hΓ hA
  generalize Ty.ground⟦Γ⟧ = X
  generalize Ty.ground⟦A⟧ = Y
  intro hΓ hA
  cases hΓ
  cases hA
  rfl

theorem fst_ty_heq (A B : Ty G) :
    (fst
      Ty.ground⟦A⟧ Ty.ground⟦B⟧)
      ≍ (Quotient.mk' (fstTerm A B) : SynHom (A × B) A) := by
  have hA := ty_denote A
  have hB := ty_denote B
  revert hA hB
  generalize Ty.ground⟦A⟧ = X
  generalize Ty.ground⟦B⟧ = Y
  intro hA hB
  cases hA
  cases hB
  rfl

theorem snd_ty_heq (A B : Ty G) :
    (snd
      Ty.ground⟦A⟧ Ty.ground⟦B⟧)
      ≍ (Quotient.mk' (sndTerm A B) : SynHom (A × B) B) := by
  have hA := ty_denote A
  have hB := ty_denote B
  revert hA hB
  generalize Ty.ground⟦A⟧ = X
  generalize Ty.ground⟦B⟧ = Y
  intro hA hB
  cases hA
  cases hB
  rfl

theorem toUnit_heq (Γ : Ctx G) :
    toUnit
      Ty.ground⟦Γ⟧ ≍
      (Quotient.mk' (terminalTerm (CtxTy Γ)) : SynHom (CtxTy Γ) Ty.unit) := by
  have hΓ := ctx_denote Γ
  revert hΓ
  generalize Ty.ground⟦Γ⟧ = X
  intro hΓ
  cases hΓ
  exact heq_of_eq (SynObj.toUnit_mk (CtxTy Γ))

theorem ev_heq (A B : Ty G) :
    (ihom.ev Ty.ground⟦A⟧).app
      Ty.ground⟦B⟧ ≍
      (Quotient.mk' (uncurryTerm (idTerm (A ⇒ B))) :
        SynHom (A × (A ⇒ B)) B) := by
  have hA := ty_denote A
  have hB := ty_denote B
  revert hA hB
  generalize Ty.ground⟦A⟧ = X
  generalize Ty.ground⟦B⟧ = Y
  intro hA hB
  cases hA
  cases hB
  exact SynObj.ev_mk_heq A B

theorem comp_heq {X Y Z X' Y' Z' : Ty G} {f : X ⟶ Y} {g : Y ⟶ Z}
    {f' : X' ⟶ Y'} {g' : Y' ⟶ Z'} (hX : X = X') (hY : Y = Y') (hZ : Z = Z')
    (hf : f ≍ f') (hg : g ≍ g') :
    (f ≫ g) ≍ (f' ≫ g') := by
  subst X'
  subst Y'
  subst Z'
  exact heq_of_eq (congrArg₂ (fun f g => f ≫ g) (eq_of_heq hf) (eq_of_heq hg))

theorem lift_heq {X Y Z X' Y' Z' : Ty G} {f : X ⟶ Y} {g : X ⟶ Z}
    {f' : X' ⟶ Y'} {g' : X' ⟶ Z'} (hX : X = X') (hY : Y = Y') (hZ : Z = Z')
    (hf : f ≍ f') (hg : g ≍ g') :
    lift f g ≍
      lift f' g' := by
  subst X'
  subst Y'
  subst Z'
  exact heq_of_eq (congrArg₂ lift
    (eq_of_heq hf) (eq_of_heq hg))

theorem fst_obj_heq {X Y X' Y' : Ty G} (hX : X = X') (hY : Y = Y') :
    fst X Y ≍
      (Quotient.mk' (fstTerm X' Y') : SynHom (X' × Y') X') := by
  subst X'
  subst Y'
  rfl

theorem snd_obj_heq {X Y X' Y' : Ty G} (hX : X = X') (hY : Y = Y') :
    snd X Y ≍
      (Quotient.mk' (sndTerm X' Y') : SynHom (X' × Y') Y') := by
  subst X'
  subst Y'
  rfl

theorem curry_heq {A X Y A' X' Y' : Ty G} {f : A ⊗ Y ⟶ X}
    {f' : A' ⊗ Y' ⟶ X'} (hA : A = A') (hX : X = X') (hY : Y = Y')
    (hf : f ≍ f') :
    MonoidalClosed.curry f ≍
      MonoidalClosed.curry f' := by
  subst A'
  subst X'
  subst Y'
  exact heq_of_eq (congrArg MonoidalClosed.curry (eq_of_heq hf))

theorem tensor_ctx_eq (A : Ty G) (Γ : Ctx G) :
    Ty.ground⟦A⟧ ⊗ Ty.ground⟦Γ⟧ = A × CtxTy Γ := by
  rw [ty_denote, ctx_denote]
  rfl

theorem close_app_var (t : Γ ⊢ A) :
    Tm.app ((close t).weaken [CtxTy Γ]) (.var .zero) =βη
      Tm.subst (unpack Γ) t := by
  unfold close
  simp only [ClosedTm.weaken, Tm.rename]
  apply Relation.EqvGen.trans _ _ _ (.rel _ _ .betaLam)
  simp only [Tm.inst]
  rw [subst_rename]
  have he : ((fun {B} (x : [CtxTy Γ] ∋ B) =>
      Tm.single (.var .zero) (Var.ext (emptyRen _) x)) :
        Tm.Sub [CtxTy Γ] [CtxTy Γ]) =
      ((fun {_} x => Tm.var x) : Tm.Sub [CtxTy Γ] [CtxTy Γ]) := by
    funext B x
    induction x using Var.cases with
    | zero => rfl
    | succ x => exact Fin.elim0 x.1
  rw [he]
  have hv := subst_vars
    (fun {_} x => x : Var.Ren [CtxTy Γ] [CtxTy Γ])
    (Tm.subst (unpack Γ) t)
  rw [rename_id] at hv
  rw [hv]
  exact .refl _

theorem pairTerm_close (l : Γ ⊢ A) (r : Γ ⊢ B) :
    pairTerm (close l) (close r) =βη close (.pair l r) := by
  unfold pairTerm close
  simp only [Tm.subst]
  exact betaEta_lam (betaEta_pair (close_app_var l) (close_app_var r))

theorem comp_close_fst (p : Γ ⊢ A × B) :
    compTerm (close p) (fstTerm A B) =βη close (.fst p) := by
  unfold compTerm close
  rw [weaken_fstTerm]
  simp only [Tm.subst]
  apply betaEta_lam
  apply Relation.EqvGen.trans _ _ _ (.rel _ _ .betaLam)
  simp only [Tm.inst, Tm.subst, Tm.single_zero]
  exact betaEta_fst (close_app_var p)

theorem comp_close_snd (p : Γ ⊢ A × B) :
    compTerm (close p) (sndTerm A B) =βη close (.snd p) := by
  unfold compTerm close
  rw [weaken_sndTerm]
  simp only [Tm.subst]
  apply betaEta_lam
  apply Relation.EqvGen.trans _ _ _ (.rel _ _ .betaLam)
  simp only [Tm.inst, Tm.subst, Tm.single_zero]
  exact betaEta_snd (close_app_var p)

def evalTerm (A B : Ty G) : ClosedTm ((A × (A ⇒ B)) ⇒ B) :=
  .lam (.app (.snd (.var .zero)) (.fst (.var .zero)))

theorem uncurry_idTerm (A B : Ty G) :
    uncurryTerm (idTerm (A ⇒ B)) =βη evalTerm A B := by
  unfold uncurryTerm idTerm evalTerm
  simp only [ClosedTm.weaken, Tm.rename]
  apply Relation.EqvGen.trans _ _ _ (.rel _ _ (.lam (.app₁ .betaLam)))
  simp only [Tm.inst, Tm.subst]
  exact .refl _

theorem comp_pair_close_ev (f : Γ ⊢ A ⇒ B) (a : Γ ⊢ A) :
    compTerm (pairTerm (close a) (close f))
      (uncurryTerm (idTerm (A ⇒ B))) =βη close (.app f a) := by
  apply Relation.EqvGen.trans _ _ _
    (compTerm_congr (.refl _) (uncurry_idTerm A B))
  unfold compTerm evalTerm
  rw [ClosedTm.weaken_lam]
  simp only [Tm.rename, Var.ext_zero]
  let p : [CtxTy Γ] ⊢ A × (A ⇒ B) :=
    .app ((pairTerm (close a) (close f)).weaken [CtxTy Γ]) (.var .zero)
  rw [show
    Tm.app ((pairTerm (close a) (close f)).weaken [CtxTy Γ]) (.var .zero) = p
    from rfl]
  rw [show close (.app f a) = Tm.lam (Tm.subst (unpack Γ) (.app f a)) from rfl]
  apply betaEta_lam
  apply Relation.EqvGen.trans _ _ _ (.rel _ _ .betaLam)
  simp only [Tm.inst, Tm.subst, Tm.single_zero]
  have hp : p =βη .pair (Tm.subst (unpack Γ) a) (Tm.subst (unpack Γ) f) := by
    apply Relation.EqvGen.trans _ _ _
      (betaEta_app (betaEta_weaken (pairTerm_close a f) _) (.refl _))
    simpa only [Tm.subst] using close_app_var (Tm.pair a f)
  exact betaEta_app
    (Relation.EqvGen.trans _ _ _ (betaEta_snd hp) (.rel _ _ .betaSnd))
    (Relation.EqvGen.trans _ _ _ (betaEta_fst hp) (.rel _ _ .betaFst))

def swapTerm (A B : Ty G) : ClosedTm ((A × B) ⇒ (B × A)) :=
  pairTerm (sndTerm A B) (fstTerm A B)

theorem swapTerm_app (p : Δ ⊢ A × B) :
    Tm.app ((swapTerm A B).weaken Δ) p =βη .pair (.snd p) (.fst p) := by
  unfold swapTerm
  rw [weaken_pairTerm]
  apply Relation.EqvGen.trans _ _ _ (.rel _ _ .betaLam)
  simp only [Tm.inst, Tm.subst, Tm.single_zero,
    subst_weaken_closed]
  apply betaEta_pair
  · rw [weaken_sndTerm]
    apply Relation.EqvGen.trans _ _ _ (.rel _ _ .betaLam)
    simp only [Tm.inst, Tm.subst, Tm.single_zero]
    exact .refl _
  · rw [weaken_fstTerm]
    apply Relation.EqvGen.trans _ _ _ (.rel _ _ .betaLam)
    simp only [Tm.inst, Tm.subst, Tm.single_zero]
    exact .refl _

def unpackSnoc (Γ : Ctx G) (A : Ty G) : Tm.Sub (A :: Γ) [CtxTy Γ × A] :=
  fun x => project (.var .zero) x

def closeSnoc (body : A :: Γ ⊢ B) : ClosedTm ((CtxTy Γ × A) ⇒ B) :=
  .lam (Tm.subst (unpackSnoc Γ A) body)

theorem close_eq_closeSnoc (body : A :: Γ ⊢ B) : close body = closeSnoc body := by
  rfl

theorem closeSnoc_app_pair (body : A :: Γ ⊢ B) :
    Tm.app ((closeSnoc body).weaken [A, CtxTy Γ])
      (.pair (.var (.succ .zero)) (.var .zero)) =βη
      Tm.subst (Tm.exts (unpack Γ)) body := by
  unfold closeSnoc
  simp only [ClosedTm.weaken, Tm.rename]
  apply Relation.EqvGen.trans _ _ _ (.rel _ _ .betaLam)
  simp only [Tm.inst]
  rw [subst_rename]
  let σ : Tm.Sub [CtxTy Γ × A] [A, CtxTy Γ] :=
    fun {_} x => Var.cases (.pair (.var (.succ .zero)) (.var .zero))
      (fun x => Fin.elim0 x.1) x
  have he : ((fun {C} (x : [CtxTy Γ × A] ∋ C) =>
      Tm.single (.pair (.var (.succ .zero)) (.var .zero))
        (Var.ext (emptyRen _) x)) :
      Tm.Sub [CtxTy Γ × A] [A, CtxTy Γ]) =
      (σ : Tm.Sub [CtxTy Γ × A] [A, CtxTy Γ]) := by
    funext C x
    induction x using Var.cases with
    | zero => rfl
    | succ x => exact Fin.elim0 x.1
  rw [he, subst_comp]
  apply subst_betaEta body
  intro C x
  induction x using Var.cases with
  | zero =>
      apply Relation.EqvGen.trans _ _ _ (.rel _ _ .betaSnd)
      exact .refl _
  | succ x =>
      simp only [unpackSnoc, Tm.exts_succ, project_succ]
      rw [project_subst]
      apply project_betaEta (.rel _ _ .betaFst) x |>.trans
      unfold unpack
      rw [← project_rename
        (.succ : Var.Ren [CtxTy Γ] [A, CtxTy Γ])]
      exact .refl _

theorem curry_swap_close (body : A :: Γ ⊢ B) :
    curryTerm (compTerm (swapTerm A (CtxTy Γ)) (close body)) =βη
      close (.lam body) := by
  rw [close_eq_closeSnoc]
  unfold curryTerm
  rw [weaken_compTerm]
  apply Relation.EqvGen.trans _ _ _ (.rel _ _ (.lam (.lam .betaLam)))
  simp only [Tm.inst, Tm.subst, Tm.single_zero,
    subst_weaken_closed]
  let p : [A, CtxTy Γ] ⊢ A × CtxTy Γ :=
    .pair (.var .zero) (.var (.succ .zero))
  have hs : Tm.app ((swapTerm A (CtxTy Γ)).weaken [A, CtxTy Γ]) p =βη
      .pair (.var (.succ .zero)) (.var .zero) := by
    apply Relation.EqvGen.trans _ _ _ (swapTerm_app p)
    exact betaEta_pair (.rel _ _ .betaSnd) (.rel _ _ .betaFst)
  apply betaEta_lam
  apply betaEta_lam
  apply Relation.EqvGen.trans _ _ _ (betaEta_app (.refl _) hs)
  exact closeSnoc_app_pair body

theorem denote_close {G : Type} {Γ : Ctx G} {A : Ty G} (t : Γ ⊢ A) :
    Ty.ground⟦t⟧ ≍ Quotient.mk' (close t) := by
  induction t with
  | var x =>
      induction x using Var.rec with
      | @zero Γ A =>
          exact snd_heq Γ A
      | @succ Γ A B x ih =>
          have hc := comp_heq (ctx_denote (B :: Γ)) (ctx_denote Γ) (ty_denote A)
            (fst_heq Γ B) ih
          apply hc.trans
          apply heq_of_eq
          apply Quotient.sound
          unfold close unpack
          simp only [Tm.subst, project_succ]
          unfold compTerm fstTerm
          simp only [ClosedTm.weaken, Tm.rename]
          apply Relation.EqvGen.trans _ _ _ (.rel _ _ (.lam (.app₂ .betaLam)))
          simp only [Tm.inst, Tm.subst]
          apply Relation.EqvGen.trans _ _ _ (.rel _ _ (.lam .betaLam))
          simp only [Tm.inst]
          simp only [CtxTy]
          rw [subst_rename]
          simp only [Var.ext_zero]
          let σ : Tm.Sub [CtxTy Γ] [CtxTy Γ × B] :=
            fun {_} x => Var.cases (.fst (.var .zero)) (fun x => Fin.elim0 x.1) x
          simp only [Tm.single_zero]
          have he : ((fun {C} (y : [CtxTy Γ] ∋ C) =>
              Tm.single (.fst (.var .zero)) (Var.ext (emptyRen _) y)) :
              Tm.Sub [CtxTy Γ] [CtxTy Γ × B]) =
              (σ : Tm.Sub [CtxTy Γ] [CtxTy Γ × B]) := by
            funext C y
            induction y using Var.cases with
            | zero => rfl
            | succ y => exact Fin.elim0 y.1
          rw [he]
          rw [project_subst]
          exact .refl _
  | @lam Γ A B body ih =>
      have hsnd := snd_obj_heq (ty_denote A) (ctx_denote Γ)
      have hfst := fst_obj_heq (ty_denote A) (ctx_denote Γ)
      have hswap := lift_heq (tensor_ctx_eq A Γ) (ctx_denote Γ) (ty_denote A)
        hsnd hfst
      have hcomp := comp_heq (tensor_ctx_eq A Γ) (ctx_denote (A :: Γ)) (ty_denote B)
        hswap ih
      have hcurry := curry_heq (ty_denote A) (ty_denote B) (ctx_denote Γ) hcomp
      apply hcurry.trans
      apply (SynObj.curry_mk_heq
        (compTerm (swapTerm A (CtxTy Γ)) (close body))).trans
      exact heq_of_eq (Quotient.sound (curry_swap_close body))
  | @app Γ A B f a ihf iha =>
      have hp := lift_heq (ctx_denote Γ) (ty_denote A) (ty_denote (A ⇒ B)) iha ihf
      have hc := comp_heq (ctx_denote Γ) (ty_denote (A × (A ⇒ B))) (ty_denote B)
        hp (ev_heq A B)
      apply hc.trans
      exact heq_of_eq (Quotient.sound (comp_pair_close_ev f a))
  | pair l r ihl ihr =>
      have hp := lift_heq (ctx_denote _) (ty_denote _) (ty_denote _) ihl ihr
      apply hp.trans
      apply heq_of_eq
      rw [SynObj.lift_mk]
      exact Quotient.sound (pairTerm_close l r)
  | @fst Γ A B p ih =>
      have hc := comp_heq (ctx_denote Γ) (ty_denote (A × B)) (ty_denote A)
        ih (fst_ty_heq A B)
      apply hc.trans
      exact heq_of_eq (Quotient.sound (comp_close_fst p))
  | @snd Γ A B p ih =>
      have hc := comp_heq (ctx_denote Γ) (ty_denote (A × B)) (ty_denote B)
        ih (snd_ty_heq A B)
      apply hc.trans
      exact heq_of_eq (Quotient.sound (comp_close_snd p))
  | @unit Γ =>
      exact toUnit_heq Γ

/-- Completeness for the syntactic category. -/
theorem syntactic_completeness {Γ : Ctx G} {A : Ty G} {t u : Γ ⊢ A}
    (h : Ty.ground⟦t⟧ = Ty.ground⟦u⟧) :
    t =βη u := by
  have ht := denote_close t
  have hu := denote_close u
  have hc := eq_of_heq (ht.symm.trans ((heq_of_eq h).trans hu))
  have hclose : close t =βη close u := Quotient.exact hc
  apply Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (reopen t))
  apply Relation.EqvGen.trans _ _ _ (betaEta_app (betaEta_weaken hclose Γ) (.refl _))
  exact reopen u

/-- Pitts's Section 8 completeness theorem for categorical semantics. -/
theorem completeness {Γ : Ctx G} {A : Ty G} {t u : Γ ⊢ A}
    (h : ∀ (D : Type) [Category.{0} D]
      [CartesianMonoidalCategory D] [MonoidalClosed D]
      (M : G → D), M⟦t⟧ = M⟦u⟧) :
    t =βη u :=
  syntactic_completeness (h (Ty G) Ty.ground)

/-- Soundness and completeness for the syntactic category (Pitts, Section 8, equation (1)). -/
theorem syntactic_soundness_completeness {Γ : Ctx G} {A : Ty G} {t u : Γ ⊢ A} :
    t =βη u ↔ Ty.ground⟦t⟧ = Ty.ground⟦u⟧ := ⟨soundness Ty.ground, syntactic_completeness⟩

end LambdaCalculus.Intrinsic.StlcProd

end Cslib
