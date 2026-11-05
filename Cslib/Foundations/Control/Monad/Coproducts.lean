/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Cslib.Foundations.Control.Monad.IsMonadHom

/-!
# Coproducts of monads

This file defines the universal property of coproducts of lawful monads (`IsMonadCoproduct`)
using `IsMonadHom`. The universal property is carried as data: `IsMonadCoproduct.desc`
interprets the coproduct into any monad equipped with interpretations of both components,
so that concrete coproducts (such as free monads on a sum of signatures) yield computable
interpreters.

A coproduct combines the effects of two monads: computations from either monad can be
included and sequenced in the coproduct using `do` notation. A pair of monad morphisms
interpreting the component effects determines a unique interpretation of the combined effects.

## References

* [Jiří Adámek, Nathan Bowler, Paul B. Levy, Stefan Milius,
  *Coproducts of Monads on Set*][Adamek2012]
* [Christoph Lüth, Neil Ghani, *Composing Monads Using Coproducts*][LuthGhani2002]
-/

@[expose] public section

namespace Cslib

universe u v

/-- The maps `inl` and `inr` exhibit `p` as a coproduct of lawful monads. -/
structure IsMonadCoproduct
    (m n p : Type u → Type v)
    [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n]
    [Monad p] [LawfulMonad p]
    (inl : ∀ {α}, m α → p α)
    (inr : ∀ {α}, n α → p α) where
  /-- The left inclusion preserves monadic structure. -/
  inl_hom : IsMonadHom m p inl
  /-- The right inclusion preserves monadic structure. -/
  inr_hom : IsMonadHom n p inr
  /-- Every pair of monad morphisms descends to the coproduct. -/
  desc {t : Type u → Type v} [Monad t] [LawfulMonad t]
    {f : ∀ {α}, m α → t α} {g : ∀ {α}, n α → t α}
    (hf : IsMonadHom m t f) (hg : IsMonadHom n t g) :
    ∀ {α}, p α → t α
  /-- The universal interpreter preserves monadic structure. -/
  isMonadHom_desc {t : Type u → Type v} [Monad t] [LawfulMonad t]
    {f : ∀ {α}, m α → t α} {g : ∀ {α}, n α → t α}
    (hf : IsMonadHom m t f) (hg : IsMonadHom n t g) :
    IsMonadHom p t (desc hf hg)
  /-- The universal interpreter extends the left morphism. -/
  desc_inl {t : Type u → Type v} [Monad t] [LawfulMonad t]
    {f : ∀ {α}, m α → t α} {g : ∀ {α}, n α → t α}
    (hf : IsMonadHom m t f) (hg : IsMonadHom n t g) {α} (x : m α) :
    desc hf hg (inl x) = f x
  /-- The universal interpreter extends the right morphism. -/
  desc_inr {t : Type u → Type v} [Monad t] [LawfulMonad t]
    {f : ∀ {α}, m α → t α} {g : ∀ {α}, n α → t α}
    (hf : IsMonadHom m t f) (hg : IsMonadHom n t g) {α} (x : n α) :
    desc hf hg (inr x) = g x
  /-- Any monad morphism extending `f` and `g` equals the universal interpreter. -/
  desc_unique {t : Type u → Type v} [Monad t] [LawfulMonad t]
    {f : ∀ {α}, m α → t α} {g : ∀ {α}, n α → t α}
    (hf : IsMonadHom m t f) (hg : IsMonadHom n t g)
    {k : ∀ {α}, p α → t α} (hk : IsMonadHom p t k)
    (hinl : ∀ {α} (x : m α), k (inl x) = f x)
    (hinr : ∀ {α} (x : n α), k (inr x) = g x) :
    @k = (desc hf hg : ∀ {α}, p α → t α)

namespace IsMonadCoproduct

attribute [simp] desc_inl desc_inr

variable {m n p : Type u → Type v}
    [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n]
    [Monad p] [LawfulMonad p]
    {inl : ∀ {α}, m α → p α} {inr : ∀ {α}, n α → p α}
    (h : IsMonadCoproduct m n p inl inr)
    {t : Type u → Type v} [Monad t] [LawfulMonad t]

include h in
/-- Monad morphisms out of a coproduct agree if they agree on both inclusions. -/
theorem hom_ext {f g : ∀ {α}, p α → t α}
    (hf : IsMonadHom p t f) (hg : IsMonadHom p t g)
    (hinl : ∀ {α} (x : m α), f (inl x) = g (inl x))
    (hinr : ∀ {α} (x : n α), f (inr x) = g (inr x)) : @f = @g :=
  (h.desc_unique (hf.comp h.inl_hom) (hf.comp h.inr_hom) hf (fun _ => rfl) (fun _ => rfl)).trans
    (h.desc_unique (hf.comp h.inl_hom) (hf.comp h.inr_hom) hg
      (fun x => (hinl x).symm) (fun x => (hinr x).symm)).symm

/-- Descending along the inclusions themselves gives the identity. -/
theorem desc_inl_inr :
    (h.desc h.inl_hom h.inr_hom : ∀ {α}, p α → p α) = fun {α} (x : p α) => x :=
  (h.desc_unique h.inl_hom h.inr_hom (IsMonadHom.id p) (fun _ => rfl) (fun _ => rfl)).symm

@[simp]
theorem desc_inl_inr_apply {α} (x : p α) : h.desc h.inl_hom h.inr_hom x = x :=
  congrArg (fun F : ∀ {α}, p α → p α => F x) h.desc_inl_inr

/-- A coproduct of `m` and `n` is also a coproduct of `n` and `m`. -/
def symm : IsMonadCoproduct n m p inr inl where
  inl_hom := h.inr_hom
  inr_hom := h.inl_hom
  desc := @fun _ _ _ _ _ hg hf => h.desc hf hg
  isMonadHom_desc := @fun _ _ _ _ _ hg hf => h.isMonadHom_desc hf hg
  desc_inl := @fun _ _ _ _ _ hg hf _ x => h.desc_inr hf hg x
  desc_inr := @fun _ _ _ _ _ hg hf _ x => h.desc_inl hf hg x
  desc_unique := @fun _ _ _ _ _ hg hf _ hk hinr hinl => h.desc_unique hf hg hk hinl hinr

section Fusion

variable {t' : Type u → Type v} [Monad t'] [LawfulMonad t']
    {f : ∀ {α}, m α → t α} {g : ∀ {α}, n α → t α}
    (hf : IsMonadHom m t f) (hg : IsMonadHom n t g)
    {k : ∀ {α}, t α → t' α} (hk : IsMonadHom t t' k)

/-- A monad morphism out of the target fuses with the universal interpreter. -/
theorem comp_desc :
    (k ∘ h.desc hf hg : ∀ {α}, p α → t' α) =
      (h.desc (hk.comp hf) (hk.comp hg) : ∀ {α}, p α → t' α) :=
  h.desc_unique (hk.comp hf) (hk.comp hg) (hk.comp (h.isMonadHom_desc hf hg))
    (fun x => by simp only [Function.comp_apply, desc_inl])
    (fun x => by simp only [Function.comp_apply, desc_inr])

theorem comp_desc_apply {α} (x : p α) :
    k (h.desc hf hg x) = h.desc (hk.comp hf) (hk.comp hg) x :=
  congrArg (fun F : ∀ {α}, p α → t' α => F x) (h.comp_desc hf hg hk)

end Fusion

section Map

variable {m' n' p' : Type u → Type v}
    [Monad m'] [LawfulMonad m']
    [Monad n'] [LawfulMonad n']
    [Monad p'] [LawfulMonad p']
    {inl' : ∀ {α}, m' α → p' α} {inr' : ∀ {α}, n' α → p' α}
    (h' : IsMonadCoproduct m' n' p' inl' inr')
    {f : ∀ {α}, m α → m' α} {g : ∀ {α}, n α → n' α}
    (hf : IsMonadHom m m' f) (hg : IsMonadHom n n' g)

/-- The monad morphism between coproducts induced by morphisms of the components. -/
def map : ∀ {α}, p α → p' α :=
  h.desc (h'.inl_hom.comp hf) (h'.inr_hom.comp hg)

/-- The induced morphism between coproducts preserves monadic structure. -/
theorem isMonadHom_map : IsMonadHom p p' (h.map h' hf hg) :=
  h.isMonadHom_desc _ _

@[simp]
theorem map_inl {α} (x : m α) : h.map h' hf hg (inl x) = inl' (f x) :=
  h.desc_inl _ _ x

@[simp]
theorem map_inr {α} (x : n α) : h.map h' hf hg (inr x) = inr' (g x) :=
  h.desc_inr _ _ x

/-- The morphism induced by the identities is the identity. -/
theorem map_id :
    (h.map h (IsMonadHom.id m) (IsMonadHom.id n) : ∀ {α}, p α → p α) =
      fun {α} (x : p α) => x :=
  (h.desc_unique _ _ (IsMonadHom.id p) (fun _ => rfl) (fun _ => rfl)).symm

@[simp]
theorem map_id_apply {α} (x : p α) : h.map h (IsMonadHom.id m) (IsMonadHom.id n) x = x :=
  congrArg (fun F : ∀ {α}, p α → p α => F x) h.map_id

variable {m'' n'' p'' : Type u → Type v}
    [Monad m''] [LawfulMonad m'']
    [Monad n''] [LawfulMonad n'']
    [Monad p''] [LawfulMonad p'']
    {inl'' : ∀ {α}, m'' α → p'' α} {inr'' : ∀ {α}, n'' α → p'' α}
    (h'' : IsMonadCoproduct m'' n'' p'' inl'' inr'')
    {f' : ∀ {α}, m' α → m'' α} {g' : ∀ {α}, n' α → n'' α}
    (hf' : IsMonadHom m' m'' f') (hg' : IsMonadHom n' n'' g')

/-- The morphism induced by composites is the composite of the induced morphisms. -/
theorem map_comp :
    (h'.map h'' hf' hg' ∘ h.map h' hf hg : ∀ {α}, p α → p'' α) =
      (h.map h'' (hf'.comp hf) (hg'.comp hg) : ∀ {α}, p α → p'' α) :=
  h.desc_unique (h''.inl_hom.comp (hf'.comp hf)) (h''.inr_hom.comp (hg'.comp hg))
    ((h'.isMonadHom_map h'' hf' hg').comp (h.isMonadHom_map h' hf hg))
    (fun x => by simp only [Function.comp_apply, map_inl])
    (fun x => by simp only [Function.comp_apply, map_inr])

theorem map_map {α} (x : p α) :
    h'.map h'' hf' hg' (h.map h' hf hg x) = h.map h'' (hf'.comp hf) (hg'.comp hg) x :=
  congrArg (fun F : ∀ {α}, p α → p'' α => F x) (h.map_comp h' hf hg h'' hf' hg')

end Map

section Assoc

variable {o q r : Type u → Type v}
    [Monad o] [LawfulMonad o]
    [Monad q] [LawfulMonad q]
    [Monad r] [LawfulMonad r]
    {inl' : ∀ {α}, p α → q α} {inr' : ∀ {α}, o α → q α}
    (hq : IsMonadCoproduct p o q inl' inr')
    {jnl : ∀ {α}, n α → r α} {jnr : ∀ {α}, o α → r α}
    (hr : IsMonadCoproduct n o r jnl jnr)

/-- Coproducts are associative: if `p` is a coproduct of `m` and `n`, `q` is a coproduct of
`p` and `o`, and `r` is a coproduct of `n` and `o`, then `q` is a coproduct of `m` and `r`. -/
def assoc :
    IsMonadCoproduct m r q (fun x => inl' (inl x))
      (hr.desc (hq.inl_hom.comp h.inr_hom) hq.inr_hom) where
  inl_hom := hq.inl_hom.comp h.inl_hom
  inr_hom := hr.isMonadHom_desc _ _
  desc := @fun _ _ _ _ _ hf hg =>
    hq.desc (h.isMonadHom_desc hf (hg.comp hr.inl_hom)) (hg.comp hr.inr_hom)
  isMonadHom_desc _ _ := hq.isMonadHom_desc _ _
  desc_inl := @fun _ _ _ _ _ _ _ _ x => by simp only [desc_inl]
  desc_inr := @fun t _ _ _ _ hf hg _ x =>
    congrArg (fun F : ∀ {α}, r α → t α => F x) <|
      hr.hom_ext ((hq.isMonadHom_desc _ _).comp (hr.isMonadHom_desc _ _)) hg
        (fun y => by simp only [Function.comp_apply, desc_inl, desc_inr])
        (fun z => by simp only [Function.comp_apply, desc_inr])
  desc_unique := @fun t _ _ _ _ hf hg _ hk hinl hinr =>
    hq.desc_unique _ _ hk
      (fun x => congrArg (fun F : ∀ {α}, p α → t α => F x) <|
        h.hom_ext (hk.comp hq.inl_hom) (h.isMonadHom_desc hf (hg.comp hr.inl_hom))
          (fun x => by
            rw [desc_inl]
            exact hinl x)
          (fun y => by
            rw [desc_inr]
            have hy := hinr (jnl y)
            rw [desc_inl] at hy
            exact hy))
      (fun z => by
        have hz := hinr (jnr z)
        rw [desc_inr] at hz
        exact hz)

end Assoc

section Unit

variable (m : Type u → Type u) [Monad m] [LawfulMonad m]

/-- Every monad is a coproduct of itself and the identity monad. -/
def unitRight : IsMonadCoproduct m Id m id pure where
  inl_hom := IsMonadHom.id m
  inr_hom := IsMonadHom.pure m
  desc := @fun _ _ _ f _ _ _ => f
  isMonadHom_desc := @fun _ _ _ _ _ hf _ => hf
  desc_inl := @fun _ _ _ _ _ _ _ _ _ => rfl
  desc_inr := @fun _ _ _ _ _ hf hg _ x => (hf.map_pure x).trans (hg.eq_pure x).symm
  desc_unique := @fun _ _ _ _ _ _ _ _ _ hinl _ => by
    funext α x
    exact hinl x

/-- Every monad is a coproduct of the identity monad and itself. -/
def unitLeft : IsMonadCoproduct Id m m pure id :=
  (unitRight m).symm

end Unit

end IsMonadCoproduct

end Cslib
