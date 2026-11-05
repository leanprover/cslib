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

end IsMonadCoproduct

end Cslib
