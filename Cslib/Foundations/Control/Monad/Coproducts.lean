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
using `IsMonadHom`, and the induced interpreter `IsMonadCoproduct.desc`.

A coproduct combines the effects of two monads: computations from either monad can be
included and sequenced in the coproduct using `do` notation. A pair of monad morphisms
interpreting the component effects determines a unique interpretation of the combined effects.

## References

* [Jiří Adámek, Nathan Bowler, Paul B. Levy, Stefan Milius,
  *Coproducts of Monads on Set*][Adamek2012]
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
    (inr : ∀ {α}, n α → p α) : Prop where
  /-- The left inclusion preserves monadic structure. -/
  inl_hom : IsMonadHom m p inl
  /-- The right inclusion preserves monadic structure. -/
  inr_hom : IsMonadHom n p inr
  /-- Every pair of monad morphisms has a unique extension along the inclusions. -/
  universal :
    ∀ (t : Type u → Type v) [Monad t] [LawfulMonad t]
      (f : ∀ {α}, m α → t α) (g : ∀ {α}, n α → t α),
      IsMonadHom m t f → IsMonadHom n t g →
      ∃! h : ∀ {α}, p α → t α,
        IsMonadHom p t h ∧
        (∀ {α} (x : m α), h (inl x) = f x) ∧
        (∀ {α} (x : n α), h (inr x) = g x)

namespace IsMonadCoproduct

variable {m n p : Type u → Type v}
    [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n]
    [Monad p] [LawfulMonad p]
    {inl : ∀ {α}, m α → p α} {inr : ∀ {α}, n α → p α}
    (h : IsMonadCoproduct m n p inl inr)
    {t : Type u → Type v} [Monad t] [LawfulMonad t]

section Desc

variable (f : ∀ {α}, m α → t α) (g : ∀ {α}, n α → t α)
    (hf : IsMonadHom m t f) (hg : IsMonadHom n t g)

/-- The unique monad morphism extending `f` and `g`, chosen using classical choice. -/
noncomputable def desc : ∀ {α}, p α → t α :=
  @Classical.choose (∀ {α}, p α → t α) _ (h.universal t f g hf hg).exists

private theorem desc_spec :
    IsMonadHom p t (h.desc f g hf hg) ∧
    (∀ {α} (x : m α), h.desc f g hf hg (inl x) = f x) ∧
    (∀ {α} (x : n α), h.desc f g hf hg (inr x) = g x) :=
  @Classical.choose_spec (∀ {α}, p α → t α) _ (h.universal t f g hf hg).exists

/-- The universal interpreter preserves monadic structure. -/
theorem isMonadHom_desc : IsMonadHom p t (h.desc f g hf hg) :=
  (h.desc_spec f g hf hg).1

/-- The universal interpreter extends the left morphism. -/
@[simp]
theorem desc_inl {α} (x : m α) : h.desc f g hf hg (inl x) = f x :=
  (h.desc_spec f g hf hg).2.1 x

/-- The universal interpreter extends the right morphism. -/
@[simp]
theorem desc_inr {α} (x : n α) : h.desc f g hf hg (inr x) = g x :=
  (h.desc_spec f g hf hg).2.2 x

/-- Any monad morphism extending `f` and `g` equals the universal interpreter. -/
theorem desc_unique {k : ∀ {α}, p α → t α} (hk : IsMonadHom p t k)
    (hinl : ∀ {α} (x : m α), k (inl x) = f x)
    (hinr : ∀ {α} (x : n α), k (inr x) = g x) :
    @k = (h.desc f g hf hg : ∀ {α}, p α → t α) :=
  (h.universal t f g hf hg).unique ⟨hk, hinl, hinr⟩ (h.desc_spec f g hf hg)

end Desc

include h in
/-- Monad morphisms out of a coproduct agree if they agree on both inclusions. -/
theorem hom_ext {f g : ∀ {α}, p α → t α}
    (hf : IsMonadHom p t f) (hg : IsMonadHom p t g)
    (hinl : ∀ {α} (x : m α), f (inl x) = g (inl x))
    (hinr : ∀ {α} (x : n α), f (inr x) = g (inr x)) : @f = @g := by
  obtain ⟨k, _, huniq⟩ := h.universal t (fun x => f (inl x)) (fun x => f (inr x))
    (hf.comp h.inl_hom) (hf.comp h.inr_hom)
  exact (huniq f ⟨hf, fun _ => rfl, fun _ => rfl⟩).trans
    (huniq g ⟨hg, fun x => (hinl x).symm, fun x => (hinr x).symm⟩).symm

end IsMonadCoproduct

end Cslib
