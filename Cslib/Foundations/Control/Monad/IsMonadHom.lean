/-
Copyright (c) 2026 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Cslib.Init
public import Mathlib.Logic.Function.Defs
public import Batteries.Control.AlternativeMonad

/-!
# (unbundled) morphisms of monads

This file defines predicates on functions `f : ∀ {α}, m α → n α` that preserve functor, applicative,
monadic, and alternative structure (`IsFunctorHom`, `IsApplicativeHom`, `IsMonadHom`,
`IsAlternativeHom`, `IsAlternativeMonadHom`).

Rather than assuming lawfulness, they explicitly require compatibility with every operator
defined by the corresponding typeclasses, with helper constructors that dismiss the derived
operators when the structures are lawful.
-/

public section

namespace Cslib

/-! ### Functor Homomorphisms -/

/--
A function `f` is a morphism of functors if it preserves `<$>` and `Functor.mapConst`.
-/
structure IsFunctorHom (m n) [Functor m] [Functor n] (f : ∀ {α}, m α → n α) : Prop where
  map_map {α β} (g : α → β) (x : m α) : f (g <$> x) = g <$> f x
  map_mapConst {α β} (a : α) (x : m β) : f (Functor.mapConst a x) = Functor.mapConst a (f x)

namespace IsFunctorHom
variable {m n p : Type _ → Type _} [Functor m] [Functor n] [Functor p]

attribute [grind .] map_map map_mapConst

private theorem map_mapConst_of_map_map
    [LawfulFunctor m] [LawfulFunctor n] (f : ∀ {α}, m α → n α)
    (map_map : ∀ {α β} (g : α → β) (x : m α), f (g <$> x) = g <$> f x) :
    ∀ {α β} (a : α) (x : m β), f (Functor.mapConst a x) = Functor.mapConst a (f x) := by
  intros α β a x
  simp [LawfulFunctor.map_const, map_map]

/-- Construct an `IsFunctorHom` for lawful functors from `map_map`. -/
theorem mk' [LawfulFunctor m] [LawfulFunctor n] {f : ∀ {α}, m α → n α}
    (map_map : ∀ {α β} (g : α → β) (x : m α), f (g <$> x) = g <$> f x) :
    IsFunctorHom m n f where
  map_map := map_map
  map_mapConst := map_mapConst_of_map_map f map_map

variable (m) in
protected theorem id : IsFunctorHom m m id where
  map_map _ _ := rfl
  map_mapConst _ _ := rfl

protected theorem comp {f : ∀ {α}, n α → p α} {g : ∀ {α}, m α → n α}
    (hf : IsFunctorHom n p f) (hg : IsFunctorHom m n g) :
    IsFunctorHom m p (f ∘ g) where
  map_map _ _ := by simp [hf.map_map, hg.map_map]
  map_mapConst _ _ := by simp [hf.map_mapConst, hg.map_mapConst]

end IsFunctorHom


/-! ### Applicative Homomorphisms -/

/--
A function `f` is a morphism of applicatives if it preserves `pure`, `<$>`, `<*>`, `<*`, and `*>`.
-/
structure IsApplicativeHom (m n) [Applicative m] [Applicative n] (f : ∀ {α}, m α → n α) : Prop
    extends IsFunctorHom m n f where
  map_pure {α} (a : α) : f (pure a) = pure a
  map_seq {α β} (x : m (α → β)) (y : Unit → m α) :
      f (Seq.seq x y) = Seq.seq (f x) (f <| y ·)
  map_seqLeft {α β} (x : m α) (y : Unit → m β) :
      f (SeqLeft.seqLeft x y) = SeqLeft.seqLeft (f x) (f <| y ·)
  map_seqRight {α β} (x : m α) (y : Unit → m β) :
      f (SeqRight.seqRight x y) = SeqRight.seqRight (f x) (f <| y ·)


namespace IsApplicativeHom
variable {m n p : Type _ → Type _} [Applicative m] [Applicative n] [Applicative p]

attribute [grind .] map_pure map_seq map_seqLeft map_seqRight
attribute [grind →] toIsFunctorHom

private theorem map_map_of_map_pure_map_seq
    [LawfulApplicative m] [LawfulApplicative n] (f : ∀ {α}, m α → n α)
    (map_pure : ∀ {α} (a : α), f (pure a) = pure a)
    (map_seq : ∀ {α β} (x : m (α → β)) (y : Unit → m α),
      f (Seq.seq x y) = Seq.seq (f x) (f <| y ·)) :
    ∀ {α β} (g : α → β) (x : m α), f (g <$> x) = g <$> f x := by
  intros α β g x
  rw [← pure_seq, ← pure_seq]
  change f (Seq.seq (pure g) (fun _ => x)) = Seq.seq (pure g) (fun _ => f x)
  rw [map_seq, map_pure]

private theorem map_seqLeft_of_map_seq_map_map
    [LawfulApplicative m] [LawfulApplicative n] (f : ∀ {α}, m α → n α)
    (map_map : ∀ {α β} (g : α → β) (x : m α), f (g <$> x) = g <$> f x)
    (map_seq : ∀ {α β} (x : m (α → β)) (y : Unit → m α),
      f (Seq.seq x y) = Seq.seq (f x) (f <| y ·)) :
    ∀ {α β} (x : m α) (y : Unit → m β),
      f (SeqLeft.seqLeft x y) = SeqLeft.seqLeft (f x) (f <| y ·) := by
  intros α β x y
  let y' := y (); have hy : y = fun _ => y' := rfl; clear_value y'; subst y
  simp [seqLeft_eq, map_seq, map_map]

private theorem map_seqRight_of_map_seq_map_map
    [LawfulApplicative m] [LawfulApplicative n] (f : ∀ {α}, m α → n α)
    (map_map : ∀ {α β} (g : α → β) (x : m α), f (g <$> x) = g <$> f x)
    (map_seq : ∀ {α β} (x : m (α → β)) (y : Unit → m α),
      f (Seq.seq x y) = Seq.seq (f x) (f <| y ·)) :
    ∀ {α β} (x : m α) (y : Unit → m β),
      f (SeqRight.seqRight x y) = SeqRight.seqRight (f x) (f <| y ·) := by
  intros α β x y
  let y' := y (); have hy : y = fun _ => y' := rfl; clear_value y'; subst y
  simp [seqRight_eq, map_seq, map_map]

/-- Construct an `IsApplicativeHom` for lawful applicatives from `map_pure` and `map_seq`. -/
theorem mk' [LawfulApplicative m] [LawfulApplicative n] {f : ∀ {α}, m α → n α}
    (map_pure : ∀ {α} (a : α), f (pure a) = pure a)
    (map_seq : ∀ {α β} (x : m (α → β)) (y : Unit → m α),
      f (Seq.seq x y) = Seq.seq (f x) (f <| y ·)) :
    IsApplicativeHom m n f where
  map_pure
  toIsFunctorHom := .mk' (map_map_of_map_pure_map_seq f map_pure map_seq)
  map_seq
  map_seqLeft := map_seqLeft_of_map_seq_map_map f
    (map_map_of_map_pure_map_seq f map_pure map_seq) map_seq
  map_seqRight := map_seqRight_of_map_seq_map_map f
    (map_map_of_map_pure_map_seq f map_pure map_seq) map_seq

variable (m) in
protected theorem id : IsApplicativeHom m m id where
  map_pure _ := rfl
  toIsFunctorHom := IsFunctorHom.id m
  map_seq _ _ := rfl
  map_seqLeft _ _ := rfl
  map_seqRight _ _ := rfl

protected theorem comp {f : ∀ {α}, n α → p α} {g : ∀ {α}, m α → n α}
    (hf : IsApplicativeHom n p f) (hg : IsApplicativeHom m n g) :
    IsApplicativeHom m p (f ∘ g) where
  map_pure _ := by simp [hf.map_pure, hg.map_pure]
  toIsFunctorHom := hf.toIsFunctorHom.comp hg.toIsFunctorHom
  map_seq _ _ := by simp [hf.map_seq, hg.map_seq]
  map_seqLeft _ _ := by simp [hf.map_seqLeft, hg.map_seqLeft]
  map_seqRight _ _ := by simp [hf.map_seqRight, hg.map_seqRight]

end IsApplicativeHom


/-! ### Monad Homomorphisms -/

/--
A function `f` is a morphism of monads if it preserves `pure`, `>>=`, `<$>`, `<*>`, `<*`, and `*>`.
-/
structure IsMonadHom (m n) [Monad m] [Monad n] (f : ∀ {α}, m α → n α) : Prop
    extends IsApplicativeHom m n f where
  map_bind {α β} (x : m α) (y : α → m β) : f (x >>= y) = f x >>= (f <| y ·)

namespace IsMonadHom
variable {m n p : Type _ → Type _} [Monad m] [Monad n] [Monad p]

attribute [grind .] map_bind
attribute [grind →] toIsApplicativeHom

private theorem map_map_of_map_pure_map_bind
    [LawfulMonad m] [LawfulMonad n] (f : ∀ {α}, m α → n α)
    (map_pure : ∀ {α} (a : α), f (pure a) = pure a)
    (map_bind : ∀ {α β} (x : m α) (y : α → m β), f (x >>= y) = f x >>= (f <| y ·)) :
    ∀ {α β} (g : α → β) (x : m α), f (g <$> x) = g <$> f x := by
  intros α β g x
  simp [← bind_pure_comp, map_bind, map_pure]

private theorem map_seq_of_map_pure_map_bind
    [LawfulMonad m] [LawfulMonad n] (f : ∀ {α}, m α → n α)
    (map_pure : ∀ {α} (a : α), f (pure a) = pure a)
    (map_bind : ∀ {α β} (x : m α) (y : α → m β), f (x >>= y) = f x >>= (f <| y ·)) :
    ∀ {α β} (x : m (α → β)) (y : Unit → m α),
      f (Seq.seq x y) = Seq.seq (f x) (f <| y ·) := by
  intros α β x y
  let y' := y (); have hy : y = fun _ => y' := rfl; clear_value y'; subst y
  simp [seq_eq_bind_map, map_map_of_map_pure_map_bind f map_pure, map_bind]

/-- Construct an `IsMonadHom` for lawful monads from `map_pure` and `map_bind`. -/
theorem mk' [LawfulMonad m] [LawfulMonad n] {f : ∀ {α}, m α → n α}
    (map_pure : ∀ {α} (a : α), f (pure a) = pure a)
    (map_bind : ∀ {α β} (x : m α) (y : α → m β), f (x >>= y) = f x >>= (f <| y ·)) :
    IsMonadHom m n f where
  map_bind
  toIsApplicativeHom := .mk' map_pure (map_seq_of_map_pure_map_bind f map_pure map_bind)

variable (m) in
protected theorem id : IsMonadHom m m id where
  toIsApplicativeHom := IsApplicativeHom.id m
  map_bind _ _ := rfl

protected theorem comp {f : ∀ {α}, n α → p α} {g : ∀ {α}, m α → n α}
    (hf : IsMonadHom n p f) (hg : IsMonadHom m n g) :
    IsMonadHom m p (f ∘ g) where
  toIsApplicativeHom := hf.toIsApplicativeHom.comp hg.toIsApplicativeHom
  map_bind _ _ := by simp [hf.map_bind, hg.map_bind]

end IsMonadHom

/-! ### Alternative Homomorphisms -/

/--
A function `f` is a morphism of alternatives if it preserves `pure`, `<$>`, `<*>`, `<*`, `*>`,
`failure`, and `orElse`.
-/
structure IsAlternativeHom (m n) [Alternative m] [Alternative n] (f : ∀ {α}, m α → n α) : Prop
    extends IsApplicativeHom m n f where
  map_failure {α} : f (Alternative.failure : m α) = Alternative.failure
  map_orElse {α} (x : m α) (y : Unit → m α) :
    f (HOrElse.hOrElse x y) = HOrElse.hOrElse (f x) (f <| y ·)

namespace IsAlternativeHom
variable {m n p : Type _ → Type _} [Alternative m] [Alternative n] [Alternative p]

attribute [grind .] map_failure map_orElse
attribute [grind →] toIsApplicativeHom

/-- Construct an `IsAlternativeHom` for lawful applicatives from `map_pure`, `map_seq`,
`map_failure`, and `map_orElse`. -/
theorem mk' [LawfulApplicative m] [LawfulApplicative n] {f : ∀ {α}, m α → n α}
    (map_pure : ∀ {α} (a : α), f (pure a) = pure a)
    (map_seq : ∀ {α β} (x : m (α → β)) (y : Unit → m α),
      f (Seq.seq x y) = Seq.seq (f x) (f <| y ·))
    (map_failure : ∀ {α}, f (Alternative.failure : m α) = Alternative.failure)
    (map_orElse : ∀ {α} (x : m α) (y : Unit → m α),
      f (HOrElse.hOrElse x y) = HOrElse.hOrElse (f x) (f <| y ·)) :
    IsAlternativeHom m n f where
  toIsApplicativeHom := .mk' map_pure map_seq
  map_failure
  map_orElse

variable (m) in
protected theorem id : IsAlternativeHom m m id where
  toIsApplicativeHom := IsApplicativeHom.id m
  map_failure := rfl
  map_orElse _ _ := rfl

protected theorem comp {f : ∀ {α}, n α → p α} {g : ∀ {α}, m α → n α}
    (hf : IsAlternativeHom n p f) (hg : IsAlternativeHom m n g) :
    IsAlternativeHom m p (f ∘ g) where
  toIsApplicativeHom := hf.toIsApplicativeHom.comp hg.toIsApplicativeHom
  map_failure := by simp [hf.map_failure, hg.map_failure]
  map_orElse _ _ := by simp [hf.map_orElse, hg.map_orElse]

end IsAlternativeHom

/-! ### Alternative Monad Homomorphisms -/

/--
A function `f` is a morphism of alternative monads if it preserves monadic and alternative
structure.
-/
structure IsAlternativeMonadHom (m n) [AlternativeMonad m] [AlternativeMonad n]
    (f : ∀ {α}, m α → n α) : Prop
    extends IsMonadHom m n f, IsAlternativeHom m n f

namespace IsAlternativeMonadHom
variable {m n p : Type _ → Type _} [AlternativeMonad m] [AlternativeMonad n] [AlternativeMonad p]

attribute [grind →] toIsMonadHom toIsAlternativeHom

/-- Construct an `IsAlternativeMonadHom` for lawful monads from `map_pure`, `map_bind`,
`map_failure`, and `map_orElse`. -/
theorem mk' [LawfulMonad m] [LawfulMonad n] {f : ∀ {α}, m α → n α}
    (map_pure : ∀ {α} (a : α), f (pure a) = pure a)
    (map_bind : ∀ {α β} (x : m α) (y : α → m β), f (x >>= y) = f x >>= (f <| y ·))
    (map_failure : ∀ {α}, f (Alternative.failure : m α) = Alternative.failure)
    (map_orElse : ∀ {α} (x : m α) (y : Unit → m α),
      f (HOrElse.hOrElse x y) = HOrElse.hOrElse (f x) (f <| y ·)) :
    IsAlternativeMonadHom m n f where
  toIsMonadHom := .mk' map_pure map_bind
  map_failure
  map_orElse

variable (m) in
protected theorem id : IsAlternativeMonadHom m m id where
  toIsMonadHom := IsMonadHom.id m
  map_failure := rfl
  map_orElse _ _ := rfl

protected theorem comp {f : ∀ {α}, n α → p α} {g : ∀ {α}, m α → n α}
    (hf : IsAlternativeMonadHom n p f) (hg : IsAlternativeMonadHom m n g) :
    IsAlternativeMonadHom m p (f ∘ g) where
  toIsMonadHom := hf.toIsMonadHom.comp hg.toIsMonadHom
  map_failure := by simp [hf.map_failure, hg.map_failure]
  map_orElse _ _ := by simp [hf.map_orElse, hg.map_orElse]

end IsAlternativeMonadHom

end Cslib
