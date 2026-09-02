/-
Copyright (c) 2026 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Cslib.Init
public import Cslib.Foundations.Control.Monad.IsMonadHom
public import Mathlib.Data.List.Monad
import all Init.Data.List.Control

/-!
# List operations and monad morphisms

This file proves that monadic operations on lists commute with monad homomorphisms
(and applicative homomorphisms), and that `List.reverse` is a monad homomorphism on `List`.
-/

public section

namespace Cslib

universe u v w
variable {m n : Type u → Type v}

/-! ### Preservation of list operations under applicative homomorphisms -/

namespace IsApplicativeHom
variable [Applicative m] [Applicative n]

@[grind .]
theorem map_listMapA {F : ∀ {α}, m α → n α} (hf : IsApplicativeHom m n F)
    {α : Type w} {β : Type u} (f : α → m β) (l : List α) :
    F (l.mapA f) = l.mapA (F ∘ f) := by
  induction l with grind [List.mapA]

@[grind .]
theorem map_listForA {F : ∀ {α}, m α → n α} (hf : IsApplicativeHom m n F)
    {α : Type w} (l : List α) (f : α → m PUnit) :
    F (l.forA f) = l.forA (F ∘ f) := by
  induction l with grind [List.forA]

end IsApplicativeHom

/-! ### Preservation of list operations under monad homomorphisms -/

namespace IsMonadHom
variable [Monad m] [Monad n]

@[grind .]
theorem map_listMapM'
    {F : ∀ {α}, m α → n α} (hf : IsMonadHom m n F)
    {α : Type w} {β : Type u} (f : α → m β) (l : List α) :
    F (l.mapM' f) = l.mapM' (F ∘ f) := by
  induction l with grind [List.mapM']

@[grind .]
theorem map_listMapM [LawfulMonad m] [LawfulMonad n]
    {F : ∀ {α}, m α → n α} (hf : IsMonadHom m n F)
    {α : Type w} {β : Type u} (f : α → m β) (l : List α) :
    F (l.mapM f) = l.mapM (F ∘ f) := by
  induction l with grind

@[grind .]
theorem map_listForM {F : ∀ {α}, m α → n α} (hf : IsMonadHom m n F)
    {α : Type w} (l : List α) (f : α → m PUnit) :
    F (l.forM f) = l.forM (F ∘ f) := by
  induction l with grind [List.forM]

@[grind .]
theorem map_listFoldlM {F : ∀ {α}, m α → n α} (hf : IsMonadHom m n F)
    {s : Type u} {α : Type w} (f : s → α → m s) (init : s) (l : List α) :
    F (l.foldlM f init) = l.foldlM (fun s a => F (f s a)) init := by
  induction l generalizing init with grind [List.foldlM]

@[grind .]
theorem map_listFoldrM {F : ∀ {α}, m α → n α} (hf : IsMonadHom m n F)
    {s : Type u} {α : Type w} (f : α → s → m s) (init : s) (l : List α) :
    F (l.foldrM f init) = l.foldrM (fun a s => F (f a s)) init := by
  simp only [List.foldrM]
  exact hf.map_listFoldlM (fun s a => f a s) init l.reverse

@[grind .]
theorem map_listFindSomeM?
    {F : ∀ {α}, m α → n α} (hf : IsMonadHom m n F)
    {α : Type w} {β : Type u} (f : α → m (Option β)) (l : List α) :
    F (l.findSomeM? f) = l.findSomeM? (F ∘ f) := by
  induction l with grind

@[grind .]
theorem map_listFindM? {m n : Type → Type v} [Monad m] [Monad n]
    {F : ∀ {α}, m α → n α} (hf : IsMonadHom m n F)
    {α : Type} (p : α → m Bool) (l : List α) :
    F (l.findM? p) = l.findM? (F ∘ p) := by
  induction l with grind [List.findM?]

@[grind .]
theorem map_listAnyM {m n : Type → Type v} [Monad m] [Monad n]
    {F : ∀ {α}, m α → n α} (hf : IsMonadHom m n F)
    {α : Type w} (p : α → m Bool) (l : List α) :
    F (l.anyM p) = l.anyM (F ∘ p) := by
  induction l with grind [List.anyM]

@[grind .]
theorem map_listAllM {m n : Type → Type v} [Monad m] [Monad n]
    {F : ∀ {α}, m α → n α} (hf : IsMonadHom m n F)
    {α : Type w} (p : α → m Bool) (l : List α) :
    F (l.allM p) = l.allM (F ∘ p) := by
  induction l with grind [List.allM]

@[grind .]
theorem map_listFilterAuxM {m n : Type → Type v} [Monad m] [Monad n]
    {F : ∀ {α}, m α → n α} (hf : IsMonadHom m n F)
    {α : Type} (p : α → m Bool) (l acc : List α) :
    F (List.filterAuxM p l acc) = List.filterAuxM (F ∘ p) l acc := by
  induction l generalizing acc with grind [List.filterAuxM]

@[grind .]
theorem map_listFilterM {m n : Type → Type v} [Monad m] [Monad n]
    {F : ∀ {α}, m α → n α} (hf : IsMonadHom m n F)
    {α : Type} (p : α → m Bool) (l : List α) :
    F (l.filterM p) = l.filterM (F ∘ p) := by
  grind [List.filterM]

end IsMonadHom

/-! ### Preservation of list operations under alternative homomorphisms -/

namespace IsAlternativeHom
variable [Alternative m] [Alternative n]

@[grind .]
theorem map_listFirstM {F : ∀ {α}, m α → n α} (hf : IsAlternativeHom m n F)
    {α : Type w} {β : Type u} (f : α → m β) (l : List α) :
    F (l.firstM f) = l.firstM (F ∘ f) := by
  induction l with grind [List.firstM]

end IsAlternativeHom

/-! ### Monad homomorphisms on `List` -/

protected theorem List.isMonadHom_reverse : IsMonadHom List List List.reverse :=
  .mk' (fun _ => rfl) (fun _ _ => List.reverse_flatMap)

/-- The only applicative morphism on lists are the identity and reversal. -/
proof_wanted isApplicative_list_iff (f : ∀ {α}, List α → List α) :
    IsApplicativeHom List List f ↔ @f = (@id <| List ·) ∨ @f = @List.reverse

end Cslib
