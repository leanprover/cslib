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
import Mathlib.Data.List.Basic

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

/-! ### Monad homomorphisms on the `List` monad -/

@[grind .]
theorem IsApplicativeHom.map_listSingleton
    {F : ∀ {α}, List α → List α} (hf : IsApplicativeHom List List F) {α} (a : α) :
    F ([a] : List α) = [a] := hf.map_pure _

@[grind .]
theorem IsMonadHom.map_listFlatMap
    {F : ∀ {α}, List α → List α} (hf : IsMonadHom List List F) {α β} (l : List α) (g : α → List β) :
    F (l.flatMap g) = (F l).flatMap (F <| g ·) := hf.map_bind _ _

@[grind .]
theorem IsFunctorHom.map_listNil {F : ∀ {α}, List α → List α} (hf : IsFunctorHom List List F) {α} :
    F ([] : List α) = [] := by
  simpa [Subsingleton.elim (F ([] : List PEmpty)) []]
    using (hf.map_map PEmpty.elim []).symm

protected theorem List.isMonadHom_reverse : IsMonadHom List List List.reverse :=
  .mk' (fun _ => rfl) (fun _ _ => List.reverse_flatMap)

section uniqueness

/-- A property holds on all lists if it holds on the nil list, the singleton list,
and concatenations thereof. -/
private theorem List.nil_singleton_append_induction {motive : List α → Prop}
    (nil : motive []) (singleton : ∀ a, motive [a])
    (append : ∀ xs ys, motive xs → motive ys → motive (xs ++ ys)) :
    ∀ l, motive l
  | [] => nil
  | x :: xs => append [x] xs (singleton x) (nil_singleton_append_induction nil singleton append xs)

/-- Universe-generic type with two elements. This is used only internally in a proof, and keeps
things more concise than `ULift Bool`. -/
private inductive Two : Type u | a | b

private theorem eq_ab_or_ba : ∀ (l : List Two),
    l.flatMap (fun | .a => [.a] | .b => []) = [Two.a] →
    l.flatMap (fun | .a => [] | .b => [.b]) = [Two.b] →
    l = [Two.a, Two.b] ∨ l = [Two.b, Two.a]
  | [.a, .b], _, _ => .inl rfl
  | [.b, .a], _, _ => .inr rfl

/-- The only monad morphisms on lists are the identity and reversal. -/
theorem isMonadHom_list_iff (f : ∀ {α : Type u}, List α → List α) :
    IsMonadHom List List @f ↔ @f = (@id <| List ·) ∨ @f = @List.reverse := by
  refine ⟨fun h => ?_, ?_⟩
  · have h_append {α} (xs ys : List α) :
        f (xs ++ ys) = (f [Two.a, Two.b]).flatMap (fun | .a => f xs | .b => f ys) := by
      have : xs ++ ys = [Two.a, Two.b].flatMap (fun | .a => xs | .b => ys) := by
        simp
      rw [this, h.map_listFlatMap]
      congr 1; funext x; cases x <;> rfl
    refine (eq_ab_or_ba (f [Two.a, Two.b]) ?_ ?_).imp (fun hL => ?_) (fun hL => ?_)
    · simpa [h.map_listNil, h.map_listSingleton] using (h_append [Two.a] []).symm
    · simpa [h.map_listNil, h.map_listSingleton] using (h_append [] [Two.b]).symm
    · funext α l
      induction l using List.nil_singleton_append_induction with grind
    · funext α l
      induction l using List.nil_singleton_append_induction with grind
  · rintro (rfl | rfl)
    · exact .id _
    · exact List.isMonadHom_reverse

end uniqueness

end Cslib
