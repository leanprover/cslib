/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Cslib.Algorithms.Lean.Query.Sort.Insertion.Lemmas

/-! # Naturality of the monad-generic sorts

`List.orderedInsertM` and `List.insertionSortM` are generic over the monad supplying the
comparator, and the query programs are their instantiations at `FreeM (LEQuery α)`. This
file proves the generic programs are natural in the monad: any monad morphism commutes
with them. The morphism laws are stated inline; they are the fields of `IsMonadHom` from
https://github.com/leanprover/cslib/pull/856. No lawfulness of either monad is needed.

Since evaluation against an oracle is a monad morphism `FreeM (LEQuery α) → Id`,
naturality identifies the executable `Id` instantiation with `List.insertionSort`, with
no separate proof about the generic definition; and because the query programs are
definitional instantiations, the framework's complexity bounds apply to the generic
programs unchanged.
-/

open Cslib Cslib.Query

universe v w

section Naturality

variable {α : Type} {m : Type → Type v} [Monad m] {n : Type → Type w} [Monad n]
  (φ : ∀ {β}, m β → n β)
  (hpure : ∀ {β} (a : β), φ (pure a) = pure a)
  (hbind : ∀ {β γ} (x : m β) (f : β → m γ), φ (x >>= f) = φ x >>= (φ <| f ·))

include hpure hbind

theorem List.orderedInsertM_naturality (cmp : α → α → m Bool) (x : α) (xs : List α) :
    φ (xs.orderedInsertM cmp x) = xs.orderedInsertM (fun a b => φ (cmp a b)) x := by
  induction xs with
  | nil => simp [List.orderedInsertM, hpure]
  | cons y ys ih =>
    simp only [List.orderedInsertM, hbind]
    congr 1
    funext b
    cases b <;> simp [hbind, hpure, ih]

theorem List.insertionSortM_naturality (cmp : α → α → m Bool) (xs : List α) :
    φ (xs.insertionSortM cmp) = xs.insertionSortM (fun a b => φ (cmp a b)) := by
  induction xs with
  | nil => simp [List.insertionSortM, hpure]
  | cons x xs ih =>
    simp only [List.insertionSortM, hbind, ih, List.orderedInsertM_naturality φ hpure hbind]

end Naturality

/-! ## Consequences of naturality -/

variable {α : Type}

/-- Evaluation against an oracle is a monad morphism to `Id`, so by naturality the
`Id` instantiation of the generic program is the evaluation of the query program. -/
theorem insertionSortM_eval (oracle : {ι : Type} → LEQuery α ι → ι) (xs : List α) :
    (insertionSort xs).eval oracle =
      xs.insertionSortM (m := Id) fun a b => oracle (.le a b) :=
  List.insertionSortM_naturality (m := FreeM (LEQuery α)) (n := Id)
    (fun {_} p => FreeM.eval oracle p)
    (fun _ => rfl) (fun x f => FreeM.eval_bind oracle x f) _ xs

/-- The executable `Id` instantiation of the generic program is `List.insertionSort`. -/
example (oracle : {ι : Type} → LEQuery α ι → ι) (xs : List α) :
    xs.insertionSortM (m := Id) (fun a b => oracle (.le a b)) =
      xs.insertionSort fun a b => oracle (.le a b) := by
  rw [← insertionSortM_eval, eval_insertionSort]

/-- The query-complexity bound applies to the generic program at its query
instantiation, definitionally. -/
example (oracle : {ι : Type} → LEQuery α ι → ι) (xs : List α) :
    (xs.insertionSortM LEQuery.ask).countQueries oracle ≤
      xs.length * (xs.length - 1) / 2 :=
  insertionSort_countQueries_le oracle xs

example : Id.run ([3, 1, 2].insertionSortM fun a b : Nat => pure (decide (a ≤ b))) =
    [1, 2, 3] := by decide
