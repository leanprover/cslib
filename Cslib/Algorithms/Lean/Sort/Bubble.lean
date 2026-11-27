/-
Copyright (c) 2026 Robert Joseph George. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/
module

public import Mathlib.Order.Defs.Unbundled
public import Cslib.Foundations.Control.Monad.IsMonadHom

/-!
# Bubble sort

This file defines bubble sort on lists, `List.bubbleSort r`, with the same conventions as
Mathlib's `List.insertionSort`, and a monadic version `List.bubbleSortM`. The monadic version can
be instantiated with `Id` to recover `List.bubbleSort`, or with `TimeM` or `FreeM` for
algorithmic analysis.

A pass `List.bubblePass r a l` carries a running candidate through `a :: l` from left to right.
When the candidate `x` meets the next element `b` and `r x b` holds, `x` is left behind and `b`
becomes the candidate; otherwise `b` is left behind and `x` moves on. For a total order this
means the candidate only overtakes strictly smaller elements, so equivalent elements are never
exchanged and the sort is stable. After the pass the candidate is a maximum and is placed last,
and the elements left behind are sorted recursively.

## Main definitions

* `List.bubblePass`: one pass, returning the elements left behind and the final candidate.
* `List.bubbleSort`: bubble sort.
* `List.bubblePassM`, `List.bubbleSortM`: monadic versions, for a comparator `α → α → m Bool`.

## Main results

* `List.perm_bubbleSort`: `bubbleSort r l` is a permutation of `l`, hence
  `List.length_bubbleSort` and `List.mem_bubbleSort`.
* `List.pairwise_bubbleSort`: `bubbleSort r l` is sorted when `r` is total and transitive.
* `List.sublist_bubbleSort`: stability. A sublist of `l` that is sorted for `r` is a sublist of
  `bubbleSort r l`, for any relation `r`.
* `List.bubbleSortM_pure` and `Cslib.IsMonadHom.map_listBubbleSortM`: the monadic version
  computes `List.bubbleSort` for a pure comparator and commutes with monad morphisms.
-/

public section

open Cslib (IsMonadHom)

namespace List

section BubbleSort

variable {α : Type*} (r : α → α → Prop) [DecidableRel r]

/-- `bubblePass r a l` is one pass of bubble sort over `a :: l`. It carries a candidate,
initially `a`, from left to right: at the next element `b`, the candidate is left behind and `b`
takes over if `r candidate b`, and otherwise `b` is left behind. It returns the elements left
behind, in order, and the final candidate. -/
def bubblePass (a : α) : List α → List α × α
  | [] => ([], a)
  | b :: l =>
    if r a b then
      let p := bubblePass b l
      (a :: p.1, p.2)
    else
      let p := bubblePass a l
      (b :: p.1, p.2)

/-- A pass over `[a]` leaves nothing behind and ends with `a`. -/
@[simp, grind =] theorem bubblePass_nil (a : α) : bubblePass r a [] = ([], a) := by
  rfl

/-- One step of a pass: the candidate `a` is left behind if `r a b`, and `b` is otherwise. -/
@[simp, grind =] theorem bubblePass_cons (a b : α) (l : List α) :
    bubblePass r a (b :: l) =
      if r a b then (a :: (bubblePass r b l).1, (bubblePass r b l).2)
      else (b :: (bubblePass r a l).1, (bubblePass r a l).2) := by
  rfl

/-- A pass over `a :: l` leaves behind as many elements as `l` has. -/
@[simp]
theorem length_bubblePass (a : α) (l : List α) : (bubblePass r a l).1.length = l.length := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih =>
    rw [bubblePass_cons]
    split <;> rw [length_cons, length_cons, ih]

/-- `bubbleSort r l` sorts `l` using bubble sort: a `bubblePass` moves a maximal element (when
`r` is total and transitive) to the end, and the elements left behind are sorted recursively. -/
def bubbleSort : List α → List α
  | [] => []
  | a :: l => bubbleSort (bubblePass r a l).1 ++ [(bubblePass r a l).2]
termination_by l => l.length
decreasing_by
  rw [length_bubblePass, length_cons]
  exact Nat.lt_add_one _

/-- Bubble sort of the empty list. -/
@[simp, grind =] theorem bubbleSort_nil : bubbleSort r [] = [] := by
  rw [bubbleSort]

/-- Bubble sort makes one pass, sorts the elements left behind and appends the candidate. -/
@[simp, grind =] theorem bubbleSort_cons (a : α) (l : List α) :
    bubbleSort r (a :: l) = bubbleSort r (bubblePass r a l).1 ++ [(bubblePass r a l).2] := by
  rw [bubbleSort]

/-- A pass returns a permutation of its input, with the final candidate placed last. -/
theorem perm_bubblePass (a : α) (l : List α) :
    (bubblePass r a l).1 ++ [(bubblePass r a l).2] ~ a :: l := by
  induction l generalizing a with
  | nil => exact Perm.refl [a]
  | cons b l ih =>
    by_cases hab : r a b
    · rw [bubblePass_cons, ite_eq_left hab]
      exact (ih b).cons a
    · rw [bubblePass_cons, ite_eq_right hab]
      exact ((ih a).cons b).trans (Perm.swap a b l)

/-- `bubbleSort r l` is a permutation of `l`. -/
theorem perm_bubbleSort (l : List α) : bubbleSort r l ~ l := by
  fun_induction bubbleSort r l with
  | case1 => exact Perm.refl []
  | case2 a l ih => exact (ih.append_right _).trans (perm_bubblePass r a l)

/-- `bubbleSort r l` has the same length as `l`. -/
@[simp]
theorem length_bubbleSort (l : List α) : (bubbleSort r l).length = l.length :=
  (perm_bubbleSort r l).length_eq

/-- `bubbleSort r l` has the same elements as `l`. -/
@[simp]
theorem mem_bubbleSort {l : List α} {a : α} : a ∈ bubbleSort r l ↔ a ∈ l :=
  (perm_bubbleSort r l).mem_iff

/-- For a total transitive `r`, the final candidate of a pass over `a :: l` is a maximum: every
element of `a :: l` is related to it. -/
theorem rel_bubblePass_snd_of_mem [Std.Total r] [IsTrans α r] {a b : α} {l : List α}
    (hb : b ∈ a :: l) : r b (bubblePass r a l).2 := by
  induction l generalizing a b with
  | nil =>
    obtain rfl := mem_singleton.1 hb
    exact refl_of r _
  | cons c l ih =>
    rw [mem_cons, mem_cons] at hb
    by_cases hac : r a c
    · rw [bubblePass_cons, ite_eq_left hac]
      rcases hb with rfl | rfl | hb
      · exact trans_of r hac (ih mem_cons_self)
      · exact ih mem_cons_self
      · exact ih (mem_cons_of_mem c hb)
    · rw [bubblePass_cons, ite_eq_right hac]
      rcases hb with rfl | rfl | hb
      · exact ih mem_cons_self
      · exact trans_of r ((total_of r _ _).resolve_right hac) (ih mem_cons_self)
      · exact ih (mem_cons_of_mem a hb)

/-- `bubbleSort r l` is sorted for a total transitive relation `r`. -/
theorem pairwise_bubbleSort [Std.Total r] [IsTrans α r] (l : List α) :
    (bubbleSort r l).Pairwise r := by
  fun_induction bubbleSort r l with
  | case1 => exact Pairwise.nil
  | case2 a l ih =>
    refine pairwise_append.2 ⟨ih, pairwise_singleton r _, fun b hb c hc => ?_⟩
    obtain rfl := mem_singleton.1 hc
    -- `b` was left behind by the pass, so it is an element of `a :: l`.
    have hb' : b ∈ a :: l :=
      (perm_bubblePass r a l).subset (mem_append_left _ ((perm_bubbleSort r _).subset hb))
    exact rel_bubblePass_snd_of_mem r hb'

/-- A pass keeps every sorted sublist of `a :: l` in order: the candidate only overtakes an
element `b` when `r candidate b` fails, and then `b` cannot follow the candidate in a sublist that
is sorted for `r`. -/
theorem sublist_bubblePass {a : α} {l c : List α} (hc : c.Pairwise r) (hcl : c <+ a :: l) :
    c <+ (bubblePass r a l).1 ++ [(bubblePass r a l).2] := by
  induction l generalizing a c with
  | nil => exact hcl
  | cons b l ih =>
    by_cases hab : r a b
    · rw [bubblePass_cons, ite_eq_left hab]
      cases hcl with
      | cons _ hcl => exact (ih hc hcl).cons a
      | cons_cons _ hcl => exact (ih hc.of_cons hcl).cons_cons a
    · rw [bubblePass_cons, ite_eq_right hab]
      cases hcl with
      | cons _ hcl =>
        cases hcl with
        | cons _ hcl => exact (ih hc (hcl.cons a)).cons b
        | cons_cons _ hcl => exact (ih hc.of_cons (hcl.cons a)).cons_cons b
      | cons_cons _ hcl =>
        -- `c` starts with `a`, so it cannot continue with `b`, as `r a b` fails.
        cases hcl with
        | cons _ hcl => exact (ih hc (hcl.cons_cons a)).cons b
        | cons_cons _ _ => exact absurd (rel_of_pairwise_cons hc mem_cons_self) hab

/-- Bubble sort is stable: if `c` is a sorted sublist of `l`, then `c` is still a sublist of
`bubbleSort r l`. -/
theorem sublist_bubbleSort {l c : List α} (hc : c.Pairwise r) (hcl : c <+ l) :
    c <+ bubbleSort r l := by
  induction l using bubbleSort.induct r generalizing c with
  | case1 => rwa [bubbleSort_nil]
  | case2 a l ih =>
    rw [bubbleSort_cons]
    obtain ⟨c₁, c₂, rfl, h₁, h₂⟩ := sublist_append_iff.1 (sublist_bubblePass r hc hcl)
    exact (ih (hc.sublist (sublist_append_left c₁ c₂)) h₁).append h₂

end BubbleSort

section Monadic

variable {m n} [Monad m] [Monad n] (r : α → α → m Bool)

/-- A monadic version of `List.bubblePass`. -/
def bubblePassM (a : α) : List α → m (List α × α)
  | [] => return ([], a)
  | b :: l => do
    if ← r a b then
      let p ← bubblePassM b l
      return (a :: p.1, p.2)
    else
      let p ← bubblePassM a l
      return (b :: p.1, p.2)

/-- `bubblePassM` on `[a]` returns `([], a)` without comparing. -/
@[simp, grind =] theorem bubblePassM_nil (a : α) : bubblePassM r a [] = pure ([], a) := by
  rfl

/-- One step of `bubblePassM`: one comparison, then the rest of the pass. -/
@[simp, grind =] theorem bubblePassM_cons (a b : α) (l : List α) :
    bubblePassM r a (b :: l) = do
      if ← r a b then
        let p ← bubblePassM r b l
        return (a :: p.1, p.2)
      else
        let p ← bubblePassM r a l
        return (b :: p.1, p.2) := by
  rfl

/-- With a pure comparator, `bubblePassM` computes `List.bubblePass`. -/
@[simp]
theorem bubblePassM_pure [LawfulMonad m] (r : α → α → Bool) (a : α) (l : List α) :
    bubblePassM (fun x y => (pure (r x y) : m Bool)) a l = pure (bubblePass (r · ·) a l) := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih =>
    by_cases h : r a b = true
    · simp only [bubblePassM_cons, bubblePass_cons, pure_bind, h, ↓reduceIte, ih]
    · simp only [bubblePassM_cons, bubblePass_cons, pure_bind, h, Bool.false_eq_true, ↓reduceIte,
        ih]

/-- `bubblePassM` in `Id` is `List.bubblePass`. -/
@[simp]
theorem idRun_bubblePassM (r : α → α → Id Bool) (a : α) (l : List α) :
    Id.run (bubblePassM r a l) = bubblePass (fun x y => Id.run <| r x y) a l :=
  bubblePassM_pure _ _ _

/-- A monad morphism commutes with `bubblePassM`, acting on the comparator. -/
@[grind .]
theorem _root_.Cslib.IsMonadHom.map_listBubblePassM {f : {β : Type} → m β → n β}
    (hf : IsMonadHom m n f) (r : α → α → m Bool) (a : α) (l : List α) :
    f (bubblePassM r a l) = bubblePassM (fun x y => f (r x y)) a l := by
  induction l generalizing a with
  | nil => simp only [bubblePassM_nil, hf.map_pure]
  | cons b l ih => simp only [bubblePassM_cons, hf.map_bind, apply_ite f, hf.map_pure, ih]

/-- A monadic version of `List.bubbleSort`.

The recursive call sorts a list produced inside the monad, whose length the termination checker
cannot see, so `bubbleSortM.go` recurses on explicit fuel; `l.length` passes are enough for `l`.
`bubbleSortM_cons` unfolds one pass without mentioning the fuel. -/
def bubbleSortM (l : List α) : m (List α) :=
  go l.length l
where
  /-- Bubble sort with at most `fuel` passes. When the fuel runs out the list is returned as it
  is. -/
  go : Nat → List α → m (List α)
    | 0, l => return l
    | _ + 1, [] => return []
    | fuel + 1, a :: l => do
      let p ← bubblePassM r a l
      return (← go fuel p.1) ++ [p.2]

/-- A continuation of `bubblePassM r a l` only matters on pairs whose first component is as long
as `l`. -/
private theorem bind_bubblePassM_congr [LawfulMonad m] {f g : List α × α → m β} (a : α)
    (l : List α) (h : ∀ p : List α × α, p.1.length = l.length → f p = g p) :
    bubblePassM r a l >>= f = bubblePassM r a l >>= g := by
  induction l generalizing a f g with
  | nil =>
    rw [bubblePassM_nil, pure_bind, pure_bind]
    exact h ([], a) rfl
  | cons b l ih =>
    rw [bubblePassM_cons, bind_assoc, bind_assoc]
    refine bind_congr fun c => ?_
    split
    · rw [bind_assoc, bind_assoc]
      exact ih b fun p hp => by
        rw [pure_bind, pure_bind]
        exact h _ (congrArg (· + 1) hp)
    · rw [bind_assoc, bind_assoc]
      exact ih a fun p hp => by
        rw [pure_bind, pure_bind]
        exact h _ (congrArg (· + 1) hp)

/-- `bubbleSortM` of the empty list. -/
@[simp] theorem bubbleSortM_nil : bubbleSortM r [] = pure [] := by
  rfl

/-- `bubbleSortM` makes one pass, sorts the elements left behind and appends the candidate.
This is the fuel-free unfolding; it needs a lawful monad. -/
@[simp] theorem bubbleSortM_cons [LawfulMonad m] (a : α) (l : List α) :
    bubbleSortM r (a :: l) = (do
      let p ← bubblePassM r a l
      return (← bubbleSortM r p.1) ++ [p.2]) := by
  rw [bubbleSortM, length_cons, bubbleSortM.go]
  refine bind_bubblePassM_congr r a l fun p hp => ?_
  rw [bubbleSortM, hp]

/-- With a pure comparator, `bubbleSortM` computes `List.bubbleSort`. -/
@[simp]
theorem bubbleSortM_pure [LawfulMonad m] (xs : List α) (r : α → α → Bool) :
    bubbleSortM (fun x y => (pure (r x y) : m Bool)) xs = pure (bubbleSort (r · ·) xs) := by
  fun_induction bubbleSort (r · ·) xs with
  | case1 => rfl
  | case2 a l ih => rw [bubbleSortM_cons, bubblePassM_pure, pure_bind, ih, pure_bind]

/-- `bubbleSortM` in `Id` is `List.bubbleSort`. -/
@[simp]
theorem idRun_bubbleSortM (xs : List α) (r : α → α → Id Bool) :
    Id.run (bubbleSortM r xs) = bubbleSort (fun x y => Id.run <| r x y) xs :=
  bubbleSortM_pure _ _

/-- A monad morphism commutes with `bubbleSortM`, acting on the comparator. -/
@[grind .]
theorem _root_.Cslib.IsMonadHom.map_listBubbleSortM {f : {β : Type} → m β → n β}
    (hf : IsMonadHom m n f) (r : α → α → m Bool) (xs : List α) :
    f (bubbleSortM r xs) = bubbleSortM (fun x y => f (r x y)) xs := by
  suffices h : ∀ fuel l,
      f (bubbleSortM.go r fuel l) = bubbleSortM.go (fun x y => f (r x y)) fuel l from h _ xs
  intro fuel
  induction fuel with
  | zero => exact fun l => hf.map_pure l
  | succ fuel ih =>
    rintro (_ | ⟨a, l⟩)
    · exact hf.map_pure []
    · simp only [bubbleSortM.go, hf.map_bind, hf.map_pure, hf.map_listBubblePassM, ih]

end Monadic

end List
