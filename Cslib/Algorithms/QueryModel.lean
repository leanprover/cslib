/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Shreyas Srinivas
-/

module

public import Mathlib
public import Cslib.Foundations.Control.Monad.Free.Effects
public import Cslib.Foundations.Control.Monad.Free.Fold
public import Batteries

@[expose] public section

/-
# Query model

This file defines a simple query language modeled as a free monad over a
parametric type of  query operations.

## Main definitions

- `QueryF`, `Prog` : query language and programs
- `evalQuery`, `evalProg` : concrete execution semantics

## Tags

query model, free monad, time complexity, merge sort
-/

namespace Cslib

namespace Algorithms

class PureCosts (α : Type u) where
  pureCost : α

instance : PureCosts ℕ where
  pureCost := 1

structure Model (QType : Type u → Type u) (Cost : Type) [Add Cost] [Zero Cost]
  [PureCosts Cost] where
  evalQuery : QType ι → ι
  cost : QType ι → Cost

namespace Model



section Examples

inductive ListOps (α : Type) : Type → Type  where
  | get (l : List α) (i : Fin l.length) : ListOps α α
  | find (l : List α) (elem : α) : ListOps α ℕ
  | write (l : List α) (i : Fin l.length) (x : α) : ListOps α (List α)


def List_LinSearch_WorstCase [DecidableEq α] : Model (ListOps α) ℕ where
  evalQuery
    | .write l i x => l.set i x
    | .find l elem =>  l.findIdx (· = elem)
    | .get l i => l[i]
  cost
    | .write l i x => l.length
    | .find l elem =>  l.length
    | .get l i => l.length



def List_BinSearch_WorstCase [BEq α] : Model (ListOps α) ℕ where
  evalQuery
    | .write l i x => l.set i x
    | .get l i => l[i]
    | .find l elem => l.findIdx (· == elem)

  cost
    | .find l _ => 1 + Nat.log 2 (l.length)
    | .write l i x => l.length
    | .get l x => l.length

inductive ArrayOps (α : Type) : Type → Type  where
  | get : (l : Array α) → (i : Fin l.size) → ArrayOps α α
  | find :  (l : Array α) → α → ArrayOps α ℕ
  | write : (l : Array α) → (i : Fin l.size) →  (x : α) → ArrayOps α (Array α)

def Array_BinSearch_WorstCase [BEq α] : Model (ArrayOps α) ℕ where
  evalQuery
    | .write l i x => l.set i x
    | .get l i => l[i]
    | .find l elem => l.findIdx (· == elem)

  cost
    | .find l _ => 1 + Nat.log 2 (l.size)
    | .write l i x => 1
    | .get l x => 1



end Examples

end Model

abbrev Prog Q α := FreeM Q α

instance {Q α} : Coe (Q α) (FreeM Q α) where
  coe := FreeM.lift
namespace Prog


def eval [Add Cost] [Zero Cost] [PureCosts Cost]
  (P : Prog Q α) (M : Model Q Cost) : α :=
  match P with
  | .pure x => x
  | .liftBind op cont  =>
      let qval := M.evalQuery op
      eval (cont qval) M

def time [Add Cost] [Zero Cost] [PureCosts Cost]
  (P : Prog Q α) (M : Model Q Cost) : Cost :=
  match P with
  | .pure _ => PureCosts.pureCost
  | .liftBind op cont =>
      let t₁ := M.cost op
      let qval := M.evalQuery op
      t₁ + (time (cont qval) M)

section TimeM

-- The below is a proof of concept and pointless
def interpretQueryIntoTime (M : Model Q ℕ) (q : Q α) : TimeM α where
  ret := M.evalQuery q
  time := M.cost q

def interpretProgIntoTime (P : Prog Q α) (M : Model Q ℕ) : TimeM α where
  ret := eval P M
  time := time P M

def liftProgIntoTime (M : Model Q ℕ) (P : Prog Q α) : TimeM α :=
  P.liftM (interpretQueryIntoTime M)


-- The below lemma only holds if the cost of pure operations is zero. This
-- is however a footgun

-- -- This lemma is a sanity check. This is the only place `TimeM` is used.
-- lemma timing_is_identical : ∀ (P : Prog Q α) (M : Model Q ℕ),
--   time P M = (liftProgIntoTime M P).time := by
--   intro P pm
--   induction P with
--   | pure a =>
--       simp [time,liftProgIntoTime]
--   | liftBind op cont ih =>
--       expose_names
--       simp_all [time, liftProgIntoTime, interpretQueryIntoTime]

end TimeM

section ProgExamples

inductive Arith (α : Type) : Type → Type where
  | add (x y : α) : Arith α α
  | mul (x y : α) : Arith α α
  | neg (x : α) : Arith α α
  | zero : Arith α α
  | one : Arith α α

def RatArithQuery_NatCost : Model (Arith ℚ) ℕ where
  evalQuery q :=
    match q with
    | .add x y => x + y
    | .mul x y => x * y
    | .neg x =>  -x
    | .zero => (0 : ℚ)
    | .one => (1 : ℚ)
  cost _ := 1

structure AddMulCosts where
  addCount : ℕ
  mulCount : ℕ
  pure : ℕ

instance : Zero (AddMulCosts) where
  zero := ⟨0,0,0⟩

instance : PureCosts (AddMulCosts) where
  pureCost := ⟨0,0,1⟩

instance : Add (AddMulCosts) where
    add x y :=
      let ⟨x_addcount, x_mulcount, x_pure⟩ := x
      let ⟨y_addcount, y_mulcount, y_pure⟩ := y
      ⟨x_addcount + y_addcount, x_mulcount + y_mulcount, x_pure + y_pure⟩

def RatArithQuery_AddMulCost : Model (Arith ℚ) AddMulCosts where
  evalQuery
    | .add x y => x + y
    | .mul x y => x * y
    | .neg x =>  -x
    | .zero => (0 : ℚ)
    | .one => (1 : ℚ)
  cost
    | .add _ _ => ⟨1,0,0⟩
    | .mul _ _ => ⟨0,1,0⟩
    | _ => 0

open Arith in
def ex1 : Prog (Arith ℚ) ℚ := do
  let mut x : ℚ ← @zero ℚ
  let mut y ← @one ℚ
  let z ← (add (x + y + y) y)
  let w ← @neg ℚ (←(add z y))
  add w z


#eval ex1.eval RatArithQuery_NatCost
#eval ex1.time RatArithQuery_NatCost
#eval ex1.time RatArithQuery_AddMulCost

section ArraySort
/--
The array version of the sort operations
-/
inductive VecSortOps (α : Type) : Type → Type  where
  | swap : (a : Vector α n) → (i j : Fin n) → VecSortOps α (Vector α n)
  | cmp :  (a : Vector α n) → (i j : Fin n) → VecSortOps α Bool
  | write : (a : Vector α n) → (i : Fin n) → (x : α) → VecSortOps α (Vector α n)
  | read : (a : Vector α n) → (i : Fin n) → VecSortOps α α
  | push : (a : Vector α n) → (elem : α) → VecSortOps α (Vector α (n + 1))

def VecSort_WorstCase [DecidableEq α] : Model (VecSortOps α) ℕ where
  evalQuery
    | .write v i x => v.set i x
    | .cmp l i j =>  l[i] == l[j]
    | .read l i => l[i]
    | .swap l i j => l.swap i j
    | .push a elem => a.push elem

  cost
    | .write l i x => 1
    | .read l i =>  1
    | .cmp l i j => 1
    | .swap l i j => 1
    | .push a elem => 2 -- amortized over array insertion and resizing by doubling

def VecSort_CmpSwap [DecidableEq α] : Model (VecSortOps α) ℕ where
  evalQuery
    | .write v i x => v.set i x
    | .cmp l i j =>  l[i] == l[j]
    | .read l i => l[i]
    | .swap l i j => l.swap i j
    | .push a elem => a.push elem

  cost
    | .cmp l i j => 1
    | .swap l i j => 1
    | _ => 0


open VecSortOps in
def simpleExample (v : Vector ℤ n) (i k : Fin n)
  : Prog (VecSortOps ℤ) (Vector ℤ (n + 1)) :=  do
  let b : Vector ℤ n ← write v i 10
  let mut c : Vector ℤ n ← swap b i k
  let elem ← read c i
  push c elem

#eval (simpleExample #v[1,2,3,4,5] 5 2).eval VecSort_WorstCase
#eval (simpleExample #v[1,2,3,4,5] 5 2).time VecSort_WorstCase
#eval (simpleExample #v[1,2,3,4,5] 5 2).time VecSort_CmpSwap

end ArraySort

section VectorLinearSearch

inductive VecSearch (α : Type) : Type → Type  where
  | compare (a : Vector α n) (i : ℕ) (val : α) : VecSearch α Bool


def VecSearch_Nat [DecidableEq α] : Model (VecSearch α) ℕ where
  evalQuery q :=
    match q with
    | .compare l i x =>  l[i]? == some x
  cost q :=
    match q with
    | .compare _ _ _ => 1

structure CmpCount where
  cmp : ℕ
  pure : ℕ

instance : Add (CmpCount) where
  add x y := ⟨x.1 + y.1, x.2 + y.2⟩

instance : Zero (CmpCount) where
  zero := ⟨0,0⟩

instance : PureCosts (CmpCount) where
  pureCost := ⟨0,1⟩

def VecSearch_Cmp [DecidableEq α] : Model (VecSearch α) CmpCount where
  evalQuery q :=
    match q with
    | .compare l i x =>  l[i]? == some x
  cost q :=
    match q with
    | .compare _ _ _ => ⟨1,0⟩

open VecSearch in
def linearSearchAux (v : Vector α n)
  (x : α) (acc : Bool) (index : ℕ) : Prog (VecSearch α) Bool := do
  if h : index ≥ n then
    return acc
  else
    let cmp_res : Bool ← compare v index x
    if cmp_res then
      return true
    else
      linearSearchAux v x false (index + 1)

open VecSearch in
def linearSearch (v : Vector α n) (x : α) : Prog (VecSearch α) Bool:=
  linearSearchAux v x false 0

#eval (linearSearch #v[12,23,31,42,52,4,6] 4).eval VecSearch_Nat
#eval (linearSearch #v[1,2,3,4,5,6] 7).eval VecSearch_Cmp

#eval (linearSearch #v[1,2,3,22, 11, 12, 4,5,6] 4).time VecSearch_Nat
#eval (linearSearch #v[1,2,3,22, 11, 12, 4,5,6] 7).time VecSearch_Cmp


lemma linearSearch_correct_true [DecidableEq α] (v : Vector α n)
  (hn_pos : n > 0) :
  ∀ x : α, x ∈ v → (linearSearch v x).eval VecSearch_Nat = true := by
  intro x x_mem_v
  simp only [linearSearch]
  induction n with
  | zero =>
      simp_all
  | succ n ih =>
      simp_all only [gt_iff_lt, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true]
      unfold linearSearchAux
      split_ifs with h_cond
      · simp_all
      · unfold eval
        simp_all
        split_ifs with h_find
        · simp [eval]
        · sorry

lemma linearSearch_correct_false [DecidableEq α] (v : Vector α n) :
  ∀ x : α, x ∉ v → (linearSearch v x).eval VecSearch_Nat = false := by
  intro x x_mem_v
  simp only [linearSearch]
  induction n with
  | zero =>
      simp_all [VecSearch_Nat]
      sorry
  | succ n ih =>
      sorry

lemma linearSearch_time_complexity [DecidableEq α] (v : Vector α n) :
  ∀ x : α, (linearSearch v x).time VecSearch_Nat ≤ n + 1 := by
  intro x
  simp only [linearSearch, VecSearch_Nat]
  induction n with
  | zero =>
      simp_all [linearSearchAux, time, PureCosts.pureCost]
  | succ n ih =>
      unfold linearSearchAux
      split_ifs with h_cond
      · simp_all
      · simp [time]
        sorry

-- The Monadic version
open VecSearch in
def linearSearchM (v : Vector α n) (x : α) : Prog (VecSearch α) Bool := do
  let mut comp_res : Bool := false
  for i in [0:n] do
    comp_res ← compare v i x
    if comp_res == true then
      break
    else
      continue
  return comp_res

#eval (linearSearchM #v[12,23,31,42,52,4,6] 4).eval VecSearch_Nat
#eval (linearSearchM #v[1,2,3,4,5,6] 7).eval VecSearch_Nat

#eval (linearSearchM #v[1,2,3,22, 11, 12, 4,5,6] 4).time VecSearch_Nat
#eval (linearSearchM #v[1,2,3,22, 11, 12, 4,5,6] 7).time VecSearch_Nat
#eval (linearSearchM #v[1,2,3,22, 11, 12, 4,5,6] 7).time VecSearch_Cmp

lemma linearSearchM_correct_true [DecidableEq α] (v : Vector α n) :
  ∀ x : α, x ∈ v → (linearSearchM v x).eval VecSearch_Nat = true := by
  intro x x_mem_v
  induction h : v.toArray.toList with
  | nil =>
      simp_all [linearSearchM, eval]
      have v_empty : h ▸ v = #v[] := by
        simp
      have x_not_mem_v : x ∉ v := by
        subst h
        aesop
      tauto
  | cons head tail ih =>
      sorry


lemma linearSearchM_correct_false [DecidableEq α] (v : Vector α n) :
  ∀ x : α, x ∉ v → (linearSearchM v x).eval VecSearch_Nat = false := by
  intro x x_mem_v
  induction h : v.toArray.toList with
  | nil =>
      simp_all [linearSearchM, eval]
  | cons head tail ih =>
      simp_all [linearSearchM]
      sorry

lemma linearSearchM_time_complexity [DecidableEq α] (v : Vector α n) :
  ∀ x : α, (linearSearchM v x).time VecSearch_Nat ≤ n + 1 := by
  intro x
  induction h : v.toArray.toList with
  | nil =>
      simp_all [linearSearchM, time, PureCosts.pureCost]
  | cons head tail ih =>
      simp_all [linearSearchM, VecSearch_Nat]
      sorry


end VectorLinearSearch

section ListLinearSearch
inductive ListSearch (α : Type) : Type → Type  where
  | compare (a : List α) (val : α) : ListSearch α Bool


def ListSearch_Nat [DecidableEq α] : Model (ListSearch α) ℕ where
  evalQuery q :=
    match q with
    | .compare l x => l.head? = some x
  cost q :=
    match q with
    | .compare _ _ => 1


def ListSearch_Cmp [DecidableEq α] : Model (ListSearch α) CmpCount where
  evalQuery q :=
    match q with
    | .compare l x =>  l.head? == some x
  cost q :=
    match q with
    | .compare _ _ => ⟨1,0⟩

open ListSearch in
def listLinearSearch (l : List α) (x : α) : Prog (ListSearch α) Bool := do
  match l with
  | [] => return false
  | l :: ls =>
      let cmp : Bool ← compare (l :: ls) x
      if cmp then
        return true
      else
        listLinearSearch ls x

lemma listLinearSearchM_correct_true [iDec : DecidableEq α] (l : List α) :
  ∀ x : α, x ∈ l → (listLinearSearch l x).eval ListSearch_Nat = true := by
  intro x x_mem_l
  induction l with
  | nil =>
      simp_all only [List.not_mem_nil]
  | cons head tail ih =>
      simp_all only [List.mem_cons, listLinearSearch, bind, FreeM.lift_def, pure,
        FreeM.liftBind_bind, FreeM.pure_bind, eval]
      split_ifs with h
      · simp [eval]
      · obtain (x_head | xtail) := x_mem_l
        · rw [x_head] at h
          simp[ListSearch_Nat] at h
        · specialize ih xtail
          exact ih

lemma listLinearSearchM_correct_false [DecidableEq α] (l : List α) :
  ∀ x : α, x ∉ l → (listLinearSearch l x).eval ListSearch_Nat = false := by
  intro x x_mem_l
  induction l with
  | nil =>
      simp_all [listLinearSearch, eval]
  | cons head tail ih =>
      simp only [List.mem_cons, not_or] at x_mem_l
      specialize ih x_mem_l.2
      simp only [listLinearSearch, bind, FreeM.lift_def, pure, FreeM.liftBind_bind, FreeM.pure_bind,
        eval]
      split_ifs with h_eq
      · simp [ListSearch_Nat] at h_eq
        exfalso
        exact x_mem_l.1 h_eq.symm
      · exact ih



lemma listLinearSearchM_time_complexity_upper_bound [DecidableEq α] (l : List α) :
  ∀ x : α, (listLinearSearch l x).time ListSearch_Nat ≤ 1 + l.length := by
  intro x
  induction l with
  | nil =>
      simp_all [listLinearSearch, ListSearch_Nat, time, PureCosts.pureCost]
  | cons head tail ih =>
      simp_all [listLinearSearch, ListSearch_Nat, time]
      split_ifs with h_head
      · simp [time, PureCosts.pureCost]
      · grind

lemma listLinearSearchM_time_complexity_lower_bound [DecidableEq α] [inon : Nontrivial α] :
  ∃ l : List α, ∃ x : α, (listLinearSearch l x).time ListSearch_Nat = 1 + l.length := by
  obtain ⟨x, y, x_neq_y⟩ := inon
  use [x,x,x,x,x,y], y
  simp_all [time, ListSearch_Nat, listLinearSearch, PureCosts.pureCost]


end ListLinearSearch

end ProgExamples

end Prog

end Algorithms

end Cslib
