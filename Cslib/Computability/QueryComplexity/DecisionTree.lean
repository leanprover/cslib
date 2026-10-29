/-
Copyright (c) 2026 Vignesh Karri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vignesh Karri, Samuel Schlesinger
-/

module

public import Cslib.Computability.QueryComplexity.Measures
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Decision trees and decision tree complexity

A decision tree over `n` variables queries one coordinate at a time and branches on the answer,
until it reaches a leaf holding an output bit. It computes `f : BooleanFunction n` when every input
`x` reaches a leaf labelled `f x`.

`D(f)`, the decision tree complexity, is the least depth of a tree computing `f`. This file
proves `C(f) ≤ D(f)`: the set of queries made when evaluating an input forms a certificate for
that input. Together with `Measures.lean` that gives the chain

`s(f) ≤ bs(f) ≤ C(f) ≤ D(f) ≤ n`.

## Main definitions

- `DecisionTree n`: a decision tree over `n` Boolean variables.
- `DecisionTree.Computes`: when a tree computes a given Boolean function.
- `DecisionTree.depth`: the number of queries in the worst case.
- `DecisionTree.complexity`: `D(f)`, the least depth of a tree computing `f`.
- `DecisionTree.queries`: the coordinates queried on an input.

## Main results

- `DecisionTree.complexity_le_card`: `D(f) ≤ n`.
- `DecisionTree.certificateComplexity_le_complexity`: `C(f) ≤ D(f)`.
- `DecisionTree.complexity_eq_card_of_sensitivityAt_eq_card`: an input sensitive to every
  coordinate forces `D(f) = n`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09],
  Section 12.1 (Decision trees and decision tree complexity) and Section 12.2
  (Certificate Complexity).
* [H. Buhrman, R. de Wolf, *Complexity measures and decision tree complexity:
  a survey*][BuhrmanDeWolf2002]
-/

@[expose] public section

namespace Cslib.QueryComplexity

open BitString

variable {n : ℕ}

/-! ## Decision trees -/

/-- A decision tree over `n` Boolean variables: either a leaf holding the output
bit, or a node querying one coordinate. The left child is taken when the answer is
`false`, the right child when it is `true`. -/
inductive DecisionTree (n : ℕ) where
  | leaf (output : Bool) : DecisionTree n
  | node (i : Fin n) : DecisionTree n → DecisionTree n → DecisionTree n

namespace DecisionTree

/-! ## Evaluation -/

/-- Runs the input `x` through the decision tree and outputs the value at the leaf.
The left child is the `false` branch, the right child the `true` branch. -/
def eval : DecisionTree n → BitString n → Bool
  | .leaf b, _ => b
  | .node i l r, x => if x i then r.eval x else l.eval x

@[simp]
lemma eval_leaf (b : Bool) (x : BitString n) : (leaf b : DecisionTree n).eval x = b := rfl

@[simp]
lemma eval_node (i : Fin n) (l r : DecisionTree n) (x : BitString n) :
    (node i l r).eval x = if x i then r.eval x else l.eval x := rfl

/-- A tree computes `f` when it outputs `f x` on every input `x`. -/
def Computes (t : DecisionTree n) (f : BooleanFunction n) : Prop :=
  ∀ x, t.eval x = f x

instance instDecidableComputes (t : DecisionTree n) (f : BooleanFunction n) :
    Decidable (t.Computes f) := inferInstanceAs (Decidable (∀ x, t.eval x = f x))

/-- The depth of a tree: the number of queries on its longest root-to-leaf
path. A leaf queries nothing, so it has depth `0`. -/
def depth : DecisionTree n → ℕ
  | .leaf _ => 0
  | .node _ l r => max l.depth r.depth + 1

@[simp]
lemma depth_leaf (b : Bool) : (leaf b : DecisionTree n).depth = 0 := rfl

/-- A node costs one query above its deeper child. -/
@[simp]
lemma depth_node (i : Fin n) (l r : DecisionTree n) :
    (node i l r).depth = max l.depth r.depth + 1 := rfl

/-! ## Querying a list of coordinates

`graft is k acc` queries the coordinates of `is` in turn, recording the answers in `acc`, and then
continues with the tree `k acc'` for the assignment `acc'` reached. With leaves as continuations
this is the tree that queries every coordinate and reads off `f`, so every function has a tree of
depth `n`. Other continuations give trees that query a certificate and then continue with a tree
for the restricted function.
-/

/-- Query the coordinates of `is` in turn, starting from the assignment `acc`, then continue with
the tree `k acc'` for the assignment `acc'` reached. -/
def graft : List (Fin n) → (BitString n → DecisionTree n) → BitString n → DecisionTree n
  | [], k, acc => k acc
  | i :: is, k, acc =>
    .node i (graft is k (Function.update acc i false)) (graft is k (Function.update acc i true))

@[simp]
lemma graft_nil (k : BitString n → DecisionTree n) (acc : BitString n) : graft [] k acc = k acc :=
  rfl

@[simp]
lemma graft_cons (i : Fin n) (is : List (Fin n)) (k : BitString n → DecisionTree n)
    (acc : BitString n) :
    graft (i :: is) k acc =
      .node i (graft is k (Function.update acc i false))
        (graft is k (Function.update acc i true)) :=
  rfl

/-- Running the grafted tree on `x` runs the continuation at the assignment taking `x` on `is`
and `acc` elsewhere. -/
theorem eval_graft (is : List (Fin n)) (k : BitString n → DecisionTree n) (acc x : BitString n) :
    (graft is k acc).eval x = (k fun j => if j ∈ is then x j else acc j).eval x := by
  induction is generalizing acc with
  | nil => simp
  | cons i is ih =>
    have : (graft (i :: is) k acc).eval x = (graft is k (Function.update acc i (x i))).eval x := by
      cases hx : x i <;> simp [hx]
    rw [this, ih]
    congr 2
    funext j
    by_cases hj : j ∈ is
    · simp [hj]
    · by_cases hji : j = i
      · subst hji; simp
      · simp [hj, hji]

/-- Grafting adds at most the number of queried coordinates to the depth. -/
theorem depth_graft_le (is : List (Fin n)) (k : BitString n → DecisionTree n) (acc : BitString n)
    {d : ℕ} (hk : ∀ b, (k b).depth ≤ d) : (graft is k acc).depth ≤ is.length + d := by
  induction is generalizing acc with
  | nil => simpa using hk acc
  | cons i is ih =>
    simp only [graft_cons, depth_node, List.length_cons]
    have := ih (Function.update acc i false)
    have := ih (Function.update acc i true)
    omega

/-- Query the coordinates of `is` in turn, then output `f` of the assignment reached. -/
def queryAll (f : BooleanFunction n) (is : List (Fin n)) (acc : BitString n) : DecisionTree n :=
  graft is (fun b => .leaf (f b)) acc

/-- Running `queryAll` on `x` outputs `f` at the assignment taking `x` on `is` and `acc`
elsewhere. -/
theorem eval_queryAll (f : BooleanFunction n) (is : List (Fin n)) (acc x : BitString n) :
    (queryAll f is acc).eval x = f fun j => if j ∈ is then x j else acc j :=
  eval_graft is _ acc x

/-- `queryAll` makes at most one query per entry of `is`. -/
theorem depth_queryAll_le (f : BooleanFunction n) (is : List (Fin n)) (acc : BitString n) :
    (queryAll f is acc).depth ≤ is.length := by
  simpa [queryAll] using depth_graft_le is (fun b => .leaf (f b)) acc (d := 0) fun _ => le_rfl

/-- The tree querying every coordinate, in the order of `List.finRange n`, and reading off `f`. -/
def fullTree (f : BooleanFunction n) : DecisionTree n :=
  queryAll f (List.finRange n) (fun _ => false)

/-- Every function is computed by some tree. -/
theorem fullTree_computes (f : BooleanFunction n) : (fullTree f).Computes f := fun x => by
  simp [fullTree, eval_queryAll]

/-- Querying every coordinate takes `n` queries. -/
theorem depth_fullTree_le (f : BooleanFunction n) : (fullTree f).depth ≤ n :=
  (depth_queryAll_le f _ _).trans_eq (List.length_finRange ..)

/-- `D(f)`: the least depth of a decision tree computing `f`. -/
noncomputable def complexity (f : BooleanFunction n) : ℕ :=
  sInf {d | ∃ t : DecisionTree n, t.Computes f ∧ t.depth ≤ d}

/-- Upper-bound rule for `D(f)`: exhibit one tree. -/
theorem complexity_le_depth {t : DecisionTree n} {f : BooleanFunction n} (h : t.Computes f) :
    complexity f ≤ t.depth :=
  Nat.sInf_le ⟨t, h, le_rfl⟩

/-- `D(f) ≤ n`: querying every coordinate is always an option. -/
theorem complexity_le_card (f : BooleanFunction n) : complexity f ≤ n :=
  (complexity_le_depth (fullTree_computes f)).trans (depth_fullTree_le f)

/-- Some tree computing `f` has depth exactly `D(f)`. -/
theorem exists_computes_depth_eq_complexity (f : BooleanFunction n) :
    ∃ t : DecisionTree n, t.Computes f ∧ t.depth = complexity f := by
  obtain ⟨t, ht, hd⟩ :=
    Nat.sInf_mem (s := {d | ∃ t : DecisionTree n, t.Computes f ∧ t.depth ≤ d})
      ⟨_, fullTree f, fullTree_computes f, le_rfl⟩
  exact ⟨t, ht, le_antisymm hd (complexity_le_depth ht)⟩

/-- `D(f) ≤ d` if and only if some tree of depth at most `d` computes `f`. -/
theorem complexity_le_iff {f : BooleanFunction n} {d : ℕ} :
    complexity f ≤ d ↔ ∃ t : DecisionTree n, t.Computes f ∧ t.depth ≤ d := by
  refine ⟨fun h => ?_, fun ⟨_, ht, hd⟩ => (complexity_le_depth ht).trans hd⟩
  obtain ⟨t, ht, hd⟩ := exists_computes_depth_eq_complexity f
  exact ⟨t, ht, hd.trans_le h⟩

/-- Lower-bound rule for `D(f)`: a bound that holds for every tree computing `f`. -/
theorem le_complexity_iff {f : BooleanFunction n} {d : ℕ} :
    d ≤ complexity f ↔ ∀ t : DecisionTree n, t.Computes f → d ≤ t.depth := by
  refine ⟨fun h t ht => h.trans (complexity_le_depth ht), fun h => ?_⟩
  obtain ⟨t, ht, hd⟩ := exists_computes_depth_eq_complexity f
  exact (h t ht).trans hd.le

/-- Only constant functions are computed without any query. -/
theorem complexity_eq_zero_iff {f : BooleanFunction n} :
    complexity f = 0 ↔ ∀ x y, f x = f y := by
  constructor
  · intro h
    obtain ⟨t, ht, hd⟩ := exists_computes_depth_eq_complexity f
    cases t with
    | leaf b => exact fun x y => (ht x).symm.trans (ht y)
    | node i l r => simp [h] at hd
  · intro h
    exact Nat.le_zero.1 (complexity_le_depth (t := .leaf (f fun _ => false)) fun x => h _ x)

/-! ## Queries

The coordinates queried along the route an input takes. Inputs agreeing with `x` on them follow
the same route, so they form a certificate for `x`.
-/

/-- The coordinates queried on the route `x` takes through `t`. -/
def queries : DecisionTree n → BitString n → Finset (Fin n)
  | .leaf _, _ => ∅
  | .node i l r, x => insert i (if x i then r.queries x else l.queries x)

@[simp]
lemma queries_leaf (b : Bool) (x : BitString n) : (leaf b : DecisionTree n).queries x = ∅ := rfl

@[simp]
lemma queries_node (i : Fin n) (l r : DecisionTree n) (x : BitString n) :
    (node i l r).queries x = insert i (if x i then r.queries x else l.queries x) := rfl

/-- At most `depth t` coordinates are queried on any input. -/
theorem card_queries_le_depth (t : DecisionTree n) (x : BitString n) :
    (t.queries x).card ≤ t.depth := by
  induction t with
  | leaf _ => simp
  | node i l r ihl ihr =>
    refine (Finset.card_insert_le _ _).trans ?_
    rw [depth_node]
    split
    · exact Nat.add_le_add_right (ihr.trans (le_max_right _ _)) 1
    · exact Nat.add_le_add_right (ihl.trans (le_max_left _ _)) 1

/-- Inputs agreeing with `x` on the coordinates queried for `x` reach the same leaf. -/
theorem eval_eq_of_forall_mem_queries (t : DecisionTree n) {x y : BitString n}
    (h : ∀ i ∈ t.queries x, y i = x i) : t.eval y = t.eval x := by
  induction t with
  | leaf _ => rfl
  | node i l r ihl ihr =>
    simp only [queries_node, Finset.mem_insert, forall_eq_or_imp] at h
    obtain ⟨hi, h⟩ := h
    simp only [eval, hi]
    split_ifs at h ⊢
    · exact ihr h
    · exact ihl h

/-- The queries made on `x` by a tree computing `f` are a certificate for `x`. -/
theorem isCertificate_queries {f : BooleanFunction n} {t : DecisionTree n} (ht : t.Computes f)
    (x : BitString n) : IsCertificate f x (t.queries x) :=
  fun y hy => (ht y).symm.trans ((t.eval_eq_of_forall_mem_queries hy).trans (ht x))

/-- Pointwise: `C(f, x) ≤ D(f)`. The queries made on `x` certify it, and a tree of depth `d`
makes at most `d` of them. -/
theorem certificateComplexityAt_le_complexity (f : BooleanFunction n) (x : BitString n) :
    certificateComplexityAt f x ≤ complexity f :=
  le_complexity_iff.2 fun t ht =>
    (certificateComplexityAt_le (isCertificate_queries ht x)).trans (t.card_queries_le_depth x)

/-- `C(f) ≤ D(f)`. -/
theorem certificateComplexity_le_complexity (f : BooleanFunction n) :
    certificateComplexity f ≤ complexity f :=
  Finset.sup_le fun x _ => certificateComplexityAt_le_complexity f x

/-- The whole chain at one input: `s(f, x) ≤ D(f)`. -/
theorem sensitivityAt_le_complexity (f : BooleanFunction n) (x : BitString n) :
    sensitivityAt f x ≤ complexity f :=
  (sensitivityAt_le_sensitivity f x).trans <| (sensitivity_le_blockSensitivity f).trans <|
    (blockSensitivity_le_certificateComplexity f).trans (certificateComplexity_le_complexity f)

/-- A function sensitive to every coordinate at some input needs to query all of them. -/
theorem complexity_eq_card_of_sensitivityAt_eq_card {f : BooleanFunction n} {x : BitString n}
    (h : sensitivityAt f x = n) : complexity f = n :=
  le_antisymm (complexity_le_card f) (h.symm.trans_le (sensitivityAt_le_complexity f x))

end DecisionTree

end Cslib.QueryComplexity
