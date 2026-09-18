/-
Copyright (c) 2026 Vignesh Karri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vignesh Karri
-/

module

public import Cslib.Computability.QueryComplexity.Measures
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Decision trees and decision tree complexity

A decision tree over `n` variables queries one coordinate at a time and branches on the answer,
until it reaches a leaf holding an output bit. It computes `f : BoolFunc n` when every input
reaches a leaf labelled `f x`.

`D(f)`, the decision tree complexity, is the least depth of a tree computing `f`. This file
proves `C(f) ≤ D(f)`: the set of queries made when evaluating an input forms a certificate for
that input. Together with `Measures.lean` that gives the chain

`s(f) ≤ bs(f) ≤ C(f) ≤ D(f) ≤ n`.

## Main definitions

- `DecisionTree`: a decision tree over `n` Boolean variables.
- `DecisionTree.Computes`: when a tree computes a given Boolean function.
- `DecisionTree.depth`, `DecisionTree.cost`: worst-case and per-input query counts.
- `DecisionTree.complexity`: `D(f)`, the least depth of a tree computing `f`.
- `DecisionTree.path`: the partial assignment recording the queries made on an input.

## Main results

- `DecisionTree.complexity_le_card`: `D(f) ≤ n`.
- `DecisionTree.certificateComplexity_le_complexity`: `C(f) ≤ D(f)`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak2009],
  Section 12.1 (Decision trees and decision tree complexity) and Section 12.2
  (Certificate Complexity).
* [H. Buhrman, R. de Wolf, *Complexity measures and decision tree complexity:
  a survey*][BuhrmanDeWolf2002]
-/

@[expose] public section

namespace Cslib.QueryComplexity

variable {n : ℕ}

/-! ## Decision trees -/

/-- A decision tree over `n` Boolean variables: either a leaf holding the output
bit, or a node querying one coordinate. The left child is taken when the answer is
`false`, the right child when it is `true`. Nothing forbids querying the same
coordinate twice on a route. -/
inductive DecisionTree (n : Nat) where
  | leaf (output : Bool) : DecisionTree n
  | node (i : Fin n) : DecisionTree n → DecisionTree n → DecisionTree n

namespace DecisionTree

/-! ## Evaluation -/

/-- Runs the input `x` through the decision tree and outputs the value at the leaf.
The left child is the `false` branch, the right child the `true` branch. -/
def eval : DecisionTree n → Cube n → Bool
  | .leaf b, _ => b
  | .node i l r, x => if x i then r.eval x else l.eval x

/-- Decision Tree t computes f if for all inputs evaluating x on t gives the
correct function value. -/
def Computes (t : DecisionTree n) (f : BoolFunc n) : Prop :=
  ∀ x, t.eval x = f x

instance instDecidableComputes (t : DecisionTree n) (f : BoolFunc n) :
    Decidable (t.Computes f) := inferInstanceAs (Decidable (∀ x, t.eval x = f x))

/-- The depth of a tree: the number of queries on its longest root-to-leaf
path. A leaf queries nothing, so it has depth `0`. -/
def depth : DecisionTree n → ℕ
  | .leaf _ => 0
  | .node _ l r => max l.depth r.depth + 1

/-- A leaf asks nothing. -/
@[simp]
lemma depth_leaf (b : Bool) : (leaf b : DecisionTree n).depth = 0 := rfl

/-- A node costs one query above its deeper child. -/
@[simp]
lemma depth_node (i : Fin n) (l r : DecisionTree n) :
    (node i l r).depth = max l.depth r.depth + 1 := rfl

/-! ## Paths

The queries and answers along the route an input takes, as an `Assignment n`.
This is used later when we prove that the path an input takes from route to
leaf if a valid certificate for it.
-/

/-- The cost of running `t` on `x`: the number of queries actually made, i.e.
the length of the single root-to-leaf path that `x` follows. Always at most
`depth`, with equality when `x` takes a longest path. -/
def cost : DecisionTree n → Cube n → ℕ
  | .leaf _, _ => 0
  | .node i l r, x => (if x i then r.cost x else l.cost x) + 1

/-- A leaf asks nothing, whatever the input. -/
@[simp]
lemma cost_leaf (b : Bool) (x : Cube n) : (leaf b : DecisionTree n).cost x = 0 := rfl

/-- A node charges one query, then continues into the child `x` selects. -/
@[simp]
lemma cost_node (i : Fin n) (l r : DecisionTree n) (x : Cube n) :
    (node i l r).cost x = (if x i then r.cost x else l.cost x) + 1 := rfl

/-- The route one input takes is no longer than the longest route in the tree. -/
theorem cost_le_depth (t : DecisionTree n) (x : Cube n) : cost t x ≤ depth t := by
  induction t with
  | leaf out => simp
  | node i l r l_ih r_ih =>
    by_cases h : x i
    · -- `x i` is true, so both `cost` and `eval` descend the RIGHT child
      simp only [cost_node, h, ↓reduceIte, depth_node, add_le_add_iff_right, le_sup_iff]
      exact Or.inr r_ih
    · simp_all

/-! ## The brute-force tree

Every `f` is computed by some tree: one that queries every coordinate and
then reads off the answer. This proves the set in the `complexity` definition is nonempty.
-/

/-- Query each coordinate of `is` in turn, then answer `f` on the accumulated
input. `acc` records the answers so far; coordinates not yet queried keep whatever
value `acc` came in with. The recursion is on the list rather than on `n`, which
keeps every subtree over the same coordinate type. -/
def bruteForce (f : BoolFunc n) : List (Fin n) → Cube n → DecisionTree n
  | [], acc => .leaf (f acc)
  | i :: is, acc =>
    .node i (bruteForce f is (Function.update acc i false))
    (bruteForce f is (Function.update acc i true))

/-- The tree asks exactly one question per coordinate of `is`. -/
theorem depth_bruteForce (is : List (Fin n)) (acc : Cube n) (f : BoolFunc n) :
    (bruteForce f is acc).depth = is.length := by
  induction is generalizing acc with
  | nil => simp [bruteForce]
  | cons head tail tail_ih =>
    simp [bruteForce, tail_ih]

/-- Correctness, in the generalised form the induction needs. -/
theorem eval_bruteForce (is : List (Fin n)) (acc : Cube n) (f : BoolFunc n) (x : Cube n)
    (h : ∀ j, j ∉ is → x j = acc j) : (bruteForce f is acc).eval x = f x := by
  induction is generalizing acc with
  | nil =>
    -- Nothing left to query, so `h` says `acc` and `x` agree at *every* coordinate.
    have hacc : acc = x := by grind
    simp [bruteForce, eval, hacc]
  | cons i is ih =>
    -- Whichever branch `x` takes, the accumulator now records `x i` correctly, so the
    -- invariant survives and the induction hypothesis applies to that subtree.
    have key : ∀ b : Bool, x i = b →
        (bruteForce f is (Function.update acc i b)).eval x = f x := by
      intro b hb
      refine ih _ fun j hj => ?_
      by_cases hji : j = i
      · -- the coordinate just answered: the update wrote exactly `x i`
        subst hji; simp [hb]
      · -- any other coordinate is untouched, so the old agreement carries over
        rw [Function.update_of_ne hji]
        exact h j (by simp [hji, hj])
    simp only [bruteForce, eval]
    by_cases hxi : x i = true
    · simp [hxi, key true hxi]
    · simp only [Bool.not_eq_true] at hxi
      simp [hxi, key false hxi]

/-- The brute-force tree for `f`: query every coordinate, in the order given by
`List.finRange n`. -/
def fullTree (f : BoolFunc n) : DecisionTree n := bruteForce f (List.finRange n) (fun _ => false)

/-- Every function is computed by some tree. -/
theorem fullTree_computes (f : BoolFunc n) : (fullTree f).Computes f := by
  intro x
  apply eval_bruteForce
  simp

/-- The depth of this brute force tree is `n`. -/
@[simp]
theorem depth_fullTree (f : BoolFunc n) : (fullTree f).depth = n := by
  unfold fullTree
  simp [depth_bruteForce]

/-- `D(f)`: the least depth over all decision trees computing f. -/
noncomputable def complexity (f : BoolFunc n) : ℕ :=
  sInf {k | ∃ t : DecisionTree n, t.Computes f ∧ t.depth = k}

/-- Upper-bound rule for `D(f)`: exhibit a single tree computing `f`. -/
theorem complexity_le_depth {t : DecisionTree n} {f : BoolFunc n} (h : t.Computes f) :
  complexity f ≤ t.depth := by
  apply Nat.sInf_le
  exact ⟨t, h, rfl⟩

/-- The set of achievable depths is non-empty — `fullTree` lives in it. Everything
below needs this; without it `complexity f` could be `sInf ∅ = 0` for all we know. -/
theorem depths_nonempty (f : BoolFunc n) :
    {k | ∃ t : DecisionTree n, t.Computes f ∧ t.depth = k}.Nonempty :=
  ⟨n, fullTree f, fullTree_computes f, depth_fullTree f⟩

/-- `D(f) ≤ n`: querying everything is always an option. -/
theorem complexity_le_card (f : BoolFunc n) : complexity f ≤ n :=
  (complexity_le_depth (fullTree_computes f)).trans_eq (depth_fullTree f)

/-- An optimal tree exists. A non-empty set of naturals attains its infimum
(`Nat.sInf_mem`), so the minimum in `complexity` is realised by an actual tree.
Every argument that begins "take an optimal decision tree for `f`" needs this. -/
theorem exists_computes_depth_eq_complexity (f : BoolFunc n) :
    ∃ t : DecisionTree n, t.Computes f ∧ t.depth = complexity f :=
  Nat.sInf_mem (depths_nonempty f)

/-- Lower-bound rule for `D(f)`: to bound `D(f)` from below, bound the depth of
every tree computing `f`. The counterpart of `complexity_le_depth`. -/
theorem le_complexity {f : BoolFunc n} {k : ℕ}
    (h : ∀ t : DecisionTree n, t.Computes f → k ≤ t.depth) : k ≤ complexity f :=
  le_csInf (depths_nonempty f) fun _ hb => by
    obtain ⟨t, ht, rfl⟩ := hb
    exact h t ht

/-- The path of `x` through `t`is the partial assignment recording every query
made along the route `x` takes, together with the answer given. -/
def path : DecisionTree n → Cube n → Assignment n
  | .leaf _, _ => fun _ => none
  | .node i l r, x =>
    if x i then Function.update (path r x) i (x i) else Function.update (path l x) i (x i)

/-- Everything a path records about `x` is `x`'s own value. Needed before `routing`,
because a coordinate may be queried twice on one route. -/
theorem agrees_path {t : DecisionTree n} {x : Cube n} : Agrees (path t x) x := by
  induction t with
  | leaf _ => simp [Agrees, path]
  | node j l r l_ih r_ih =>
    intro i b hb
    simp only [path] at hb
    rcases eq_or_ne i j with rfl | hij
    · split at hb <;> simpa using hb
    · split at hb
      · exact r_ih i b (by rwa [Function.update_of_ne hij] at hb)
      · exact l_ih i b (by rwa [Function.update_of_ne hij] at hb)

lemma agrees_of_agrees_update {C : Assignment n} {x y : Cube n} {j : Fin n}
    (hC : Agrees C x) (h : Agrees (Function.update C j (some (x j))) y) : Agrees C y := by
  intro k c hk
  rcases eq_or_ne k j with rfl | hkj
  · have hy : y k = x k := h k (x k) (by simp)
    rw [hy, hC k c hk]
  · exact h k c (by rwa [Function.update_of_ne hkj])

/-- The routing lemma. If `y` answers every query the tree asked of `x` the same
way, the tree cannot tell them apart. This is the formal content of "the adversary
answers consistently", and the engine of `C(f) ≤ D(f)`. -/
theorem routing {t : DecisionTree n} {x : Cube n} {y : Cube n} :
    Agrees (path t x) y → t.eval y = t.eval x := by
  induction t with
  | leaf _ => simp [Agrees, path, eval]
  | node j l r l_ih r_ih =>
    intro h
    -- the queried coordinate is recorded, so `y` must answer it exactly as `x` did
    have hj : y j = x j := h j (x j) (by simp only [path]; split <;> simp)
    simp only [path] at h
    -- hence `y` takes the same branch, and the IH handles the subtree
    simp only [eval, hj]
    by_cases hxj : x j = true
    · rw [ite_eq_left hxj] at h
      simp only [ite_eq_left hxj]
      exact r_ih (agrees_of_agrees_update agrees_path h)
    · rw [ite_eq_right hxj] at h
      simp only [ite_eq_right hxj]
      exact l_ih (agrees_of_agrees_update agrees_path h)

/-- Recording one more query enlarges the support by at most one coordinate. -/
lemma support_update_subset (C : Assignment n) (j : Fin n) (b : Bool) :
    support (Function.update C j (some b)) ⊆ insert j (support C) := by
  intro i hi
  rcases eq_or_ne i j with rfl | hij
  · exact Finset.mem_insert_self _ _
  · rw [mem_support, Function.update_of_ne hij] at hi
    exact Finset.mem_insert_of_mem (mem_support.mpr hi)

/-- A path fixes no more coordinates than the tree made queries. The inequality can
be strict: a re-queried coordinate is charged twice but occupies one slot. -/
theorem size_path_le_cost (t : DecisionTree n) (x : Cube n) : size (path t x) ≤ cost t x := by
  induction t with
  | leaf b => simp [path, size, support]
  | node j l r l_ih r_ih =>
    simp only [path, cost]
    by_cases hxj : x j = true
    · simp only [ite_eq_left hxj]
      calc size (Function.update (path r x) j (some (x j)))
          ≤ (insert j (support (path r x))).card :=
            Finset.card_le_card (support_update_subset _ _ _)
        _ ≤ (support (path r x)).card + 1 := Finset.card_insert_le _ _
        _ ≤ cost r x + 1 := Nat.add_le_add_right r_ih 1
    · simp only [ite_eq_right hxj]
      calc size (Function.update (path l x) j (some (x j)))
          ≤ (insert j (support (path l x))).card :=
            Finset.card_le_card (support_update_subset _ _ _)
        _ ≤ (support (path l x)).card + 1 := Finset.card_insert_le _ _
        _ ≤ cost l x + 1 := Nat.add_le_add_right l_ih 1

/-- The path is a certificate. Anything agreeing with the route `x` took reaches
the same leaf (`routing`), so `f` is pinned to `f x` on the whole subcube. -/
theorem path_mem_certificates {f : BoolFunc n} {t : DecisionTree n} (ht : t.Computes f)
    (x : Cube n) : path t x ∈ certificates f x :=
  mem_certificates.mpr ⟨agrees_path, fun y hy => (ht y).symm.trans ((routing hy).trans (ht x))⟩

/-- Pointwise: `C(f, x) ≤ D(f)`, by running the chain
`C(f, x) ≤ size (path t x) ≤ cost t x ≤ depth t` over every tree computing `f`. -/
theorem pointCertificateComplexity_le_complexity (f : BoolFunc n) (x : Cube n) :
    pointCertificateComplexity f x ≤ complexity f := by
  apply le_complexity
  intro t ht
  calc pointCertificateComplexity f x
      ≤ size (path t x) := pointCertificateComplexity_le (path_mem_certificates ht x)
    _ ≤ cost t x := size_path_le_cost t x
    _ ≤ t.depth := cost_le_depth t x

/-- `C(f) ≤ D(f)`. -/
theorem certificateComplexity_le_complexity (f : BoolFunc n) :
    certificateComplexity f ≤ complexity f :=
  Finset.sup_le fun x _ => pointCertificateComplexity_le_complexity f x

end DecisionTree

end Cslib.QueryComplexity
