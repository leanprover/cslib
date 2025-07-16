/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
import Mathlib.Logic.Relation
import Cslib.Utils.Relation

/-!
# SKI Combinatory Logic

This file defines the syntax and operational semantics (reduction rules) of combinatory logic,
using the SKI basis.

## Main definitions

- `SKI`: the type of expressions in the SKI calculus,
- `Red`: single-step reduction of SKI expressions,
- `MRed`: multi-step reduction of SKI expressions,
- `CommonReduct`: the relation between terms having a common reduct,

## Notation

- `⬝` : application between SKI terms,
- `⇒` : single-step reduction,
- `⇒*` : multi-step reduction,

## References

The setup of SKI combinatory logic is standard, see for example:
- <https://en.m.wikipedia.org/wiki/SKI_combinator_calculus>
- <https://en.m.wikipedia.org/wiki/Combinatory_logic>
-/

/-- An SKI expression is built from the primitive combinators `S`, `K` and `I`, and application. -/
inductive SKI where
  /-- `S`-combinator, with semantics $λxyz.xz(yz) -/
  | S
  /-- `K`-combinator, with semantics $λxy.x$ -/
  | K
  /-- `I`-combinator, with semantics $λx.x$ -/
  | I
  /-- Application $x y ↦ xy$ -/
  | app : SKI → SKI → SKI
deriving Repr, DecidableEq

namespace SKI

@[inherit_doc]
scoped infixl:100 " ⬝ " => app

/-- Apply a term to a list of terms -/
def applyList (f : SKI) (xs : List SKI) : SKI := List.foldl (. ⬝ .) f xs

lemma applyList_concat (f : SKI) (ys : List SKI) (z : SKI) :
    f.applyList (ys ++ [z]) = f.applyList ys ⬝ z := by
  simp [applyList]


/-! ### Reduction relations between SKI terms -/

/-- Single-step reduction of SKI terms -/
inductive Red : SKI → SKI → Prop where
  /-- The operational semantics of the `S`, -/
  | red_S (x y z : SKI) : Red (S ⬝ x ⬝ y ⬝ z) (x ⬝ z ⬝ (y ⬝ z))
  /-- `K`, -/
  | red_K (x y : SKI) : Red (K ⬝ x ⬝ y) x
  /-- and `I` combinators. -/
  | red_I (x : SKI) : Red (I ⬝ x) x
  /-- Reduction on the head -/
  | red_head (x x' y : SKI) (_ : Red x x') : Red (x ⬝ y) (x' ⬝ y)
  /-- and tail of an SKI term. -/
  | red_tail (x y y' : SKI) (_ : Red y y') : Red (x ⬝ y) (x ⬝ y')

/-- Notation for single-step reduction -/
scoped infix:90 " ⇒ " => Red

/-- Multi-step reduction of SKI terms -/
def MRed : SKI → SKI → Prop := Relation.ReflTransGen Red

/-- Notation for multi-step reduction (by analogy with the Kleene star) -/
scoped infix:90 " ⇒* " => MRed

open Red

@[refl]
theorem MRed.refl (a : SKI) : a ⇒* a := Relation.ReflTransGen.refl

theorem MRed.single {a b : SKI} (h : a ⇒ b) : a ⇒* b := Relation.ReflTransGen.single h

theorem MRed.S (x y z : SKI) : MRed (S ⬝ x ⬝ y ⬝ z) (x ⬝ z ⬝ (y ⬝ z)) := MRed.single <| red_S ..
theorem MRed.K (x y : SKI) : MRed (K ⬝ x ⬝ y) x := MRed.single <| red_K ..
theorem MRed.I (x : SKI) : MRed (I ⬝ x) x := MRed.single <| red_I ..

theorem MRed.head {a a' : SKI} (b : SKI) (h : a ⇒* a') : (a ⬝ b) ⇒* (a' ⬝ b) := by
  induction h with
  | refl => apply MRed.refl
  | @tail a' a'' _ ha'' ih =>
    apply Relation.ReflTransGen.tail (b := a' ⬝ b) ih
    exact Red.red_head a' a'' b ha''

theorem MRed.tail (a : SKI) {b b' : SKI} (h : b ⇒* b') : (a ⬝ b) ⇒* (a ⬝ b') := by
  induction h with
  | refl => apply MRed.refl
  | @tail b' b'' _ hb'' ih =>
    apply Relation.ReflTransGen.tail (b := a ⬝ b') ih
    exact Red.red_tail a b' b'' hb''

instance MRed.instTrans : IsTrans SKI MRed := Relation.instIsTransReflTransGen
theorem MRed.transitive : Transitive MRed := transitive_of_trans MRed

instance MRed.instIsRefl : IsRefl SKI MRed := Relation.instIsReflReflTransGen
theorem MRed.reflexive : Reflexive MRed := IsRefl.reflexive

instance MRedTrans : Trans Red MRed MRed :=
  ⟨fun hab => Relation.ReflTransGen.trans (MRed.single hab)⟩

instance MRedRedTrans : Trans MRed Red MRed :=
  ⟨fun hab hbc => Relation.ReflTransGen.trans hab (MRed.single hbc)⟩

instance RedMRedTrans : Trans Red Red MRed :=
  ⟨fun hab hbc => Relation.ReflTransGen.trans (MRed.single hab) (MRed.single hbc)⟩

lemma parallel_mRed {a a' b b' : SKI} (ha : a ⇒* a') (hb : b ⇒* b') :
    (a ⬝ b) ⇒* (a' ⬝ b') :=
  Trans.simple (MRed.head b ha) (MRed.tail a' hb)

lemma parallel_red {a a' b b' : SKI} (ha : a ⇒ a') (hb : b ⇒ b') : (a ⬝ b) ⇒* (a' ⬝ b') := by
  trans a' ⬝ b
  all_goals apply MRed.single
  · exact Red.red_head a a' b ha
  · exact Red.red_tail a' b b' hb


/-- Express that two terms have a reduce to a common term. -/
def CommonReduct : SKI → SKI → Prop := Relation.Join MRed

lemma commonReduct_of_single {a b : SKI} (h : a ⇒* b) : CommonReduct a b := by
  refine Relation.join_of_single MRed.reflexive h

theorem symmetric_commonReduct : Symmetric CommonReduct := Relation.symmetric_join
theorem reflexive_commonReduct : Reflexive CommonReduct :=
  Relation.reflexive_join MRed.reflexive
