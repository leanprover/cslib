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
- `ReductionStep`: single-step reduction of SKI expressions,
- `LargeReduction`: multi-step reduction of SKI expressions,
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
  | ap : SKI → SKI → SKI
deriving Repr, DecidableEq

namespace SKI

/-- Notation for application between SKI terms -/
infixl:100 " ⬝ " => ap

/-- Apply a term to a list of terms -/
def applyList (f : SKI) (xs : List SKI) : SKI := List.foldl (. ⬝ .) f xs

lemma applyList_concat (f : SKI) (ys : List SKI) (z : SKI) :
    f.applyList (ys ++ [z]) = f.applyList ys ⬝ z := by
  simp [applyList]


/-! ### Reduction relations between SKI terms -/

/-- Single-step reduction of SKI terms -/
inductive ReductionStep : SKI → SKI → Prop where
  /-- The operational semantics of the `S`, -/
  | red_S (x y z : SKI) : ReductionStep (S ⬝ x ⬝ y ⬝ z) (x ⬝ z ⬝ (y ⬝ z))
  /-- `K`, -/
  | red_K (x y : SKI) : ReductionStep (K ⬝ x ⬝ y) x
  /-- and `I` combinators. -/
  | red_I (x : SKI) : ReductionStep (I ⬝ x) x
  /-- Reduction on the head -/
  | red_head (x x' y : SKI) (_ : ReductionStep x x') : ReductionStep (x ⬝ y) (x' ⬝ y)
  /-- and tail of an SKI term. -/
  | red_tail (x y y' : SKI) (_ : ReductionStep y y') : ReductionStep (x ⬝ y) (x ⬝ y')

/-- Notation for single-step reduction -/
infix:90 " ⇒ " => ReductionStep

/-- Multi-step reduction of SKI terms -/
def LargeReduction : SKI → SKI → Prop := Relation.ReflTransGen ReductionStep

/-- Notation for multi-step reduction (by analogy with the Kleene star) -/
infix:90 " ⇒* " => LargeReduction

open ReductionStep

theorem largeRed_refl (a : SKI) : a ⇒* a := Relation.ReflTransGen.refl

theorem largeRed_single (a b : SKI) (h : a ⇒ b) : a ⇒* b := Relation.ReflTransGen.single h

theorem largeRed_S (x y z : SKI) : LargeReduction (S ⬝ x ⬝ y ⬝ z) (x ⬝ z ⬝ (y ⬝ z)) :=
  largeRed_single _ _ <| red_S _ _ _

theorem largeRed_K (x y : SKI) : LargeReduction (K ⬝ x ⬝ y) x :=
  largeRed_single _ _ <| red_K _ _

theorem largeRed_I (x : SKI) : LargeReduction (I ⬝ x) x :=
  largeRed_single _ _ <| red_I _

theorem largeRed_head (a a' b : SKI) (h : a ⇒* a') : (a ⬝ b) ⇒* (a' ⬝ b) := by
  induction h with
  | refl => apply largeRed_refl
  | @tail a' a'' _ ha'' ih =>
    apply Relation.ReflTransGen.tail (b := a' ⬝ b) ih
    exact ReductionStep.red_head a' a'' b ha''

theorem largeRed_tail (a b b' : SKI) (h : b ⇒* b') : (a ⬝ b) ⇒* (a ⬝ b') := by
  induction h with
  | refl => apply largeRed_refl
  | @tail b' b'' _ hb'' ih =>
    apply Relation.ReflTransGen.tail (b := a ⬝ b') ih
    exact ReductionStep.red_tail a b' b'' hb''

instance LargeReduction.instTrans : IsTrans SKI LargeReduction := Relation.instIsTransReflTransGen
theorem largeReduction_transitive : Transitive LargeReduction := transitive_of_trans LargeReduction

instance LargeReduction.instIsRefl : IsRefl SKI LargeReduction := Relation.instIsReflReflTransGen
theorem largeReduction_reflexive : Reflexive LargeReduction := IsRefl.reflexive

instance reductionStepLargeReductionTrans :
    Trans ReductionStep LargeReduction LargeReduction := by
  constructor
  intro a b c hab hbc
  replace hab := largeRed_single _ _ hab
  exact Relation.ReflTransGen.trans hab hbc

instance largeReductionReductionStepTrans :
    Trans LargeReduction ReductionStep LargeReduction := by
  constructor
  intro a b c hab hbc
  replace hbc := largeRed_single _ _ hbc
  exact Relation.ReflTransGen.trans hab hbc

instance reductionStepTeductionStepTrans :
    Trans ReductionStep ReductionStep LargeReduction := by
  constructor
  intro a b c hab hbc
  replace hab := largeRed_single _ _ hab
  replace hbc := largeRed_single _ _ hbc
  exact Relation.ReflTransGen.trans hab hbc

lemma parallel_large_reduction (a a' b b' : SKI) (ha : a ⇒* a') (hb : b ⇒* b') :
    (a ⬝ b) ⇒* (a' ⬝ b') := by
  trans a' ⬝ b
  . exact largeRed_head a a' b ha
  . exact largeRed_tail a' b b' hb

lemma parallel_reduction (a a' b b' : SKI) (ha : a ⇒ a') (hb : b ⇒ b') : (a ⬝ b) ⇒* (a' ⬝ b') := by
  trans a' ⬝ b
  all_goals apply largeRed_single
  . exact ReductionStep.red_head a a' b ha
  . exact ReductionStep.red_tail a' b b' hb


/-- Express that two terms have a reduce to a common term. -/
def CommonReduct : SKI → SKI → Prop := Relation.Join LargeReduction

lemma commonReduct_of_single (a b : SKI) (h : a ⇒* b) : CommonReduct a b := by
  refine Relation.join_of_single largeReduction_reflexive h

theorem symmetric_join : Symmetric CommonReduct := Relation.symmetric_join
theorem reflexive_join : Reflexive CommonReduct :=
  Relation.reflexive_join largeReduction_reflexive
