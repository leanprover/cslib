/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public meta import Cslib.Foundations.Data.Relation

@[expose] public section

/-!
# SKI Combinatory Logic

This file defines the syntax and operational semantics (reduction rules) of combinatory logic,
using the SKI basis.

## Main definitions

- `SKI`: the type of expressions in the SKI calculus,
- `Red`: single-step reduction of SKI expressions,
- `MRed`: multi-step reduction of SKI expressions.

## Notation

- `⬝` : application between SKI terms,
- `⭢` : single-step reduction,
- `↠` : multi-step reduction,

## References

The setup of SKI combinatory logic is standard, see for example:
- <https://en.m.wikipedia.org/wiki/SKI_combinator_calculus>
- <https://en.m.wikipedia.org/wiki/Combinatory_logic>
-/

namespace Cslib

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
def applyList (f : SKI) (xs : List SKI) : SKI := List.foldl (· ⬝ ·) f xs

lemma applyList_concat (f : SKI) (ys : List SKI) (z : SKI) :
    f.applyList (ys ++ [z]) = f.applyList ys ⬝ z := by
  simp [applyList]

/-- The size of an SKI term is its number of combinators. -/
def size : SKI → Nat
  | S => 1
  | K => 1
  | I => 1
  | x ⬝ y => size x + size y

/-! ### Reduction relations between SKI terms -/

/-- Single-step reduction of SKI terms -/
@[scoped grind, reduction_sys]
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


open Red Relation

lemma Red.ne {x y : SKI} : (x ⭢ y) → x ≠ y
  | red_S _ _ _, h => by cases h
  | red_K _ _, h => by cases h
  | red_I _, h => by cases h
  | red_head _ _ _ h', h => Red.ne h' (SKI.app.inj h).1
  | red_tail _ _ _ h', h => Red.ne h' (SKI.app.inj h).2

theorem MRed.S (x y z : SKI) : (S ⬝ x ⬝ y ⬝ z) ↠ (x ⬝ z ⬝ (y ⬝ z)) := .single <| red_S ..
theorem MRed.K (x y : SKI) : (K ⬝ x ⬝ y) ↠ x := .single <| red_K ..
theorem MRed.I (x : SKI) : (I ⬝ x) ↠ x := .single <| red_I ..

theorem MRed.head {a a' : SKI} (b : SKI) (h : a ↠ a') : (a ⬝ b) ↠ (a' ⬝ b) := by
  induction h <;> grind

theorem MRed.tail (a : SKI) {b b' : SKI} (h : b ↠ b') : (a ⬝ b) ↠ (a ⬝ b') := by
  induction h <;> grind

lemma parallel_mRed {a a' b b' : SKI} (ha : a ↠ a') (hb : b ↠ b') :
    (a ⬝ b) ↠ (a' ⬝ b') :=
  Trans.simple (MRed.head b ha) (MRed.tail a' hb)

lemma parallel_red {a a' b b' : SKI} (ha : a ⭢ a') (hb : b ⭢ b') : (a ⬝ b) ↠ (a' ⬝ b') := by
  trans a' ⬝ b <;> grind

theorem mJoin_red_head {x x' : SKI} (y : SKI) : MJoin Red x x' → MJoin Red (x ⬝ y) (x' ⬝ y)
  | ⟨z, hz, hz'⟩ => ⟨z ⬝ y, MRed.head y hz, MRed.head y hz'⟩

theorem mJoin_red_tail (x : SKI) {y y' : SKI} : MJoin Red y y' → MJoin Red (x ⬝ y) (x ⬝ y')
  | ⟨z, hz, hz'⟩ => ⟨x ⬝ z, MRed.tail x hz, MRed.tail x hz'⟩

end SKI

end Cslib
