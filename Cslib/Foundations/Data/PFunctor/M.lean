/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import Cslib.Foundations.Data.PFunctor.Basic
public import Mathlib.Data.PFunctor.Univariate.M

/-!
# W-types as well-founded M-types

For a polynomial functor `P`, the W-type `P.W` is its initial algebra (well-founded trees) and the
M-type `P.M` is its final coalgebra (possibly infinite trees). The canonical map `W.toM` regards a
well-founded tree as a possibly infinite one, and `W.equivM` identifies `P.W` with the M-trees that
are accessible for the immediate-subtree relation, i.e. have no infinite descending path.

Lambek's lemma `M.destEquiv` packages the destructor of `P.M` as an equivalence.
-/

@[expose] public section

universe uA uB

namespace PFunctor

variable {P : PFunctor.{uA, uB}}

/-- Lambek's lemma: the destructor of the final coalgebra is an equivalence. -/
@[simps]
def M.destEquiv : P.M ≃ P P.M where
  toFun := M.dest
  invFun := M.mk
  left_inv := M.mk_dest
  right_inv := M.dest_mk

theorem M.dest_injective : Function.Injective (M.dest (F := P)) := M.destEquiv.injective

@[simp]
theorem M.dest_inj {x y : P.M} : M.dest x = M.dest y ↔ x = y := M.dest_injective.eq_iff

/-- The canonical map from the initial algebra into the final coalgebra, regarding a well-founded
tree as a possibly infinite one. -/
def W.toM : P.W → P.M :=
  M.corec W.dest

@[simp]
theorem W.toM_mk (a : P.A) (f : P.B a → P.W) :
    (W.mk ⟨a, f⟩).toM = M.mk ⟨a, fun i => (f i).toM⟩ :=
  M.dest_injective (M.dest_corec _ _)

namespace M

/-- `c` is an immediate subtree of `t`. -/
def IsChild (c t : P.M) : Prop :=
  ∃ i, (M.dest t).2 i = c

/-- An M-tree is well-founded when it is accessible for the immediate-subtree relation, i.e. it has
no infinite descending path. Its branches need not have a common depth bound. -/
abbrev IsWellFounded (t : P.M) : Prop :=
  Acc IsChild t

theorem isWellFounded_mk {a : P.A} {f : P.B a → P.M} :
    (M.mk ⟨a, f⟩).IsWellFounded ↔ ∀ i, (f i).IsWellFounded :=
  ⟨fun h i => h.inv ⟨i, rfl⟩, fun h => ⟨_, fun _ ⟨i, hi⟩ => hi ▸ h i⟩⟩

/-- The W-tree represented by a well-founded M-tree. -/
def toW (t : P.M) (h : t.IsWellFounded) : P.W :=
  Acc.rec (motive := fun _ _ => P.W) (fun t _ ih => W.mk ⟨(M.dest t).1, fun i => ih _ ⟨i, rfl⟩⟩) h

@[simp]
theorem toW_mk (a : P.A) (f : P.B a → P.M) (h : (M.mk ⟨a, f⟩).IsWellFounded) :
    (M.mk ⟨a, f⟩).toW h = W.mk ⟨a, fun i => (f i).toW (isWellFounded_mk.1 h i)⟩ := by
  cases h; rfl

end M

theorem W.isWellFounded_toM (w : P.W) : w.toM.IsWellFounded := by
  induction w with
  | mk a f ih => simpa [M.isWellFounded_mk] using ih

@[simp]
theorem M.toW_toM (w : P.W) (h : w.toM.IsWellFounded) : w.toM.toW h = w := by
  induction w with
  | mk a f ih => simp [ih]

theorem W.toM_toW (t : P.M) (h : t.IsWellFounded) : (t.toW h).toM = t := by
  induction h with
  | intro t _ ih =>
    induction t using M.cases with
    | f x =>
      obtain ⟨a, f⟩ := x
      rw [M.toW_mk, W.toM_mk]
      exact congrArg (M.mk ⟨a, ·⟩) (funext fun i => ih _ ⟨i, rfl⟩)

/-- W-trees are exactly the well-founded M-trees. -/
@[simps]
def W.equivM : P.W ≃ {t : P.M // t.IsWellFounded} where
  toFun w := ⟨w.toM, w.isWellFounded_toM⟩
  invFun t := t.1.toW t.2
  left_inv w := M.toW_toM w _
  right_inv t := Subtype.ext (W.toM_toW t.1 t.2)

theorem W.toM_injective : Function.Injective (W.toM (P := P)) :=
  fun _ _ h => W.equivM.injective (Subtype.ext h)

end PFunctor
