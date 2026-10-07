/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module

public import Cslib.Init
public import Mathlib.Order.RelSeries

/-!
# Series of a right-unique relation

Two series of a right-unique relation with the same head agree at every common index.
-/

@[expose] public section

open scoped SetRel

namespace RelSeries

variable {α : Type*} {r : SetRel α α}

/-- Two series of a right-unique relation with the same head agree at every common index. -/
lemma apply_eq_of_rightUnique (p q : RelSeries r) (hr : Relator.RightUnique (· ~[r] ·))
    (hh : p.head = q.head) (i : Fin (p.length + 1)) (j : Fin (q.length + 1))
    (hij : i.val = j.val) : p i = q j := by
  induction i using Fin.induction generalizing j with
  | zero =>
    have hj : j = 0 := Fin.ext hij.symm
    subst j
    exact hh
  | succ i ih =>
    obtain ⟨j, rfl⟩ := j.eq_succ_of_ne_zero (by intro hj; simp [hj] at hij)
    have hp := p.step i
    rw [ih j.castSucc (Nat.succ.inj hij)] at hp
    exact hr hp (q.step j)

end RelSeries
