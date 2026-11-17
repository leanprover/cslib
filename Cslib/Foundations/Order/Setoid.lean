/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Mathlib.Order.Setoid.Partition
public import Cslib.Foundations.Data.SetRel

/-!-/

@[expose] public section

namespace IndexedPartition

variable {ι α : Type*} {s : ι → Set α} (hs : IndexedPartition s)

lemma mem_apply_index (x : α) : x ∈ s (hs.index x) := hs.mem_iff_index_eq.mpr rfl

def equivSigma : α ≃ Σ i, s i where
  toFun x := ⟨hs.index x, x, hs.mem_apply_index x⟩
  invFun x := x.snd.val
  right_inv := by
    intro ⟨i, x, hx⟩
    ext
    · exact hs.mem_iff_index_eq.mp hx
    · rfl

def equivSubtypeProd : α ≃ {p : ι × α // p.2 ∈ s p.1} where
  toFun x := ⟨(hs.index x, x), hs.mem_apply_index x⟩
  invFun p := p.val.2
  right_inv := by
    intro ⟨(i, x), (hx : x ∈ s i)⟩
    ext
    · exact hs.mem_iff_index_eq.mp hx
    · rfl

end IndexedPartition

namespace Setoid

def eqvClass {α : Type*} (s : Setoid α) : Quotient s → Set α :=
  Quotient.lift (fun a ↦ {b | s a b}) <| by
    intro _ _ (h : s _ _)
    grind [s.iseqv.trans, s.iseqv.symm]

@[simp] lemma mem_eqvClass {α : Type*} (s : Setoid α) (x : α) (i : Quotient s) :
    x ∈ s.eqvClass i ↔ ⟦x⟧ = i := by
  apply i.ind
  simp [eqvClass, Quotient.eq, comm]

noncomputable def toIndexedPartition {α : Type*} (s : Setoid α) :
    IndexedPartition s.eqvClass where
  eq_of_mem := by simp
  some := Quotient.out
  some_mem i := by apply i.ind; simp
  index := Quotient.mk s
  mem_index x := s.mem_eqvClass _ _ |>.mpr rfl

open SetRel in
example {α : Type*} {r : SetRel α α} {s : Setoid α} : r ⊆ .ofRel s ↔ ∀ x y, x ~[r] y → s x y := by
  grind

end Setoid
