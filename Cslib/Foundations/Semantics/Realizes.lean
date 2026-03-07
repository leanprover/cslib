/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Foundations.Data.Relation

@[expose] public section

namespace Cslib

open Relation

/-- A type `α` has "realisers" in some calculus `β`. -/
class HasRealizer (α β : Type*) where
  /-- A term represents (realizes) a element. -/
  Realizes : β → α → Prop

def Realizes {α β : Type*} [HasRealizer α β] : β → α → Prop := HasRealizer.Realizes

scoped notation x " ⊩ " a => Realizes x a

/-- Types for which the realisability relation is invariant by anti-reduction. -/
class HasRealizerLift (α : Type*) {β : Type*} (r : β → β → Prop) extends HasRealizer α β where
  /-- Realisers lift along reductions. -/
  realizes_left_of_red : {a : α} → {x y : β} → (y ⊩ a) → r x y → x ⊩ a

/-- Types for which the realisability relation is invariant by reduction. -/
class HasRealizerDesc (α : Type*) {β : Type*} (r : β → β → Prop) extends HasRealizer α β where
  /-- Realisers descend along reductions. -/
  realizes_right_of_red : {a : α} → {x y : β} → (x ⊩ a) → r x y → y ⊩ a

variable {α β : Type*} {r : β → β → Prop}

lemma Realizes.left_of_red [HasRealizerLift α r] {a : α} {x y : β} (ha : y ⊩ a) (h : r x y) :
    x ⊩ a := HasRealizerLift.realizes_left_of_red ha h

lemma Realizes.left_of_mRed [HasRealizerLift α r] {a : α} {x y : β} (ha : y ⊩ a)
    (h : (ReflTransGen r) x y) : x ⊩ a := by
  induction h with
  | refl => assumption
  | tail h h' ih => exact ih <| ha.left_of_red h'

lemma Realizes.right_of_red [HasRealizerDesc α r] {a : α} {x y : β} (ha : x ⊩ a) (h : r x y) :
    y ⊩ a := HasRealizerDesc.realizes_right_of_red ha h

lemma Realizes.right_of_mRed [HasRealizerDesc α r] {a : α} {x y : β} (ha : x ⊩ a)
    (h : (ReflTransGen r) x y) : y ⊩ a := by
  induction h with
  | refl => assumption
  | tail h h' ih => exact ih.right_of_red h'

end Cslib
