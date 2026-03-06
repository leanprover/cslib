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

/-- Types encoded some calculus. -/
class Encoded (α β : Type*) where
  /-- An element is represented by a term. -/
  IsEncoding : α → β → Prop

def IsEncoding {α β : Type*} [Encoded α β] : α → β → Prop := Encoded.IsEncoding

scoped notation x " ⊩ " a => IsEncoding a x

/-- Types for which encodings are invariant by anti-reduction. -/
class EncodedLift (α : Type*) {β : Type*} (r : β → β → Prop) extends Encoded α β where
  /-- Representation lifts along reductions. -/
  isEncoding_left_of_red : {a : α} → {x y : β} → (y ⊩ a) → r x y → x ⊩ a

/-- Types for which encodings are invariant by reduction. -/
class EncodedDesc (α : Type*) {β : Type*} (r : β → β → Prop) extends Encoded α β where
  /-- Representation descends along reductions. -/
  isEncoding_right_of_red : {a : α} → {x y : β} → (x ⊩ a) → r x y → y ⊩ a

variable {α β : Type*} {r : β → β → Prop}

lemma IsEncoding.left_of_red [EncodedLift α r] {a : α} {x y : β} (ha : y ⊩ a) (h : r x y) :
    x ⊩ a := EncodedLift.isEncoding_left_of_red ha h

lemma IsEncoding.left_of_mRed [EncodedLift α r] {a : α} {x y : β} (ha : y ⊩ a)
    (h : (ReflTransGen r) x y) : x ⊩ a := by
  induction h with
  | refl => assumption
  | tail h h' ih => exact ih <| ha.left_of_red h'

lemma IsEncoding.right_of_red [EncodedDesc α r] {a : α} {x y : β} (ha : x ⊩ a) (h : r x y) :
    y ⊩ a := EncodedDesc.isEncoding_right_of_red ha h

lemma IsEncoding.right_of_mRed [EncodedDesc α r] {a : α} {x y : β} (ha : x ⊩ a)
    (h : (ReflTransGen r) x y) : y ⊩ a := by
  induction h with
  | refl => assumption
  | tail h h' ih => exact ih.right_of_red h'

end Cslib
