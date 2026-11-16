/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Concatenate
public import Cslib.Computability.Machines.Turing.MultiTape.Encodings.HeadCases

/-!
# Complexity of sums and options

The accessors of the sum and option encodings `Cslib.Encoding.encSum` and
`Cslib.Encoding.encOption` only inspect or change the tag bit of a code word. They are computable
in linear time and zero space, independently of the encodings of the components. The constructors
prepend a tag bit to the output of a machine computing the component.

## Main results

* `Turing.MultiTapeTM.ComputableInTimeAndSpace.sum_inl`,
  `Turing.MultiTapeTM.ComputableInTimeAndSpace.sum_inr`,
  `Turing.MultiTapeTM.ComputableInTimeAndSpace.option_some`: the constructors, applied to a
  computable function.
* `Turing.MultiTapeTM.computableInTimeAndSpace_sum_isLeft`,
  `Turing.MultiTapeTM.computableInTimeAndSpace_sum_isRight`,
  `Turing.MultiTapeTM.computableInTimeAndSpace_option_isSome`,
  `Turing.MultiTapeTM.computableInTimeAndSpace_option_isNone`: the tests.
* `Turing.MultiTapeTM.computableInTimeAndSpace_sum_swap`: swapping the components of a sum.
* `Turing.MultiTapeTM.computableInTimeAndSpace_sum_getLeft?`,
  `Turing.MultiTapeTM.computableInTimeAndSpace_sum_getRight?`,
  `Turing.MultiTapeTM.computableInTimeAndSpace_option_getD`: the partial accessors.
-/

public section

namespace Turing.MultiTapeTM

open Cslib.Encoding

variable {α β γ : Type*} {enc₁ : α ↪ List Bool} {enc₂ : β ↪ List Bool}
  {encIn : γ ↪ List Bool} {t s : γ → ℕ}

/-! ### Constructors -/

/-- `Sum.inl` of a computable function is computable in time `t + 8` and space `3 * s`: a machine
emitting the tag runs first, the input is rewound, and the machine computing the component appends
its output. -/
theorem ComputableInTimeAndSpace.sum_inl {f : γ → α}
    (h : ComputableInTimeAndSpace f encIn enc₁ t s) :
    ComputableInTimeAndSpace (fun x => (Sum.inl (f x) : α ⊕ β)) encIn (encSum enc₁ enc₂)
      (fun x => t x + 8) (fun x => 3 * s x) :=
  ((computableInTimeAndSpace_const (encOut := encBool) false).concatenate h fun _ => rfl).mono
    (fun _ => by simp only [encBool_apply, List.length_singleton]; lia) fun _ => by lia

/-- `Sum.inr` of a computable function is computable in time `t + 8` and space `3 * s`, as for
`sum_inl`. -/
theorem ComputableInTimeAndSpace.sum_inr {f : γ → β}
    (h : ComputableInTimeAndSpace f encIn enc₂ t s) :
    ComputableInTimeAndSpace (fun x => (Sum.inr (f x) : α ⊕ β)) encIn (encSum enc₁ enc₂)
      (fun x => t x + 8) (fun x => 3 * s x) :=
  ((computableInTimeAndSpace_const (encOut := encBool) true).concatenate h fun _ => rfl).mono
    (fun _ => by simp only [encBool_apply, List.length_singleton]; lia) fun _ => by lia

/-- `some` of a computable function is computable in time `t + 8` and space `3 * s`, as for
`sum_inl`. -/
theorem ComputableInTimeAndSpace.option_some {f : γ → α}
    (h : ComputableInTimeAndSpace f encIn enc₁ t s) :
    ComputableInTimeAndSpace (fun x => some (f x)) encIn (encOption enc₁)
      (fun x => t x + 8) (fun x => 3 * s x) :=
  ((computableInTimeAndSpace_const (encOut := encBool) true).concatenate h fun _ => rfl).mono
    (fun _ => by simp only [encBool_apply, List.length_singleton]; lia) fun _ => by lia

/-! ### Sums -/

/-- `Sum.isLeft` is computable in linear time and zero space. -/
theorem computableInTimeAndSpace_sum_isLeft :
    ComputableInTimeAndSpace (Sum.isLeft : α ⊕ β → Bool) (encSum enc₁ enc₂) encBool
      (fun x => 2 * (encSum enc₁ enc₂ x).length + 2) (fun _ => 0) :=
  ((computableInTimeAndSpace_headCases [] (fun b => [!b]) fun _ => false).of_realizes
    fun x => by cases x <;> simp).mono (fun _ => by simp) fun _ => le_rfl

/-- `Sum.isRight` is computable in linear time and zero space. -/
theorem computableInTimeAndSpace_sum_isRight :
    ComputableInTimeAndSpace (Sum.isRight : α ⊕ β → Bool) (encSum enc₁ enc₂) encBool
      (fun x => 2 * (encSum enc₁ enc₂ x).length + 2) (fun _ => 0) :=
  ((computableInTimeAndSpace_headCases [] (fun b => [b]) fun _ => false).of_realizes
    fun x => by cases x <;> simp).mono (fun _ => by simp) fun _ => le_rfl

/-- `Sum.swap` is computable in linear time and zero space. -/
theorem computableInTimeAndSpace_sum_swap :
    ComputableInTimeAndSpace (Sum.swap : α ⊕ β → β ⊕ α) (encSum enc₁ enc₂) (encSum enc₂ enc₁)
      (fun x => 2 * (encSum enc₁ enc₂ x).length + 2) (fun _ => 0) :=
  ((computableInTimeAndSpace_headCases [] (fun b => [!b]) fun _ => true).of_realizes
    fun x => by cases x <;> simp).mono (fun _ => by simp) fun _ => le_rfl

/-- `Sum.getLeft?` is computable in linear time and zero space. -/
theorem computableInTimeAndSpace_sum_getLeft? :
    ComputableInTimeAndSpace (Sum.getLeft? : α ⊕ β → Option α) (encSum enc₁ enc₂)
      (encOption enc₁) (fun x => 2 * (encSum enc₁ enc₂ x).length + 2) (fun _ => 0) :=
  ((computableInTimeAndSpace_headCases [] (fun b => [!b]) fun b => !b).of_realizes
    fun x => by cases x <;> simp).mono (fun _ => by simp) fun _ => le_rfl

/-- `Sum.getRight?` is computable in linear time and zero space. -/
theorem computableInTimeAndSpace_sum_getRight? :
    ComputableInTimeAndSpace (Sum.getRight? : α ⊕ β → Option β) (encSum enc₁ enc₂)
      (encOption enc₂) (fun x => 2 * (encSum enc₁ enc₂ x).length + 2) (fun _ => 0) :=
  ((computableInTimeAndSpace_headCases [] (fun b => [b]) fun b => b).of_realizes
    fun x => by cases x <;> simp).mono (fun _ => by simp) fun _ => le_rfl

/-! ### Options -/

/-- `Option.isSome` is computable in constant time and zero space, since it is constant except on
`none`. -/
theorem computableInTimeAndSpace_option_isSome :
    ComputableInTimeAndSpace (Option.isSome : Option α → Bool) (encOption enc₁) encBool
      (fun _ => 5) (fun _ => 0) :=
  (computableInTimeAndSpace_almostConstTime Option.isSome {none} [true]
    fun o ho => by cases o <;> simp_all).mono (fun _ => by simp [almostConstTime]) fun _ => le_rfl

/-- `Option.isNone` is computable in constant time and zero space, since it is constant except on
`none`. -/
theorem computableInTimeAndSpace_option_isNone :
    ComputableInTimeAndSpace (Option.isNone : Option α → Bool) (encOption enc₁) encBool
      (fun _ => 5) (fun _ => 0) :=
  (computableInTimeAndSpace_almostConstTime Option.isNone {none} [false]
    fun o ho => by cases o <;> simp_all).mono (fun _ => by simp [almostConstTime]) fun _ => le_rfl

/-- `Option.getD` with a fixed default `d` is computable in linear time and zero space. -/
theorem computableInTimeAndSpace_option_getD (d : α) :
    ComputableInTimeAndSpace (Option.getD · d : Option α → α) (encOption enc₁) enc₁
      (fun o => 2 * (encOption enc₁ o).length + (enc₁ d).length + 1) (fun _ => 0) :=
  ((computableInTimeAndSpace_headCases [] (fun b => if b then [] else enc₁ d)
    fun b => b).of_realizes fun o => by cases o <;> simp).mono (fun _ => by simp) fun _ => le_rfl

end Turing.MultiTapeTM
