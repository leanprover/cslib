/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Concatenate
public import Cslib.Computability.Machines.Turing.MultiTape.Combinators.DelimitOutput
public import Cslib.Computability.Machines.Turing.MultiTape.Encodings.Delimit

/-!
# Complexity of lists

The accessors of the list encoding `Cslib.Encoding.encList` are computable in linear time and zero
space, independently of the encoding of the elements. Lists are built from machines that compute
their parts from the same input.

## Main results

* `Turing.MultiTapeTM.ComputableInTimeAndSpace.list_cons`,
  `Turing.MultiTapeTM.ComputableInTimeAndSpace.list_append`,
  `Turing.MultiTapeTM.ComputableInTimeAndSpace.list_singleton`: building lists from computable
  functions.
* `Turing.MultiTapeTM.computableInTimeAndSpace_list_tail`,
  `Turing.MultiTapeTM.computableInTimeAndSpace_list_headD`: the tail and the head with a default.
* `Turing.MultiTapeTM.computableInTimeAndSpace_list_isEmpty`: the emptiness test.
* `Turing.MultiTapeTM.computableInTimeAndSpace_list_flatten`: concatenating a list of lists.
-/

public section

namespace Turing.MultiTapeTM

open Cslib.Encoding

variable {α γ : Type*} {enc : α ↪ List Bool} {encIn : γ ↪ List Bool}

/-! ### Constructors -/

/-- Prepending a computable element to a computable list is computable in time `4 * t₁ + t₂ + 4`
and space `3 * (s₁ + s₂)`: the machine for the element runs with its output delimited, the input
is rewound, and the machine for the list appends its output. -/
theorem ComputableInTimeAndSpace.list_cons {f₁ : γ → α} {f₂ : γ → List α} {t₁ t₂ s₁ s₂ : γ → ℕ}
    (h₁ : ComputableInTimeAndSpace f₁ encIn enc t₁ s₁)
    (h₂ : ComputableInTimeAndSpace f₂ encIn (encList enc) t₂ s₂) :
    ComputableInTimeAndSpace (fun x => f₁ x :: f₂ x) encIn (encList enc)
      (fun x => 4 * t₁ x + t₂ x + 4) (fun x => 3 * (s₁ x + s₂ x)) :=
  (h₁.delimit.concatenate h₂ fun _ => rfl).mono (fun _ => by lia) fun _ => le_rfl

/-- Concatenating two computable lists is computable in time `2 * t₁ + t₂ + 2` and space
`3 * (s₁ + s₂)`: the codes of the lists are concatenated. -/
theorem ComputableInTimeAndSpace.list_append {f₁ f₂ : γ → List α} {t₁ t₂ s₁ s₂ : γ → ℕ}
    (h₁ : ComputableInTimeAndSpace f₁ encIn (encList enc) t₁ s₁)
    (h₂ : ComputableInTimeAndSpace f₂ encIn (encList enc) t₂ s₂) :
    ComputableInTimeAndSpace (fun x => f₁ x ++ f₂ x) encIn (encList enc)
      (fun x => 2 * t₁ x + t₂ x + 2) (fun x => 3 * (s₁ x + s₂ x)) :=
  h₁.concatenate h₂ fun _ => encList_append ..

/-- The list with one computable element is computable in time `2 * t + 1` and space `s`: its
code is the delimited code of the element. -/
theorem ComputableInTimeAndSpace.list_singleton {f : γ → α} {t s : γ → ℕ}
    (h : ComputableInTimeAndSpace f encIn enc t s) :
    ComputableInTimeAndSpace (fun x => [f x]) encIn (encList enc) (fun x => 2 * t x + 1) s :=
  h.delimit.congr_out fun x => encList_singleton enc (f x)

/-! ### Accessors -/

/-- The tail of a list is computable in linear time and zero space. -/
theorem computableInTimeAndSpace_list_tail :
    ComputableInTimeAndSpace (List.tail : List α → List α) (encList enc) (encList enc)
      (fun l => 2 * (encList enc l).length + 1) (fun _ => 0) :=
  computableInTimeAndSpace_dropDelimited.of_realizes fun l => by cases l <;> simp

/-- The head of a list with a fixed default `d` is computable in linear time and zero space. -/
theorem computableInTimeAndSpace_list_headD (d : α) :
    ComputableInTimeAndSpace (List.headD · d : List α → α) (encList enc) enc
      (fun l => 2 * (encList enc l).length + (enc d).length + 1) (fun _ => 0) :=
  (computableInTimeAndSpace_undelimitOr (enc d)).of_realizes fun l => by cases l <;> simp

/-- The emptiness test is computable in constant time and zero space, since it is constant except
on the empty list. -/
theorem computableInTimeAndSpace_list_isEmpty :
    ComputableInTimeAndSpace (List.isEmpty : List α → Bool) (encList enc) encBool
      (fun _ => 4) (fun _ => 0) :=
  (computableInTimeAndSpace_almostConstTime List.isEmpty {[]} [false]
    fun l hl => by cases l <;> simp_all).mono (fun _ => by simp [almostConstTime]) fun _ => le_rfl

/-- Concatenating a list of lists is computable in linear time and zero space. -/
theorem computableInTimeAndSpace_list_flatten :
    ComputableInTimeAndSpace (List.flatten : List (List α) → List α) (encList (encList enc))
      (encList enc) (fun l => 2 * (encList (encList enc) l).length + 1) (fun _ => 0) :=
  computableInTimeAndSpace_undelimitAll.of_realizes fun l => by induction l <;> simp [*]

end Turing.MultiTapeTM
