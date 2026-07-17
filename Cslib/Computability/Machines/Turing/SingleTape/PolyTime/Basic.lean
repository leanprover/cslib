/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
import Cslib.Foundations.Data.BitstringEncoding
import Cslib.Computability.Machines.Turing.SingleTape.Deterministic
import Cslib.Computability.Machines.Turing.SingleTape.PolyTime.Id
import Cslib.Computability.Machines.Turing.SingleTape.PolyTime.Comp

/-!
# Polynomial-time computable functions between encoded types

This file abstracts the low-level `SingleTapeTM.PolyTimeComputable` predicate (about functions
`List Bool → List Bool`) into `IsComputableInPolyTime`, a predicate on functions `f : α → β`
between arbitrary types carrying a `BitstringEncoding`, and establishes the generic closure
properties that do not require building a specific Turing machine.

## Main results

* `IsComputableInPolyTime.id`: the identity function is polynomial-time computable.
* `IsComputableInPolyTime.comp`: closure under composition.
* `IsComputableInPolyTime.finite`: any function out of a finite type is polynomial-time computable.
* `IsComputableInPolyTime.optionMap`: `Option.map` preserves polynomial-time computability.

The concrete machine constructions witnessing computability of specific operations on encoded
pairs live in the sibling files of this directory (`TakeFirstBlock`, `UndelimitBlock`, `TagBlock`,
`Prod`).
-/

open Computability Turing

namespace ComplexityTheory

/--
A simple definition to abstract the notion of a poly-time Turing machine into a predicate.
-/
def IsComputableInPolyTime {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    (f : α → β) : Prop :=
  ∃ f' : List Bool → List Bool,
    Nonempty (Cslib.Turing.SingleTapeTM.PolyTimeComputable f') ∧
    ∀ x, f' (BitstringEncoding.encode x) = BitstringEncoding.encode (f x)

/-- The identity function is polynomial-time computable. -/
lemma IsComputableInPolyTime.id {α : Type} [BitstringEncoding α] :
    IsComputableInPolyTime (id : α → α) :=
  ⟨_root_.id, ⟨Cslib.Turing.SingleTapeTM.PolyTimeComputable.id⟩, fun _ => rfl⟩

lemma IsComputableInPolyTime.comp {α β γ : Type}
    [BitstringEncoding α] [BitstringEncoding β] [BitstringEncoding γ]
    {f : α → β} {g : β → γ}
    (hf : IsComputableInPolyTime f) (hg : IsComputableInPolyTime g) :
    IsComputableInPolyTime (g ∘ f) := by
  rcases hf with ⟨f', ⟨hft, hfe⟩⟩
  rcases hg with ⟨g', ⟨hgt, hge⟩⟩
  use g' ∘ f'
  constructor
  · exact Nonempty.intro ((Classical.choice hft).comp' (Classical.choice hgt))
  · intro x
    simp only [Function.comp_apply, hfe, hge]

/--
A function with a finite domain is always computable in polynomial time, since we can just
hardcode the output for each input.
-/
lemma IsComputableInPolyTime.finite {α β : Type}
    [Finite α] [BitstringEncoding α] [BitstringEncoding β]
    (f : α → β) : IsComputableInPolyTime f := by
  -- We hardcode the output for each input into a lookup table: over the finite set of encodings
  -- of `α`, the function `g` below decodes the input and re-encodes `f` of it. Any function with a
  -- finite domain of interest is polynomial-time computable via `ofFinsetDomain`.
  have : Fintype α := Fintype.ofFinite α
  set S : Finset (List Bool) := Finset.univ.image (BitstringEncoding.encode : α → List Bool)
    with hS
  set g : List Bool → List Bool :=
    fun s => (BitstringEncoding.decode s).elim [] fun x => BitstringEncoding.encode (f x) with hg
  refine ⟨fun s => if s ∈ S then g s else [],
    ⟨Cslib.Turing.SingleTapeTM.PolyTimeComputable.ofFinsetDomain g S⟩, ?_⟩
  intro x
  have hx : BitstringEncoding.encode x ∈ S := by
    rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ x)
  simp only [hg, if_pos hx]
  simp

/--
If `f` is polynomial-time computable, then so is `Option.map f`. The underlying machine preserves
the leading `some`/`none` tag of the encoding and runs the machine for `f` on the payload.
-/
lemma IsComputableInPolyTime.optionMap {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    {f : α → β} (hf : IsComputableInPolyTime f) :
    IsComputableInPolyTime (Option.map f) := by
  obtain ⟨f', ⟨hft, hfe⟩⟩ := hf
  refine ⟨Cslib.Turing.SingleTapeTM.onTailFun f', ⟨(Classical.choice hft).onTail⟩, ?_⟩
  intro o
  cases o with
  | none => rfl
  | some a =>
    change true :: f' (BitstringEncoding.encode a) = true :: BitstringEncoding.encode (f a)
    rw [hfe a]

end ComplexityTheory
