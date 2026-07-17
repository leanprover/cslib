/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
import Cslib.Computability.Machines.Turing.SingleTape.PolyTime.Basic
import Cslib.Computability.Machines.Turing.SingleTape.PolyTime.TakeFirstBlock
import Cslib.Computability.Machines.Turing.SingleTape.PolyTime.UndelimitBlock

/-!
# Symmetric monoidal structure on encoded types

Types carrying a `BitstringEncoding`, with polynomial-time computable functions as morphisms, form
a symmetric monoidal category: the tensor product of objects is `α × β` (with the block-based pair
encoding) and the tensor unit is `Unit` (encoded as the empty bitstring). Together with
`IsComputableInPolyTime.id` and `IsComputableInPolyTime.comp`, this file states the remaining
structure maps: the first projection, the tensor product of morphisms, the braiding, the
associator, and the unitors.

## Main results

* `IsComputableInPolyTime_fst`: the first projection on encoded pairs is polynomial-time computable.
* The `SymmetricMonoidal` section states the remaining structure maps; those whose machines are not
  yet built are `sorry`ed.
-/

open Computability Turing

namespace ComplexityTheory

open BitstringEncoding (undelimitBlock undelimitBlock_delimit)

/-- The first projection on encoded pairs is polynomial-time computable, by composing
`takeFirstBlock` (drop everything after the first block) and `undelimitBlock` (strip framing). -/
lemma IsComputableInPolyTime_fst {α β : Type} [BitstringEncoding α] [BitstringEncoding β] :
    IsComputableInPolyTime (Prod.fst : α × β → α) := by
  obtain ⟨m1⟩ := PolyTimeComputable_takeFirstBlock
  obtain ⟨m2⟩ := PolyTimeComputable_undelimitBlock
  refine ⟨undelimitBlock ∘ takeFirstBlock, ⟨m1.comp' m2⟩, ?_⟩
  rintro ⟨x, w⟩
  change undelimitBlock (takeFirstBlock (BitstringEncoding.encode (x, w)))
    = BitstringEncoding.encode x
  have h : BitstringEncoding.encode (x, w)
      = BitstringEncoding.delimit (BitstringEncoding.encode x) ++ BitstringEncoding.encode w := rfl
  rw [h, takeFirstBlock_delimit_append, undelimitBlock_delimit]

/-!
### Symmetric monoidal structure

Types carrying a `BitstringEncoding`, with polynomial-time computable functions as morphisms, form
a symmetric monoidal category: the tensor product of objects is `α × β` (with the block-based pair
encoding) and the tensor unit is `Unit` (encoded as the empty bitstring). Together with
`IsComputableInPolyTime.id` and `IsComputableInPolyTime.comp` above, this section states the
remaining operations: the tensor product of morphisms, the braiding, the associator, and the
unitors, each with its inverse where the structure map is an isomorphism. The coherence laws hold
on the nose, since they are equalities of the underlying functions.

At the level of encodings, `encode (x, y) = delimit (encode x) ++ encode y` and `encode () = []`,
so each structure map is a concrete rearrangement of self-delimiting blocks; the docstrings record
the bitstring-level function the witnessing machine must compute.
-/

section SymmetricMonoidal

variable {α β γ δ : Type}
variable [BitstringEncoding α] [BitstringEncoding β] [BitstringEncoding γ] [BitstringEncoding δ]

/-- Tensor product of morphisms: if `f` and `g` are polynomial-time computable, so is
`Prod.map f g : α × β → γ × δ`. The underlying machine must run the machine for `f` on the payload
of the leading self-delimiting block (re-delimiting its output) and the machine for `g` on the
remainder of the input.

TODO: construct the machine. -/
lemma IsComputableInPolyTime.prodMap {f : α → γ} {g : β → δ}
    (hf : IsComputableInPolyTime f) (hg : IsComputableInPolyTime g) :
    IsComputableInPolyTime (Prod.map f g) := by
  sorry

/-- The braiding: swapping the components of a pair is polynomial-time computable. On encodings
this exchanges the leading block with the trailing remainder, moving the framing:
`delimit P ++ Q ↦ delimit Q ++ P`.

TODO: construct the machine. -/
lemma IsComputableInPolyTime_swap :
    IsComputableInPolyTime (Prod.swap : α × β → β × α) := by
  sorry

/-- The associator: `((x, y), z) ↦ (x, (y, z))` is polynomial-time computable. On encodings this
reframes `delimit (delimit P ++ Q) ++ R` as `delimit P ++ delimit Q ++ R`.

TODO: construct the machine. -/
lemma IsComputableInPolyTime_prodAssoc :
    IsComputableInPolyTime (fun p : (α × β) × γ => (p.1.1, (p.1.2, p.2))) := by
  sorry

/-- The inverse associator: `(x, (y, z)) ↦ ((x, y), z)` is polynomial-time computable. On
encodings this reframes `delimit P ++ delimit Q ++ R` as `delimit (delimit P ++ Q) ++ R`.

TODO: construct the machine. -/
lemma IsComputableInPolyTime_prodAssoc_symm :
    IsComputableInPolyTime (fun p : α × (β × γ) => ((p.1, p.2.1), p.2.2)) := by
  sorry

/-- The left unitor: `((), x) ↦ x` is polynomial-time computable. Since `encode () = []`, on
encodings this drops the leading `false` (the delimiter of the empty block):
`false :: P ↦ P`.

TODO: construct the machine (a leftward shift by one cell; alternatively derive this from a
general `Prod.snd` lemma once a drop-first-block machine exists). -/
lemma IsComputableInPolyTime_leftUnitor :
    IsComputableInPolyTime (Prod.snd : Unit × α → α) := by
  sorry

/-- The inverse left unitor: `x ↦ ((), x)` is polynomial-time computable. On encodings this
prepends `false`: `P ↦ false :: P`.

TODO: construct the machine (a rightward shift by one cell, like the accepting branch of
`tagBlockComputer`). -/
lemma IsComputableInPolyTime_leftUnitor_inv :
    IsComputableInPolyTime (fun x : α => ((), x)) := by
  sorry

/-- The right unitor: `(x, ()) ↦ x` is polynomial-time computable. Since `encode () = []`, the
encoding of `(x, ())` is exactly `delimit (encode x)`, and this is the first projection, already
witnessed by `takeFirstBlockComputer` and `undelimitBlockComputer`. -/
lemma IsComputableInPolyTime_rightUnitor :
    IsComputableInPolyTime (Prod.fst : α × Unit → α) :=
  IsComputableInPolyTime_fst

/-- The inverse right unitor: `x ↦ (x, ())` is polynomial-time computable. On encodings this is
`delimit`: `P ↦ delimit P`.

TODO: construct the machine (an expansion shuttle mirroring `undelimitBlockComputer`). -/
lemma IsComputableInPolyTime_rightUnitor_inv :
    IsComputableInPolyTime (fun x : α => (x, ())) := by
  sorry

end SymmetricMonoidal

end ComplexityTheory
