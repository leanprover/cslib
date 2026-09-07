/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Mathlib.Basic.Finite.Sum
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Concat

/-!
# Complexity of a concatenation of two functions

If `f` and `g` are computable, then so is any function whose encoded result is the encoded result
of `f` followed by the encoded result of `g`. The bounds are the sums of the two bounds, plus one
input rewind in time and a constant in space.

The result is stated for an arbitrary function `h` together with the assumption that its encoding
is the concatenation of the two encodings, rather than for a fixed pairing. That way it covers
whatever the caller happens to be encoding — a pair, a list, a tagged union — and the caller is
the one who has to know that the concatenation of the two encodings is again injective. The pair
is the typical case and is spelled out in `computableInTimeAndSpace_pair`.

Note that nothing has to be assumed about how the two encodings compose beyond `henc`: the machine
never inspects the concatenation. It writes the first encoded result to the output tape, and then
writes the second one after it, so the concatenation is produced simply by not resetting the output
tape in between.

## Main results

* `Turing.MultiTapeTM.computableInTimeAndSpace_concat`: the complexity of a concatenation.
* `Turing.MultiTapeTM.computableInTimeAndSpace_pair`: the special case of a pair.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {α β γ δ : Type*}

/-- **Complexity of a concatenation.** If `f` and `g` are computable and the encoded result of `h`
is the encoded result of `f` followed by the encoded result of `g`, then `h` is computable in the
sum of the two times plus the length of the input, and in the sum of the two spaces plus a
constant.

The machine runs the machine for `f`, rewinds the input head, and runs the machine for `g` on fresh
work tapes; the length of the input in the time bound is the cost of that rewind. The intermediate
results are never stored: both machines write straight to the output tape, which is append-only, so
their outputs end up concatenated. The constant in the space bound is the number of work tapes of
the two machines, each of which contributes the one cell its head is parked on while the other
machine runs; the rewind itself costs no space. -/
theorem computableInTimeAndSpace_concat
    {f : α → β} {g : α → γ} {h : α → δ}
    {encIn : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool} {encD : δ ↪ List Bool}
    {tf sf tg sg : α → ℕ}
    (henc : ∀ x, encD (h x) = encB (f x) ++ encC (g x))
    (hf : ComputableInTimeAndSpace f encIn encB tf sf)
    (hg : ComputableInTimeAndSpace g encIn encC tg sg) :
    ∃ c, ComputableInTimeAndSpace h encIn encD
      (fun x => tf x + tg x + (encIn x).length + 2)
      (fun x => sf x + sg x + c) := by
  obtain ⟨k₀, State₀, hfinite₀, tm₀, htm₀⟩ := hf
  obtain ⟨k₁, State₁, hfinite₁, tm₁, htm₁⟩ := hg
  refine ⟨k₀ + k₁, k₀ + k₁, (State₀ ⊕ RewindState) ⊕ State₁, inferInstance,
    concat tm₀ tm₁, fun x => ?_⟩
  obtain ⟨t₀, ht₀, s₀, hs₀, hcomp₀⟩ := htm₀ x
  obtain ⟨t₁, ht₁, s₁, hs₁, hcomp₁⟩ := htm₁ x
  obtain ⟨t, htle, s, hsle, hcomp⟩ := computesInTimeAndSpace_concat tm₀ tm₁ hcomp₀ hcomp₁
  have htbound : t ≤ tf x + tg x + (encIn x).length + 2 := by omega
  have hsbound : s ≤ sf x + sg x + (k₀ + k₁) := by omega
  exact ⟨t, htbound, s, hsbound, henc x ▸ hcomp⟩

/-- **Complexity of computing a pair.** The special case of `computableInTimeAndSpace_concat` in
which the two results are packed into a pair, encoded by concatenating the two encodings. It is up
to the caller to provide such an encoding; this needs the encoding of the first component to
determine where it ends, as a prefix-free or length-prefixed encoding does. -/
theorem computableInTimeAndSpace_pair
    {f : α → β} {g : α → γ}
    {encIn : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
    {encPair : β × γ ↪ List Bool} {tf sf tg sg : α → ℕ}
    (henc : ∀ p : β × γ, encPair p = encB p.1 ++ encC p.2)
    (hf : ComputableInTimeAndSpace f encIn encB tf sf)
    (hg : ComputableInTimeAndSpace g encIn encC tg sg) :
    ∃ c, ComputableInTimeAndSpace (fun x => (f x, g x)) encIn encPair
      (fun x => tf x + tg x + (encIn x).length + 2)
      (fun x => sf x + sg x + c) :=
  computableInTimeAndSpace_concat (fun x => henc (f x, g x)) hf hg

end Turing.MultiTapeTM
