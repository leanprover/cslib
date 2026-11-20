/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Full.Blocks

/-!
# Finite Lupanov synthesis over the full basis

Split the inputs into `r` section coordinates and `d` data coordinates. For a carrier of
size `q`, place the `q ^ d` data assignments in `B = q ^ d ⌈/⌉ t` blocks of `t` cells,
allowing padding in the last block. Both decoders and the block dictionaries are built
once and shared by all `m` outputs. Each output then assembles one table per section.

`synthesis` assumes the input coordinates, zero, and a nonzero marker are already available.
`bound` counts the additional gates and retains the input split, block size, and gate arity
so callers can choose these parameters to obtain a suitable upper bound.

## References

* [O. B. Lupanov, *On a Method of Circuit Synthesis*][Lupanov1958]: shared-table synthesis.
-/

@[expose] public section

namespace Cslib.Circuits.Full.Lupanov

variable {U : Type*} {k r d t m : ℕ}

/-- Gate budget for a carrier of size `q`, arity `k`, `r` section coordinates, `d` data
coordinates, blocks of `t` cells, and `m` outputs. The first three terms build shared
decoders and dictionaries; only section assembly is repeated for each output. -/
def bound (q k r d t m : ℕ) : ℕ :=
  let B := q ^ d ⌈/⌉ t
  (∑ j ∈ Finset.range r, q ^ (j + 1)) + (∑ j ∈ Finset.range d, q ^ (j + 1)) +
    B * (∑ j ∈ Finset.range t, q ^ (j + 1)) +
      m * (q ^ r * (((B - 1) ⌈/⌉ (k - 1)) + 1) + ((q ^ r - 1) ⌈/⌉ (k - 1)))

/-- Synthesize all outputs using shared decoders and block dictionaries, for any input split
and positive block size. The input coordinates, zero, and a nonzero marker must be available. -/
theorem synthesis [Zero U] [Fintype U] (hk : 2 ≤ k) (ht : 0 < t)
    (marker : U) (hm : marker ≠ 0) (f : (Fin (r + d) → U) → Fin m → U)
    {s : Set ((Fin (r + d) → U) → U)} (hzero : (fun _ => 0) ∈ s)
    (hmarker : (fun _ => marker) ∈ s) (hin : inputs (r + d) ⊆ s) :
    Synthesis (fullInterpretation (k := k)) s (Set.range fun j x => f x j)
      (bound (Fintype.card U) k r d t m) := by
  classical
  let q := Fintype.card U
  let B := q ^ d ⌈/⌉ t
  obtain ⟨index⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin d → U) (β := Fin B × Fin t) (by
      simpa [q, B, smul_eq_mul, Nat.mul_comm] using le_smul_ceilDiv (b := q ^ d) ht)
  let left := fun (i : Fin r) (x : Fin (r + d) → U) => x (Fin.castAdd d i)
  let right := fun (i : Fin d) (x : Fin (r + d) → U) => x (Fin.natAdd r i)
  let address := fun x => index (fun i => right i x)
  have hleft := synthesis_indicators hk 0 marker left hmarker (fun i => hin ⟨_, rfl⟩)
  have hdictionaries := synthesis_coordinateDictionaries hk marker right index hzero hmarker
    (fun i => hin ⟨_, rfl⟩)
  let tables := fun (j : Fin m) (a : Fin r → U) =>
    Function.extend index (fun b => f (Fin.append a b) j) (fun _ => 0)
  have hsection (j : Fin m) : Synthesis (fullInterpretation (k := k))
      (s ∪ (Set.range (indicator 0 marker left) ∪ blockDictionaries marker address))
      {fun x => f x j}
      (q ^ r * (((B - 1) ⌈/⌉ (k - 1)) + 1) + ((q ^ r - 1) ⌈/⌉ (k - 1))) := by
    have h := synthesis_sections hk marker hm (fun x i => left i x) address
      (s := s ∪ (Set.range (indicator 0 marker left) ∪ blockDictionaries marker address))
      (fun a => Set.mem_union_right _ (Set.mem_union_left _ ⟨a, rfl⟩))
      (fun g hg => Set.mem_union_right _ (Set.mem_union_right _ hg)) (tables j)
    simpa [q, tables, address, left, right, index.injective.extend_apply,
      Fin.append_castAdd_natAdd] using h
  simpa [bound, q, B, Nat.add_assoc] using
    (hleft.union hdictionaries).trans (Synthesis.family _ _ hsection)

end Cslib.Circuits.Full.Lupanov
