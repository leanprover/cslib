/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Full.Blocks
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Finite Lupanov synthesis over the full basis

Split the inputs into `r` section coordinates and `d` data coordinates. For a carrier of
size `q`, place the `q ^ d` data assignments in `B = q ^ d ⌈/⌉ t` blocks of `t` cells,
allowing padding in the last block. Both decoders and the block dictionaries are built
once and shared by all `m` outputs. Each output then assembles one table per section.

`synthesis` assumes the input coordinates, zero, and a nonzero marker are already available.
`bound` counts the additional gates and retains the input split, block size, and gate arity
so callers can choose these parameters to obtain a suitable upper bound.

`exists_circuit` supplies the two constants with two more gates and needs only a finite,
nontrivial carrier. The resulting complexity bounds hold on all inputs or any input promise.

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

/-- The finite Lupanov budget on any finite nontrivial carrier when constants are supplied. -/
theorem synthesis_with_constants [Finite U] [Nontrivial U]
    (hk : 2 ≤ k) (ht : 0 < t) (f : (Fin (r + d) → U) → Fin m → U) :
    Synthesis (fullInterpretation (k := k))
      (inputs (r + d) ∪ Set.range fun u (_ : Fin (r + d) → U) => u)
      (Set.range fun j x => f x j) (bound (Nat.card U) k r d t m) := by
  let := Fintype.ofFinite U
  let : Zero U := ⟨Classical.ofNonempty⟩
  obtain ⟨marker, hm⟩ := exists_ne (0 : U)
  rw [Nat.card_eq_fintype_card]
  exact synthesis hk ht marker hm f
    (Set.mem_union_right _ ⟨0, rfl⟩) (Set.mem_union_right _ ⟨marker, rfl⟩) Set.subset_union_left

/-- Supply zero and a nonzero marker with two gates, then apply the finite Lupanov construction. -/
theorem exists_circuit [Finite U] [Nontrivial U]
    (hk : 2 ≤ k) (ht : 0 < t) (f : (Fin (r + d) → U) → Fin m → U) :
    ∃ c : Circuit (fullSignature k U) (r + d) m, c.Computes fullInterpretation f ∧
      c.size ≤ 2 + bound (Nat.card U) k r d t m := by
  let := Fintype.ofFinite U
  let : Zero U := ⟨Classical.ofNonempty⟩
  obtain ⟨marker, hm⟩ := exists_ne (0 : U)
  have hconstants := (Synthesis.full_const (k := k) (s := inputs (r + d)) (0 : U)).union
    (Synthesis.full_const marker)
  have h := hconstants.trans (synthesis hk ht marker hm f
    (Set.mem_union_right _ (Set.mem_union_left _ rfl))
    (Set.mem_union_right _ (Set.mem_union_right _ rfl)) Set.subset_union_left)
  simpa [Nat.card_eq_fintype_card] using h.exists_circuit_outputs

/-- The finite Lupanov upper bound for gate complexity, including the two constant gates. -/
theorem ecomplexity_le [Finite U] [Nontrivial U]
    (hk : 2 ≤ k) (ht : 0 < t) (f : (Fin (r + d) → U) → Fin m → U) :
    ecomplexity (fullInterpretation (k := k)) f ≤
      (2 + bound (Nat.card U) k r d t m : ℕ) :=
  ecomplexity_le_iff.mpr (exists_circuit hk ht f)

/-- The same upper bound holds on any input promise; the budget uses the ambient input size. -/
theorem ecomplexityOn_le [Finite U] [Nontrivial U] (hk : 2 ≤ k) (ht : 0 < t)
    (S : Set (Fin (r + d) → U)) (f : (Fin (r + d) → U) → Fin m → U) :
    ecomplexityOn (fullInterpretation (k := k)) S f ≤
      (2 + bound (Nat.card U) k r d t m : ℕ) :=
  ecomplexityOn_le_ecomplexity.trans (ecomplexity_le hk ht f)

/-- The natural-valued Lupanov bound; the `k + 2` arity supplies completeness automatically. -/
theorem complexity_le [Finite U] [Nontrivial U] (ht : 0 < t)
    (f : (Fin (r + d) → U) → Fin m → U) :
    complexity (fullInterpretation (k := k + 2)) f ≤
      2 + bound (Nat.card U) (k + 2) r d t m :=
  complexity_le_iff.mpr (exists_circuit (by lia) ht f)

/-- The natural-valued Lupanov bound on any input promise, using the ambient input size. -/
theorem complexityOn_le [Finite U] [Nontrivial U] (ht : 0 < t)
    (S : Set (Fin (r + d) → U)) (f : (Fin (r + d) → U) → Fin m → U) :
    complexityOn (fullInterpretation (k := k + 2)) S f ≤
      2 + bound (Nat.card U) (k + 2) r d t m :=
  complexityOn_le_complexity.trans (complexity_le ht f)

end Cslib.Circuits.Full.Lupanov
