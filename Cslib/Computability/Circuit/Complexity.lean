/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Composition
public import Cslib.Computability.Circuit.Synthesis
public import Mathlib.Data.ENat.Lattice

/-!
# Circuit complexity

The complexity of a function `F` on a support `S`, written `C^S(F)`, is the least number of gates
in a circuit whose outputs agree with `F` on every input in `S`. The function may have several
values, one for each output of the circuit, and nothing is asked of the circuit outside `S`, so
`C^S(F)` depends only on the restriction of `F` to `S`. The complexity `C(F)` of `F` is its
complexity on all inputs, and the complexity of `F` relative to a function `G`, in
`Cslib.Computability.Circuit.RelativeComplexity`, is a complexity on the graph of `G`.

Over an arbitrary signature and interpretation some functions have no circuit at all, so
`ecomplexityOn I S F` takes values in `ℕ∞`, with `⊤` when no circuit computes `F` on `S`. The
natural number `complexityOn I S F` truncates it, as `Set.ncard` truncates `Set.encard`, and is
the notion of interest over a complete basis, one over which every function has a circuit.

Support complexity obeys a small calculus from which the rules for complexity and relative
complexity follow. It grows with the support and ignores the function outside the support.
Wiring, which only selects, permutes, or duplicates inputs, costs nothing. The composite `H ∘ F`
costs at most the complexity of `F` on `S` plus that of `H` on the image of `S`, and computing two
functions side by side costs at most the sum of their complexities.

See [Jukna, Chapter 1][Jukna2012] for the Boolean case.

## References

* [Stasys Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib.Circuits

universe v u
variable {σ : Signature.{v}} {U : Type u} {n m p : ℕ}

/-- An interpretation is complete when every single-valued function, on every number of inputs,
is computed by some circuit. Since this includes functions of zero inputs, the basis must contain
constants: NAND alone is functionally complete but not complete in this sense. Functions with
several values then have circuits too, built by running circuits for their values side by side. -/
class Interpretation.IsComplete (I : Interpretation σ U) : Prop where
  /-- Every single-valued function has a circuit. -/
  exists_computes_single :
    ∀ {n : ℕ} (f : (Fin n → U) → U), ∃ c : Circuit σ n 1, c.Computes I (fun x _ => f x)

/-- Over a complete basis every function, with any number of values, has a circuit. -/
theorem Interpretation.IsComplete.exists_computes {I : Interpretation σ U} [I.IsComplete] :
    ∀ {n m : ℕ} (F : (Fin n → U) → Fin m → U), ∃ c : Circuit σ n m, c.Computes I F
  | _, 0, _ => ⟨Circuit.wiring σ Fin.elim0, fun _ => funext fun i => i.elim0⟩
  | _, m + 1, F => by
    obtain ⟨c, hc⟩ := exists_computes (I := I) fun x => F x ∘ Fin.castSucc
    obtain ⟨d, hd⟩ := exists_computes_single (I := I) fun x => F x (Fin.last m)
    refine ⟨c.append d, fun x => ?_⟩
    rw [Circuit.eval_append, hc x, hd x]
    funext i
    induction i using Fin.lastCases with
    | last => exact Fin.append_right _ _ 0
    | cast j => exact Fin.append_left _ _ j

/-- The complexity `C^S(F)` of `F` on the support `S`: the least size of a circuit computing `F`
on `S` under `I`, or `⊤` if there is none. -/
noncomputable def ecomplexityOn (I : Interpretation σ U) (S : Set (Fin n → U))
    (F : (Fin n → U) → Fin m → U) : ℕ∞ :=
  ⨅ c : {c : Circuit σ n m // c.ComputesOn I S F}, (c.1.size : ℕ∞)

/-- The complexity of `F` on the support `S` as a natural number, which is `0` when no circuit
computes `F` on `S`. -/
noncomputable def complexityOn (I : Interpretation σ U) (S : Set (Fin n → U))
    (F : (Fin n → U) → Fin m → U) : ℕ :=
  (ecomplexityOn I S F).toNat

/-- The complexity `C(F)` of `F`: its complexity on all inputs. -/
noncomputable def ecomplexity (I : Interpretation σ U) (F : (Fin n → U) → Fin m → U) : ℕ∞ :=
  ecomplexityOn I Set.univ F

/-- The complexity of `F` as a natural number, which is `0` when no circuit computes `F`. -/
noncomputable def complexity (I : Interpretation σ U) (F : (Fin n → U) → Fin m → U) : ℕ :=
  complexityOn I Set.univ F

variable {I : Interpretation σ U} {S T : Set (Fin n → U)} {F F' : (Fin n → U) → Fin m → U}
  {k : ℕ}

/-! ### Complexity on a support -/

theorem ecomplexityOn_le_of_computesOn (c : Circuit σ n m) (hc : c.ComputesOn I S F) :
    ecomplexityOn I S F ≤ c.size :=
  iInf_le (fun c : {c : Circuit σ n m // c.ComputesOn I S F} => (c.1.size : ℕ∞)) ⟨c, hc⟩

theorem ecomplexityOn_ne_top_iff :
    ecomplexityOn I S F ≠ ⊤ ↔ ∃ c : Circuit σ n m, c.ComputesOn I S F := by
  rw [ecomplexityOn, ENat.iInf_natCast_ne_top, nonempty_subtype]

/-- When some circuit computes `F` on `S`, the least size is attained. -/
theorem exists_computesOn_size_eq_ecomplexityOn (h : ∃ c : Circuit σ n m, c.ComputesOn I S F) :
    ∃ c : Circuit σ n m, c.ComputesOn I S F ∧ (c.size : ℕ∞) = ecomplexityOn I S F := by
  have : Nonempty {c : Circuit σ n m // c.ComputesOn I S F} := nonempty_subtype.mpr h
  obtain ⟨⟨c, hc⟩, hmin⟩ := ENat.exists_eq_iInf
    (fun c : {c : Circuit σ n m // c.ComputesOn I S F} => (c.1.size : ℕ∞))
  exact ⟨c, hc, hmin⟩

theorem ecomplexityOn_le_iff :
    ecomplexityOn I S F ≤ k ↔ ∃ c : Circuit σ n m, c.ComputesOn I S F ∧ c.size ≤ k := by
  constructor
  · intro h
    have hne : ecomplexityOn I S F ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top k) h
    obtain ⟨c, hc, hsize⟩ :=
      exists_computesOn_size_eq_ecomplexityOn (ecomplexityOn_ne_top_iff.mp hne)
    exact ⟨c, hc, by exact_mod_cast hsize.trans_le h⟩
  · rintro ⟨c, hc, hk⟩
    exact (ecomplexityOn_le_of_computesOn c hc).trans (by exact_mod_cast hk)

/-- A larger support is harder to compute on. -/
theorem ecomplexityOn_mono (h : S ⊆ T) : ecomplexityOn I S F ≤ ecomplexityOn I T F :=
  le_iInf fun c => iInf_le_of_le ⟨c.1, fun x hx => c.2 x (h hx)⟩ le_rfl

/-- Complexity on a support depends only on the values of the function on the support. -/
theorem ecomplexityOn_congr (h : Set.EqOn F F' S) : ecomplexityOn I S F = ecomplexityOn I S F' := by
  have hc (c : Circuit σ n m) : c.ComputesOn I S F ↔ c.ComputesOn I S F' :=
    forall₂_congr fun x hx => by rw [h hx]
  apply le_antisymm
  · exact le_iInf fun c => iInf_le_of_le ⟨c.1, (hc c.1).mpr c.2⟩ le_rfl
  · exact le_iInf fun c => iInf_le_of_le ⟨c.1, (hc c.1).mp c.2⟩ le_rfl

theorem ecomplexityOn_le_ecomplexity : ecomplexityOn I S F ≤ ecomplexity I F :=
  ecomplexityOn_mono (Set.subset_univ S)

/-- Selecting, permuting, or duplicating inputs costs nothing. -/
@[simp] theorem ecomplexityOn_wiring (select : Fin m → Fin n) :
    ecomplexityOn I S (fun x => x ∘ select) = 0 :=
  nonpos_iff_eq_zero.mp <| (ecomplexityOn_le_of_computesOn _
    ((Circuit.wiring_computes select I).computesOn S)).trans (by simp)

/-- The composition rule: computing `H ∘ F` on `S` costs at most computing `F` on `S` and then
`H` on the values `F` takes there. -/
theorem ecomplexityOn_comp_le (F : (Fin n → U) → Fin m → U) (H : (Fin m → U) → Fin p → U) :
    ecomplexityOn I S (H ∘ F) ≤ ecomplexityOn I S F + ecomplexityOn I (F '' S) H := by
  by_cases hF : ecomplexityOn I S F = ⊤
  · simp [hF]
  by_cases hH : ecomplexityOn I (F '' S) H = ⊤
  · simp [hH]
  obtain ⟨c, hc, hcs⟩ := exists_computesOn_size_eq_ecomplexityOn (ecomplexityOn_ne_top_iff.mp hF)
  obtain ⟨d, hd, hds⟩ := exists_computesOn_size_eq_ecomplexityOn (ecomplexityOn_ne_top_iff.mp hH)
  refine (ecomplexityOn_le_of_computesOn _ (hc.comp hd)).trans_eq ?_
  rw [← hcs, ← hds, Circuit.size_comp, Nat.cast_add]

/-- The pairing rule: computing `F` and `G` side by side on `S` costs at most the sum of their
complexities on `S`. -/
theorem ecomplexityOn_append_le (F : (Fin n → U) → Fin m → U) (G : (Fin n → U) → Fin p → U) :
    ecomplexityOn I S (fun x => Fin.append (F x) (G x)) ≤
      ecomplexityOn I S F + ecomplexityOn I S G := by
  by_cases hF : ecomplexityOn I S F = ⊤
  · simp [hF]
  by_cases hG : ecomplexityOn I S G = ⊤
  · simp [hG]
  obtain ⟨c, hc, hcs⟩ := exists_computesOn_size_eq_ecomplexityOn (ecomplexityOn_ne_top_iff.mp hF)
  obtain ⟨d, hd, hds⟩ := exists_computesOn_size_eq_ecomplexityOn (ecomplexityOn_ne_top_iff.mp hG)
  refine (ecomplexityOn_le_of_computesOn _ (hc.append hd)).trans_eq ?_
  rw [← hcs, ← hds, Circuit.size_append, Nat.cast_add]

/-- Reading the inputs through a wiring costs nothing beyond computing `F` on the rewired
support. -/
theorem ecomplexityOn_comp_wiring_le {S : Set (Fin p → U)} (select : Fin n → Fin p)
    (F : (Fin n → U) → Fin m → U) :
    ecomplexityOn I S (fun x => F (x ∘ select)) ≤ ecomplexityOn I ((· ∘ select) '' S) F := by
  have h := ecomplexityOn_comp_le (I := I) (S := S) (fun x => x ∘ select) F
  rw [ecomplexityOn_wiring, zero_add] at h
  exact h

/-- Selecting, permuting, or duplicating the values of `F` costs nothing. -/
theorem ecomplexityOn_wiring_comp_le (select : Fin p → Fin m) (F : (Fin n → U) → Fin m → U) :
    ecomplexityOn I S (fun x => F x ∘ select) ≤ ecomplexityOn I S F := by
  have h := ecomplexityOn_comp_le (I := I) (S := S) F (fun y => y ∘ select)
  rw [ecomplexityOn_wiring, add_zero] at h
  exact h

/-! ### Complexity on all inputs -/

theorem ecomplexity_le_of_computes (c : Circuit σ n m) (hc : c.Computes I F) :
    ecomplexity I F ≤ c.size :=
  ecomplexityOn_le_of_computesOn c (hc.computesOn _)

theorem ecomplexity_ne_top_iff : ecomplexity I F ≠ ⊤ ↔ ∃ c : Circuit σ n m, c.Computes I F := by
  simp [ecomplexity, ecomplexityOn_ne_top_iff]

/-- When some circuit computes `F`, the least size is attained. -/
theorem exists_computes_size_eq_ecomplexity (h : ∃ c : Circuit σ n m, c.Computes I F) :
    ∃ c : Circuit σ n m, c.Computes I F ∧ (c.size : ℕ∞) = ecomplexity I F := by
  simpa [ecomplexity] using
    exists_computesOn_size_eq_ecomplexityOn (S := Set.univ) (by simpa using h)

theorem ecomplexity_le_iff :
    ecomplexity I F ≤ k ↔ ∃ c : Circuit σ n m, c.Computes I F ∧ c.size ≤ k := by
  simp [ecomplexity, ecomplexityOn_le_iff]

theorem natCast_complexity_of_exists (h : ∃ c : Circuit σ n m, c.Computes I F) :
    (complexity I F : ℕ∞) = ecomplexity I F :=
  ENat.natCast_toNat (ecomplexity_ne_top_iff.mpr h)

theorem complexity_le_of_computes (c : Circuit σ n m) (hc : c.Computes I F) :
    complexity I F ≤ c.size :=
  ENat.toNat_le_of_le_natCast (ecomplexity_le_of_computes c hc)

/-- A lower bound on the complexity is a lower bound on the size of every circuit. -/
theorem le_size_of_le_complexity (h : k ≤ complexity I F) {c : Circuit σ n m}
    (hc : c.Computes I F) : k ≤ c.size :=
  h.trans (complexity_le_of_computes c hc)

theorem ecomplexity_comp_le (F : (Fin n → U) → Fin m → U) (H : (Fin m → U) → Fin p → U) :
    ecomplexity I (H ∘ F) ≤ ecomplexity I F + ecomplexity I H :=
  (ecomplexityOn_comp_le F H).trans (add_le_add le_rfl ecomplexityOn_le_ecomplexity)

theorem ecomplexity_append_le (F : (Fin n → U) → Fin m → U) (G : (Fin n → U) → Fin p → U) :
    ecomplexity I (fun x => Fin.append (F x) (G x)) ≤ ecomplexity I F + ecomplexity I G :=
  ecomplexityOn_append_le F G

/-- Computing `F` alongside `G` is at least as hard as computing `F`. -/
theorem ecomplexity_le_ecomplexity_append_left (F : (Fin n → U) → Fin m → U)
    (G : (Fin n → U) → Fin p → U) :
    ecomplexity I F ≤ ecomplexity I (fun x => Fin.append (F x) (G x)) := by
  have h := ecomplexityOn_wiring_comp_le (I := I) (S := Set.univ) (Fin.castAdd p)
    (fun x => Fin.append (F x) (G x))
  simp only [Fin.append_comp_castAdd] at h
  exact h

/-- Computing `G` alongside `F` is at least as hard as computing `G`. -/
theorem ecomplexity_le_ecomplexity_append_right (F : (Fin n → U) → Fin m → U)
    (G : (Fin n → U) → Fin p → U) :
    ecomplexity I G ≤ ecomplexity I (fun x => Fin.append (F x) (G x)) := by
  have h := ecomplexityOn_wiring_comp_le (I := I) (S := Set.univ) (Fin.natAdd m)
    (fun x => Fin.append (F x) (G x))
  simp only [Fin.append_comp_natAdd] at h
  exact h

/-- A synthesis bound on the input projections bounds the extended complexity. -/
theorem Synthesis.ecomplexity_le {f : (Fin n → U) → U} {cost : ℕ}
    (h : Synthesis I (inputs n) {f} cost) : ecomplexity I (fun x (_ : Fin 1) => f x) ≤ cost :=
  ecomplexity_le_iff.mpr h.exists_circuit

/-- A synthesis bound on the input projections bounds the complexity, with no completeness
assumption. -/
theorem Synthesis.complexity_le {f : (Fin n → U) → U} {cost : ℕ}
    (h : Synthesis I (inputs n) {f} cost) : complexity I (fun x (_ : Fin 1) => f x) ≤ cost :=
  ENat.toNat_le_of_le_natCast h.ecomplexity_le

/-! ### Over a complete basis -/

section Complete

variable [I.IsComplete]

theorem ecomplexityOn_ne_top : ecomplexityOn I S F ≠ ⊤ :=
  ecomplexityOn_ne_top_iff.mpr <|
    (Interpretation.IsComplete.exists_computes F).imp fun _ hc => hc.computesOn S

@[simp] theorem natCast_complexityOn : (complexityOn I S F : ℕ∞) = ecomplexityOn I S F :=
  ENat.natCast_toNat ecomplexityOn_ne_top

theorem ecomplexity_ne_top : ecomplexity I F ≠ ⊤ :=
  ecomplexityOn_ne_top

@[simp] theorem natCast_complexity : (complexity I F : ℕ∞) = ecomplexity I F :=
  natCast_complexityOn

/-- Over a complete basis the least size is attained. -/
theorem exists_computes_size_eq_complexity :
    ∃ c : Circuit σ n m, c.Computes I F ∧ c.size = complexity I F := by
  obtain ⟨c, hc, hsize⟩ :=
    exists_computes_size_eq_ecomplexity (Interpretation.IsComplete.exists_computes (I := I) F)
  exact ⟨c, hc, by exact_mod_cast hsize.trans (natCast_complexity (I := I) (F := F)).symm⟩

theorem complexity_le_iff :
    complexity I F ≤ k ↔ ∃ c : Circuit σ n m, c.Computes I F ∧ c.size ≤ k := by
  rw [← ecomplexity_le_iff, ← natCast_complexity (I := I) (F := F)]
  exact_mod_cast Iff.rfl

/-- Over a complete basis, lower bounds on complexity are exactly lower bounds on the size
of every circuit. -/
theorem le_complexity_iff :
    k ≤ complexity I F ↔ ∀ c : Circuit σ n m, c.Computes I F → k ≤ c.size := by
  refine ⟨fun h _ hc => le_size_of_le_complexity h hc, fun h => ?_⟩
  obtain ⟨c, hc, hsize⟩ := exists_computes_size_eq_complexity (I := I) (F := F)
  exact hsize ▸ h c hc

theorem complexityOn_mono (h : S ⊆ T) : complexityOn I S F ≤ complexityOn I T F := by
  have := ecomplexityOn_mono (I := I) (F := F) h
  rw [← natCast_complexityOn, ← natCast_complexityOn] at this
  exact_mod_cast this

theorem complexityOn_comp_le (F : (Fin n → U) → Fin m → U) (H : (Fin m → U) → Fin p → U) :
    complexityOn I S (H ∘ F) ≤ complexityOn I S F + complexityOn I (F '' S) H := by
  have := ecomplexityOn_comp_le (I := I) (S := S) F H
  rw [← natCast_complexityOn, ← natCast_complexityOn, ← natCast_complexityOn] at this
  exact_mod_cast this

theorem complexityOn_append_le (F : (Fin n → U) → Fin m → U) (G : (Fin n → U) → Fin p → U) :
    complexityOn I S (fun x => Fin.append (F x) (G x)) ≤
      complexityOn I S F + complexityOn I S G := by
  have := ecomplexityOn_append_le (I := I) (S := S) F G
  rw [← natCast_complexityOn, ← natCast_complexityOn, ← natCast_complexityOn] at this
  exact_mod_cast this

end Complete

end Cslib.Circuits
