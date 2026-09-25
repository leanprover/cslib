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

The complexity of a function `f` on a support `S`, written `C^S(f)`, is the least number of gates
in a circuit whose outputs agree with `f` on every input in `S`. The function may have several
values, one for each output of the circuit, and nothing is asked of the circuit outside `S`, so
`C^S(f)` depends only on the restriction of `f` to `S`. The complexity `C(f)` of `f` is its
complexity on all inputs, and the complexity of `f` relative to a function `g`, in
`Cslib.Computability.Circuit.RelativeComplexity`, is a complexity on the graph of `g`.

Over an arbitrary signature and interpretation some functions have no circuit at all, so
`ecomplexityOn I S f` takes values in `ℕ∞`, with `⊤` when no circuit computes `f` on `S`. The
natural number `complexityOn I S f` truncates it, as `Set.ncard` truncates `Set.encard`, and is
the notion of interest over a complete basis, one over which every function has a circuit.

Support complexity obeys a small calculus from which the rules for complexity and relative
complexity follow. It grows with the support and ignores the function outside the support.
Wiring, which only selects, permutes, or duplicates inputs, costs nothing. The composite `g ∘ f`
costs at most the complexity of `f` on `S` plus that of `g` on the image of `S`, and computing two
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
    ∀ {n m : ℕ} (f : (Fin n → U) → Fin m → U), ∃ c : Circuit σ n m, c.Computes I f
  | _, 0, _ => ⟨Circuit.wiring σ Fin.elim0, fun _ => funext fun i => i.elim0⟩
  | _, m + 1, f => by
    obtain ⟨c, hc⟩ := exists_computes (I := I) fun x => f x ∘ Fin.castSucc
    obtain ⟨d, hd⟩ := exists_computes_single (I := I) fun x => f x (Fin.last m)
    refine ⟨c.append d, fun x => ?_⟩
    rw [Circuit.eval_append, hc x, hd x]
    funext i
    induction i using Fin.lastCases with
    | last => exact Fin.append_right _ _ 0
    | cast j => exact Fin.append_left _ _ j

/-- The complexity `C^S(f)` of `f` on the support `S`: the least size of a circuit computing `f`
on `S` under `I`, or `⊤` if there is none. -/
noncomputable def ecomplexityOn (I : Interpretation σ U) (S : Set (Fin n → U))
    (f : (Fin n → U) → Fin m → U) : ℕ∞ :=
  ⨅ c : {c : Circuit σ n m // c.ComputesOn I S f}, (c.1.size : ℕ∞)

/-- The complexity of `f` on the support `S` as a natural number, which is `0` when no circuit
computes `f` on `S`. -/
noncomputable def complexityOn (I : Interpretation σ U) (S : Set (Fin n → U))
    (f : (Fin n → U) → Fin m → U) : ℕ :=
  (ecomplexityOn I S f).toNat

/-- The complexity `C(f)` of `f`: its complexity on all inputs. -/
noncomputable def ecomplexity (I : Interpretation σ U) (f : (Fin n → U) → Fin m → U) : ℕ∞ :=
  ecomplexityOn I Set.univ f

/-- The complexity of `f` as a natural number, which is `0` when no circuit computes `f`. -/
noncomputable def complexity (I : Interpretation σ U) (f : (Fin n → U) → Fin m → U) : ℕ :=
  complexityOn I Set.univ f

variable {I : Interpretation σ U} {S T : Set (Fin n → U)} {f f' : (Fin n → U) → Fin m → U}
  {k : ℕ}

/-! ### Complexity on a support -/

theorem ecomplexityOn_le_of_computesOn (c : Circuit σ n m) (hc : c.ComputesOn I S f) :
    ecomplexityOn I S f ≤ c.size :=
  iInf_le (fun c : {c : Circuit σ n m // c.ComputesOn I S f} => (c.1.size : ℕ∞)) ⟨c, hc⟩

theorem ecomplexityOn_ne_top_iff :
    ecomplexityOn I S f ≠ ⊤ ↔ ∃ c : Circuit σ n m, c.ComputesOn I S f := by
  rw [ecomplexityOn, ENat.iInf_natCast_ne_top, nonempty_subtype]

/-- When some circuit computes `f` on `S`, the least size is attained. -/
theorem exists_computesOn_size_eq_ecomplexityOn (h : ∃ c : Circuit σ n m, c.ComputesOn I S f) :
    ∃ c : Circuit σ n m, c.ComputesOn I S f ∧ (c.size : ℕ∞) = ecomplexityOn I S f := by
  have : Nonempty {c : Circuit σ n m // c.ComputesOn I S f} := nonempty_subtype.mpr h
  obtain ⟨⟨c, hc⟩, hmin⟩ := ENat.exists_eq_iInf
    (fun c : {c : Circuit σ n m // c.ComputesOn I S f} => (c.1.size : ℕ∞))
  exact ⟨c, hc, hmin⟩

theorem ecomplexityOn_le_iff :
    ecomplexityOn I S f ≤ k ↔ ∃ c : Circuit σ n m, c.ComputesOn I S f ∧ c.size ≤ k := by
  constructor
  · intro h
    have hne : ecomplexityOn I S f ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top k) h
    obtain ⟨c, hc, hsize⟩ :=
      exists_computesOn_size_eq_ecomplexityOn (ecomplexityOn_ne_top_iff.mp hne)
    exact ⟨c, hc, by exact_mod_cast hsize.trans_le h⟩
  · rintro ⟨c, hc, hk⟩
    exact (ecomplexityOn_le_of_computesOn c hc).trans (by exact_mod_cast hk)

/-- A larger support is harder to compute on. -/
theorem ecomplexityOn_mono (h : S ⊆ T) : ecomplexityOn I S f ≤ ecomplexityOn I T f :=
  le_iInf fun c => iInf_le_of_le ⟨c.1, c.2.mono h⟩ le_rfl

/-- Complexity on a support depends only on the values of the function on the support. -/
theorem ecomplexityOn_congr (h : Set.EqOn f f' S) : ecomplexityOn I S f = ecomplexityOn I S f' :=
  le_antisymm (le_iInf fun c => iInf_le_of_le ⟨c.1, c.2.trans h.symm⟩ le_rfl)
    (le_iInf fun c => iInf_le_of_le ⟨c.1, c.2.trans h⟩ le_rfl)

theorem ecomplexityOn_le_ecomplexity : ecomplexityOn I S f ≤ ecomplexity I f :=
  ecomplexityOn_mono (Set.subset_univ S)

/-- Selecting, permuting, or duplicating inputs costs nothing. -/
@[simp] theorem ecomplexityOn_wiring (select : Fin m → Fin n) :
    ecomplexityOn I S (fun x => x ∘ select) = 0 :=
  nonpos_iff_eq_zero.mp <| (ecomplexityOn_le_of_computesOn _
    ((Circuit.wiring_computes select I).computesOn S)).trans (by simp)

/-- The composition rule: computing `g ∘ f` on `S` costs at most computing `f` on `S` and then
`g` on the values `f` takes there. -/
theorem ecomplexityOn_comp_le (f : (Fin n → U) → Fin m → U) (g : (Fin m → U) → Fin p → U) :
    ecomplexityOn I S (g ∘ f) ≤ ecomplexityOn I S f + ecomplexityOn I (f '' S) g := by
  by_cases hF : ecomplexityOn I S f = ⊤
  · simp [hF]
  by_cases hH : ecomplexityOn I (f '' S) g = ⊤
  · simp [hH]
  obtain ⟨c, hc, hcs⟩ := exists_computesOn_size_eq_ecomplexityOn (ecomplexityOn_ne_top_iff.mp hF)
  obtain ⟨d, hd, hds⟩ := exists_computesOn_size_eq_ecomplexityOn (ecomplexityOn_ne_top_iff.mp hH)
  refine (ecomplexityOn_le_of_computesOn _ (hc.comp hd)).trans_eq ?_
  rw [← hcs, ← hds, Circuit.size_comp, Nat.cast_add]

/-- The pairing rule: computing `f` and `g` side by side on `S` costs at most the sum of their
complexities on `S`. -/
theorem ecomplexityOn_append_le (f : (Fin n → U) → Fin m → U) (g : (Fin n → U) → Fin p → U) :
    ecomplexityOn I S (fun x => Fin.append (f x) (g x)) ≤
      ecomplexityOn I S f + ecomplexityOn I S g := by
  by_cases hF : ecomplexityOn I S f = ⊤
  · simp [hF]
  by_cases hG : ecomplexityOn I S g = ⊤
  · simp [hG]
  obtain ⟨c, hc, hcs⟩ := exists_computesOn_size_eq_ecomplexityOn (ecomplexityOn_ne_top_iff.mp hF)
  obtain ⟨d, hd, hds⟩ := exists_computesOn_size_eq_ecomplexityOn (ecomplexityOn_ne_top_iff.mp hG)
  refine (ecomplexityOn_le_of_computesOn _ (hc.append hd)).trans_eq ?_
  rw [← hcs, ← hds, Circuit.size_append, Nat.cast_add]

/-- Reading the inputs through a wiring costs nothing beyond computing `f` on the rewired
support. -/
theorem ecomplexityOn_comp_wiring_le {S : Set (Fin p → U)} (select : Fin n → Fin p)
    (f : (Fin n → U) → Fin m → U) :
    ecomplexityOn I S (fun x => f (x ∘ select)) ≤ ecomplexityOn I ((· ∘ select) '' S) f := by
  have h := ecomplexityOn_comp_le (I := I) (S := S) (fun x => x ∘ select) f
  rw [ecomplexityOn_wiring, zero_add] at h
  exact h

/-- Selecting, permuting, or duplicating the values of `f` costs nothing. -/
theorem ecomplexityOn_wiring_comp_le (select : Fin p → Fin m) (f : (Fin n → U) → Fin m → U) :
    ecomplexityOn I S (fun x => f x ∘ select) ≤ ecomplexityOn I S f := by
  have h := ecomplexityOn_comp_le (I := I) (S := S) f (fun y => y ∘ select)
  rw [ecomplexityOn_wiring, add_zero] at h
  exact h

/-! ### Complexity on all inputs -/

theorem ecomplexity_le_of_computes (c : Circuit σ n m) (hc : c.Computes I f) :
    ecomplexity I f ≤ c.size :=
  ecomplexityOn_le_of_computesOn c (hc.computesOn _)

theorem ecomplexity_ne_top_iff : ecomplexity I f ≠ ⊤ ↔ ∃ c : Circuit σ n m, c.Computes I f := by
  simp [ecomplexity, ecomplexityOn_ne_top_iff]

/-- When some circuit computes `f`, the least size is attained. -/
theorem exists_computes_size_eq_ecomplexity (h : ∃ c : Circuit σ n m, c.Computes I f) :
    ∃ c : Circuit σ n m, c.Computes I f ∧ (c.size : ℕ∞) = ecomplexity I f := by
  simpa [ecomplexity] using
    exists_computesOn_size_eq_ecomplexityOn (S := Set.univ) (by simpa using h)

theorem ecomplexity_le_iff :
    ecomplexity I f ≤ k ↔ ∃ c : Circuit σ n m, c.Computes I f ∧ c.size ≤ k := by
  simp [ecomplexity, ecomplexityOn_le_iff]

theorem natCast_complexity_of_exists (h : ∃ c : Circuit σ n m, c.Computes I f) :
    (complexity I f : ℕ∞) = ecomplexity I f :=
  ENat.natCast_toNat (ecomplexity_ne_top_iff.mpr h)

theorem complexity_le_of_computes (c : Circuit σ n m) (hc : c.Computes I f) :
    complexity I f ≤ c.size :=
  ENat.toNat_le_of_le_natCast (ecomplexity_le_of_computes c hc)

/-- A lower bound on the complexity is a lower bound on the size of every circuit. -/
theorem le_size_of_le_complexity (h : k ≤ complexity I f) {c : Circuit σ n m}
    (hc : c.Computes I f) : k ≤ c.size :=
  h.trans (complexity_le_of_computes c hc)

theorem ecomplexity_comp_le (f : (Fin n → U) → Fin m → U) (g : (Fin m → U) → Fin p → U) :
    ecomplexity I (g ∘ f) ≤ ecomplexity I f + ecomplexity I g :=
  (ecomplexityOn_comp_le f g).trans (add_le_add le_rfl ecomplexityOn_le_ecomplexity)

theorem ecomplexity_append_le (f : (Fin n → U) → Fin m → U) (g : (Fin n → U) → Fin p → U) :
    ecomplexity I (fun x => Fin.append (f x) (g x)) ≤ ecomplexity I f + ecomplexity I g :=
  ecomplexityOn_append_le f g

/-- Computing `f` alongside `g` is at least as hard as computing `f`. -/
theorem ecomplexity_le_ecomplexity_append_left (f : (Fin n → U) → Fin m → U)
    (g : (Fin n → U) → Fin p → U) :
    ecomplexity I f ≤ ecomplexity I (fun x => Fin.append (f x) (g x)) := by
  have h := ecomplexityOn_wiring_comp_le (I := I) (S := Set.univ) (Fin.castAdd p)
    (fun x => Fin.append (f x) (g x))
  simp only [Fin.append_comp_castAdd] at h
  exact h

/-- Computing `g` alongside `f` is at least as hard as computing `g`. -/
theorem ecomplexity_le_ecomplexity_append_right (f : (Fin n → U) → Fin m → U)
    (g : (Fin n → U) → Fin p → U) :
    ecomplexity I g ≤ ecomplexity I (fun x => Fin.append (f x) (g x)) := by
  have h := ecomplexityOn_wiring_comp_le (I := I) (S := Set.univ) (Fin.natAdd m)
    (fun x => Fin.append (f x) (g x))
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

theorem ecomplexityOn_ne_top : ecomplexityOn I S f ≠ ⊤ :=
  ecomplexityOn_ne_top_iff.mpr <|
    (Interpretation.IsComplete.exists_computes f).imp fun _ hc => hc.computesOn S

@[simp] theorem natCast_complexityOn : (complexityOn I S f : ℕ∞) = ecomplexityOn I S f :=
  ENat.natCast_toNat ecomplexityOn_ne_top

theorem ecomplexity_ne_top : ecomplexity I f ≠ ⊤ :=
  ecomplexityOn_ne_top

@[simp] theorem natCast_complexity : (complexity I f : ℕ∞) = ecomplexity I f :=
  natCast_complexityOn

/-- Over a complete basis the least size is attained. -/
theorem exists_computes_size_eq_complexity :
    ∃ c : Circuit σ n m, c.Computes I f ∧ c.size = complexity I f := by
  obtain ⟨c, hc, hsize⟩ :=
    exists_computes_size_eq_ecomplexity (Interpretation.IsComplete.exists_computes (I := I) f)
  exact ⟨c, hc, by exact_mod_cast hsize.trans (natCast_complexity (I := I) (f := f)).symm⟩

theorem complexity_le_iff :
    complexity I f ≤ k ↔ ∃ c : Circuit σ n m, c.Computes I f ∧ c.size ≤ k := by
  rw [← ecomplexity_le_iff, ← natCast_complexity (I := I) (f := f)]
  exact_mod_cast Iff.rfl

/-- Over a complete basis, lower bounds on complexity are exactly lower bounds on the size
of every circuit. -/
theorem le_complexity_iff :
    k ≤ complexity I f ↔ ∀ c : Circuit σ n m, c.Computes I f → k ≤ c.size := by
  refine ⟨fun h _ hc => le_size_of_le_complexity h hc, fun h => ?_⟩
  obtain ⟨c, hc, hsize⟩ := exists_computes_size_eq_complexity (I := I) (f := f)
  exact hsize ▸ h c hc

theorem complexityOn_mono (h : S ⊆ T) : complexityOn I S f ≤ complexityOn I T f := by
  have := ecomplexityOn_mono (I := I) (f := f) h
  rw [← natCast_complexityOn, ← natCast_complexityOn] at this
  exact_mod_cast this

theorem complexityOn_comp_le (f : (Fin n → U) → Fin m → U) (g : (Fin m → U) → Fin p → U) :
    complexityOn I S (g ∘ f) ≤ complexityOn I S f + complexityOn I (f '' S) g := by
  have := ecomplexityOn_comp_le (I := I) (S := S) f g
  rw [← natCast_complexityOn, ← natCast_complexityOn, ← natCast_complexityOn] at this
  exact_mod_cast this

theorem complexityOn_append_le (f : (Fin n → U) → Fin m → U) (g : (Fin n → U) → Fin p → U) :
    complexityOn I S (fun x => Fin.append (f x) (g x)) ≤
      complexityOn I S f + complexityOn I S g := by
  have := ecomplexityOn_append_le (I := I) (S := S) f g
  rw [← natCast_complexityOn, ← natCast_complexityOn, ← natCast_complexityOn] at this
  exact_mod_cast this

end Complete

end Cslib.Circuits
