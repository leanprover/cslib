/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Circuit.Complexity
public import Cslib.Foundations.Data.BitString
public import Mathlib.Computability.Language

/-!
# Circuit families and size classes

A circuit has a fixed number of inputs, while the words of a language have every length, so a
language is decided by a family of circuits, one for each input length. The circuit on `n` inputs
only has to handle the words of length `n`, the slice `L.slice n` of the language, and nothing
relates the circuits for different lengths: families are a nonuniform model of computation.

`SIZE I s` is the class of languages decided under `I` by a family whose circuit on `n` inputs has
at most `s n` gates, following [Arora and Barak, Definition 6.2][AroraBarak09]. The bound holds
exactly at every length, not asymptotically. It is stated through the existence of a family rather
than through `complexity`, which is `0` on a slice with no circuit over an incomplete basis and
would let such a language into every size class.

## References

* [S. Arora and B. Barak, *Computational Complexity: A Modern Approach*,
  Section 6.1][AroraBarak09]
-/

@[expose] public section

namespace Language

/-- The words of length `n` in `L`, as a Boolean function of their letters. -/
noncomputable def slice (L : Language Bool) (n : ℕ) : Cslib.BooleanFunction n :=
  open scoped Classical in fun x => decide (List.ofFn x ∈ L)

@[simp] theorem slice_eq_true_iff {L : Language Bool} {n : ℕ} {x : Cslib.BitString n} :
    L.slice n x = true ↔ List.ofFn x ∈ L := by
  simp [slice]

/-- The language whose slice at each length `n` is `f n`. -/
def ofSlices (f : ∀ n, Cslib.BooleanFunction n) : Language Bool :=
  {w | f w.length (fun i => w[i]) = true}

@[simp] theorem slice_ofSlices (f : ∀ n, Cslib.BooleanFunction n) (n : ℕ) :
    (ofSlices f).slice n = f n := by
  funext x
  have h : (⟨_, fun i => (List.ofFn x)[i]⟩ : Σ m, Cslib.BitString m) = ⟨n, x⟩ :=
    List.ofFn_inj'.mp List.ofFn_getElem
  rw [Bool.eq_iff_iff, slice_eq_true_iff]
  exact (congrArg (fun p : Σ m, Cslib.BitString m => f p.1 p.2 = true) h).to_iff

end Language

namespace Cslib.Circuits

universe v

variable {σ : Signature.{v}}

/-- A family of single-output circuits, one for each number of inputs. -/
abbrev CircuitFamily (σ : Signature.{v}) := (n : ℕ) → Circuit σ n 1

/-- A circuit family decides `L` under `I` when, for every `n`, its circuit on `n` inputs
computes the slice of `L` at length `n`. -/
def CircuitFamily.Decides (F : CircuitFamily σ) (I : Interpretation σ Bool)
    (L : Language Bool) : Prop :=
  ∀ n, (F n).Computes I (fun x _ => L.slice n x)

theorem CircuitFamily.decides_iff {F : CircuitFamily σ} {I : Interpretation σ Bool}
    {L : Language Bool} :
    F.Decides I L ↔ ∀ n (x : BitString n), (F n).eval I x 0 = true ↔ List.ofFn x ∈ L := by
  unfold CircuitFamily.Decides
  refine forall_congr' fun n => ?_
  simp only [Circuit.Computes, funext_iff, Fin.forall_fin_one]
  refine forall_congr' fun x => ?_
  rw [← Language.slice_eq_true_iff]
  exact Bool.eq_iff_iff

/-- The languages decided under `I` by a circuit family whose circuit on `n` inputs has at most
`s n` gates. -/
def SIZE (I : Interpretation σ Bool) (s : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∃ F : CircuitFamily σ, F.Decides I L ∧ ∀ n, (F n).size ≤ s n}

variable {I : Interpretation σ Bool} {s : ℕ → ℕ} {L : Language Bool}

theorem SIZE_mono : Monotone (SIZE I) := by
  rintro s₁ s₂ h L ⟨F, hF, hs⟩
  exact ⟨F, hF, fun n => (hs n).trans (h n)⟩

/-- A language is in `SIZE I s` exactly when every slice has extended complexity at most the
bound, so a slice with no circuit keeps the language out of every size class. -/
theorem mem_SIZE_iff_ecomplexity_le :
    L ∈ SIZE I s ↔ ∀ n, ecomplexity I (fun x (_ : Fin 1) => L.slice n x) ≤ s n := by
  refine ⟨fun ⟨F, hF, hs⟩ n => (ecomplexity_le_of_computes (F n) (hF n)).trans ?_, fun h => ?_⟩
  · exact_mod_cast hs n
  · choose F hF hs using fun n => ecomplexity_le_iff.mp (h n)
    exact ⟨F, hF, hs⟩

/-- Over a complete basis, a language is in `SIZE I s` exactly when every slice has complexity
at most the bound. -/
theorem mem_SIZE_iff_complexity_le [I.IsComplete] :
    L ∈ SIZE I s ↔ ∀ n, complexity I (fun x (_ : Fin 1) => L.slice n x) ≤ s n := by
  simp only [mem_SIZE_iff_ecomplexity_le, ← natCast_complexity, ENat.natCast_le_natCast]

end Cslib.Circuits
