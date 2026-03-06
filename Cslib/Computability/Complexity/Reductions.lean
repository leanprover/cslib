/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Complexity.Classes.Time

@[expose] public section

/-!
# Polynomial-Time Reductions and NP-Completeness

This file defines polynomial-time many-one reductions between languages,
and uses them to define NP-hardness and NP-completeness.

## Main Definitions

* `PolyTimeReduces L₁ L₂` — `L₁` poly-time reduces to `L₂`
* `NPHard L` — every NP language poly-time reduces to `L`
* `NPComplete L` — `L` is NP-hard and in NP

## Main Results

* `PolyTimeReduces.refl` — reflexivity
* `PolyTimeReduces.trans` — transitivity
* `PolyTimeReduces.mem_P` — downward closure under P
* `NPHard.p_eq_np` — if any NP-hard language is in P then P = NP

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraB2009]
-/

open Turing SingleTapeTM

variable {Symbol : Type}

namespace Cslib.Complexity

/--
A language `L₁` **polynomial-time reduces** to `L₂` if there exists a
polynomial-time computable function `f` such that
for all `x`, `x ∈ L₁ ↔ f x ∈ L₂`.

This is also called a **many-one** or **Karp** reduction.
-/
def PolyTimeReduces (L₁ L₂ : Set (List Symbol)) : Prop :=
  ∃ f, Nonempty (PolyTimeComputable f) ∧ ∀ x, x ∈ L₁ ↔ f x ∈ L₂

/--
A language `L` is **NP-hard** if every language in NP polynomial-time
reduces to `L`.
-/
def NPHard (L : Set (List Symbol)) : Prop :=
  ∀ L' ∈ NP (Symbol := Symbol), PolyTimeReduces L' L

/--
A language `L` is **NP-complete** if it is NP-hard and in NP.
-/
def NPComplete (L : Set (List Symbol)) : Prop :=
  NPHard L ∧ L ∈ NP

end Cslib.Complexity

end

open Turing SingleTapeTM Cslib.Complexity

variable {Symbol : Type}

namespace Cslib.Complexity

/-- `≤ₚ` is reflexive: every language reduces to itself via the identity. -/
theorem PolyTimeReduces.refl
    [Inhabited Symbol]
    [Finite Symbol]
    (L : Set (List Symbol)) : PolyTimeReduces L L :=
  let _ : Fintype Symbol := Fintype.ofFinite Symbol
  ⟨id, ⟨PolyTimeComputable.id⟩, fun _ => Iff.rfl⟩

/-- `≤ₚ` is transitive: if `L₁ ≤ₚ L₂` and `L₂ ≤ₚ L₃` then `L₁ ≤ₚ L₃`. -/
theorem PolyTimeReduces.trans
    {L₁ L₂ L₃ : Set (List Symbol)}
    (h₁₂ : PolyTimeReduces L₁ L₂)
    (h₂₃ : PolyTimeReduces L₂ L₃) :
    PolyTimeReduces L₁ L₃ := by
  obtain ⟨f, ⟨hf⟩, hf_mem⟩ := h₁₂
  obtain ⟨g, ⟨hg⟩, hg_mem⟩ := h₂₃
  let _ : Inhabited Symbol := hf.toTimeComputable.tm.SymbolInhabited
  let _ : Fintype Symbol := hf.toTimeComputable.tm.SymbolFintype
  exact ⟨g ∘ f, ⟨hf.comp hg⟩,
    fun x => (hf_mem x).trans (hg_mem (f x))⟩

/-- If `L₁ ≤ₚ L₂` and `L₂ ∈ P` then `L₁ ∈ P`. -/
theorem PolyTimeReduces.mem_P
    {L₁ L₂ : Set (List Symbol)}
    (hred : PolyTimeReduces L₁ L₂)
    (hL₂ : L₂ ∈ P (Symbol := Symbol)) :
    L₁ ∈ P := by
  obtain ⟨f, ⟨hf⟩, hf_mem⟩ := hred
  obtain ⟨g, ⟨hg⟩, hg_dec⟩ := hL₂
  let _ : Inhabited Symbol := hf.toTimeComputable.tm.SymbolInhabited
  let _ : Fintype Symbol := hf.toTimeComputable.tm.SymbolFintype
  refine ⟨g ∘ f, ⟨hf.comp hg⟩, fun x => ?_⟩
  simp only [Function.comp]
  exact (hf_mem x).trans (hg_dec (f x))

/-- If any NP-hard language is in P, then P = NP.

This is the fundamental theorem connecting NP-completeness to the
P vs NP question. -/
theorem NPHard.p_eq_np
    {L : Set (List Symbol)}
    (hL : NPHard L)
    (hP : L ∈ P (Symbol := Symbol)) :
    P (Symbol := Symbol) = NP := by
  apply Set.eq_of_subset_of_subset
  · exact P_subset_NP
  · intro L' hL'
    exact (hL L' hL').mem_P hP

end Cslib.Complexity
