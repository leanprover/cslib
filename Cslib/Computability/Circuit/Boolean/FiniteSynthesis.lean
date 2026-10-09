/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Boolean.Synthesis

/-!
# Circuit synthesis from finite observations

A value is observed through finitely many Boolean features. The `observations` of a family of
values are the indicator functions of its features, and anything determined by the features
costs a number of gates polynomial in their number. Equality with each value of a finite type
is one choice of features. Words and machine configurations use cheaper ones, so that
selecting a tape cell is polynomial in the number of cells without enumerating all tape
contents.
-/

@[expose] public section

namespace Cslib.Circuits

open Boolean

variable {n : ℕ} {s : Set (BooleanFunction n)}
variable {α : Type*} {φ : Type*}

namespace Boolean

/-- The indicator functions of every feature along a family of values. -/
def observations (observe : α → φ → Bool) (f : (Fin n → Bool) → α) : Set (BooleanFunction n) :=
  Set.range fun feature x => observe (f x) feature

variable (observe : α → φ → Bool) (f : (Fin n → Bool) → α)

@[simp] theorem mem_observations {g : BooleanFunction n} :
    g ∈ observations observe f ↔ ∃ feature, (fun x => observe (f x) feature) = g :=
  Set.mem_range

/-- Every feature of an observed family is available. -/
theorem synthesis_observe (feature : φ) :
    Synthesis interpretation (observations observe f) {fun x => observe (f x) feature} 0 :=
  Synthesis.of_mem ⟨feature, rfl⟩

/-- Observe a family of values by synthesizing every feature within a common bound. -/
theorem synthesis_observations [Fintype φ] {cost : ℕ}
    (h : ∀ feature, Synthesis interpretation s {fun x => observe (f x) feature} cost) :
    Synthesis interpretation s (observations observe f) (Fintype.card φ * cost) := by
  simpa [observations] using
    Synthesis.family (fun feature x => observe (f x) feature) (fun _ => cost) h

end Boolean

namespace Synthesis

/-- Evaluate a Boolean predicate by disjoining the indicators of its satisfying values. -/
theorem of_indicators [Fintype α] [DecidableEq α] {f : (Fin n → Bool) → α} {bound : ℕ}
    (op : α → Bool)
    (hf : ∀ a, Synthesis interpretation s {fun x => decide (f x = a)} bound) :
    Synthesis interpretation s {fun x => op (f x)}
      (Fintype.card α * (bound + 1) + 1) := by
  have h := exists_mem (Finset.univ.filter fun a => op a)
    (fun a x => decide (f x = a)) (fun _ => bound) (fun a _ => hf a)
  have hsize : (∑ a ∈ Finset.univ.filter (fun a => op a), (bound + 1)) + 1 ≤
      Fintype.card α * (bound + 1) + 1 := by
    simpa using Nat.add_le_add_right (Nat.mul_le_mul_right (bound + 1)
      (Finset.card_filter_le (Finset.univ : Finset α) (fun a => op a))) 1
  simpa using h.mono_cost hsize

/-- Select one of finitely many computed bits using indicators of a bounded index. -/
theorem select {ι : Type*} [DecidableEq ι] (indices : Finset ι)
    (index : (Fin n → Bool) → ι) (branch : ι → BooleanFunction n) {a b : ℕ}
    (hindex : ∀ x, index x ∈ indices)
    (hi : ∀ i ∈ indices, Synthesis interpretation s {fun x => decide (index x = i)} a)
    (hb : ∀ i ∈ indices, Synthesis interpretation s {branch i} b) :
    Synthesis interpretation s {fun x => branch (index x) x}
      (indices.card * (a + b + 2) + 1) := by
  have h := exists_mem indices (fun i x => decide (index x = i) && branch i x)
    (fun _ => a + b + 1) (fun i hi' => (hi i hi').and (hb i hi'))
  simpa [hindex, Nat.add_assoc] using h

end Synthesis

end Cslib.Circuits
