/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Boolean.Basic
public import Cslib.Computability.Circuit.Synthesis
public import Mathlib.Data.Fintype.Card

/-!
# Boolean synthesis

The generic synthesis rules specialize to the De Morgan basis: constants, negation, conjunction,
and disjunction. Finite conjunctions and disjunctions use the generic fold bound, and
`synthesis_minterm` combines literals to test a specified tuple of input bits.
-/

@[expose] public section

namespace Cslib.Circuits

open Boolean

universe u
variable {n : ℕ} {ι : Type u}

namespace Synthesis

variable {s : Set (BooleanFunction n)} {a b : ℕ} {f g : BooleanFunction n}

/-- Constants cost one gate. -/
theorem const (value : Bool) : Synthesis interpretation s {fun _ => value} 1 :=
  nullary (I := interpretation) (.const value) rfl

/-- Apply negation to a synthesized function. -/
theorem not (h : Synthesis interpretation s {f} a) :
    Synthesis interpretation s {fun x => !f x} (a + 1) :=
  h.unary .not

/-- Binary conjunction costs one gate beyond its arguments. -/
theorem and (hf : Synthesis interpretation s {f} a) (hg : Synthesis interpretation s {g} b) :
    Synthesis interpretation s {fun x => f x && g x} (a + b + 1) := by
  simpa [interpretation] using hf.binary hg .and

/-- Binary disjunction costs one gate beyond its arguments. -/
theorem or (hf : Synthesis interpretation s {f} a) (hg : Synthesis interpretation s {g} b) :
    Synthesis interpretation s {fun x => f x || g x} (a + b + 1) := by
  simpa [interpretation] using hf.binary hg .or

/-- Disjoin a finite family of functions. The extra gate supplies the empty disjunction. -/
theorem exists_mem (indices : Finset ι) (f : ι → BooleanFunction n) (cost : ι → ℕ)
    (h : ∀ i ∈ indices, Synthesis interpretation s {f i} (cost i)) :
    Synthesis interpretation s {fun x => decide (∃ i ∈ indices, f i x = true)}
      ((∑ i ∈ indices, (cost i + 1)) + 1) := by
  have hop (f g : BooleanFunction n) :
      Synthesis interpretation {f, g} {fun x => f x || g x} 1 := by
    simpa [interpretation] using gate (I := interpretation) (s := {f, g}) .or
      (fun i => if i.val = 0 then f else g) (fun i => by split <;> simp)
  have heq : (fun x => indices.fold Bool.or false (fun i => f i x)) =
      (fun x => decide (∃ i ∈ indices, f i x = true)) := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simpa using Finset.fold_op_rel_iff_or (op := Bool.or)
      (r := fun _ v : Bool => v = true) (by simp) (c := true)
      (s := indices) (f := fun i => f i x) (b := false)
  simpa only [heq] using finset_fold Bool.or 1 hop indices f cost
    (fun _ => false) (const false) h

/-- Conjoin a finite family of functions. The extra gate supplies the empty conjunction. -/
theorem forall_mem (indices : Finset ι) (f : ι → BooleanFunction n) (cost : ι → ℕ)
    (h : ∀ i ∈ indices, Synthesis interpretation s {f i} (cost i)) :
    Synthesis interpretation s {fun x => decide (∀ i ∈ indices, f i x = true)}
      ((∑ i ∈ indices, (cost i + 1)) + 1) := by
  have hop (f g : BooleanFunction n) :
      Synthesis interpretation {f, g} {fun x => f x && g x} 1 := by
    simpa [interpretation] using gate (I := interpretation) (s := {f, g}) .and
      (fun i => if i.val = 0 then f else g) (fun i => by split <;> simp)
  have heq : (fun x => indices.fold Bool.and true (fun i => f i x)) =
      (fun x => decide (∀ i ∈ indices, f i x = true)) := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simpa using Finset.fold_op_rel_iff_and (op := Bool.and)
      (r := fun _ v : Bool => v = true) (by simp) (c := true)
      (s := indices) (f := fun i => f i x) (b := true)
  simpa only [heq] using finset_fold Bool.and 1 hop indices f cost
    (fun _ => true) (const true) h

end Synthesis

namespace Boolean

/-- A conjunction testing a specified tuple of input bits. -/
theorem synthesis_minterm {k : ℕ} (wires : Fin k → Fin n) (value : Fin k → Bool) :
    Synthesis interpretation (inputs n) {fun x => decide ((fun i => x (wires i)) = value)}
      (2 * k + 1) := by
  have literal (i : Fin k) :
      Synthesis interpretation (inputs n) {fun x => decide (x (wires i) = value i)} 1 := by
    have h : Synthesis interpretation (inputs n) {fun x => x (wires i)} 0 :=
      Synthesis.of_subset (Set.singleton_subset_iff.mpr ⟨wires i, rfl⟩)
    cases hv : value i
    · simpa [hv] using h.not
    · simpa [hv] using h.mono Set.Subset.rfl Set.Subset.rfl (by omega : 0 ≤ 1)
  have h := Synthesis.forall_mem Finset.univ
    (fun i x => decide (x (wires i) = value i)) (fun _ => 1) (fun i _ => literal i)
  simpa [funext_iff, Nat.mul_comm] using h

end Boolean
end Cslib.Circuits
