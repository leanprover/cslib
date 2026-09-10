/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Boolean.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Simultaneous Boolean synthesis

Synthesis bounds describe how many gates suffice to compute a family of functions from an
existing program. Previously computed functions remain available, allowing constructions to
share intermediate results.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

universe u
variable {n : ℕ} {ι : Type u}

/-- Functions available on the input or gate wires of a program. -/
def available (p : Σ g, Program signature n g) : Set (BooleanFunction n) :=
  {f | ∃ w, ∀ x, p.2.trace interpretation x w = f x}

/-- At most `cost` additional gates suffice to compute `targets` from `sources`, while
preserving all functions already available in the starting program. -/
def Synthesis (sources targets : Set (BooleanFunction n)) (cost : ℕ) : Prop :=
  ∀ p, sources ⊆ available p → ∃ q, q.1 ≤ p.1 + cost ∧
    available p ⊆ available q ∧ targets ⊆ available q

namespace Synthesis

variable {s t u : Set (BooleanFunction n)} {a b : ℕ} {f g : BooleanFunction n}

/-- Available functions require no additional gates. -/
theorem of_subset (h : t ⊆ s) : Synthesis s t 0 :=
  fun p hp => ⟨p, by omega, Set.Subset.rfl, h.trans hp⟩

/-- Enlarge the source family, narrow the target family, or increase the budget. -/
theorem mono (h : Synthesis s t a) {s' t' : Set (BooleanFunction n)}
    (hs : s ⊆ s') (ht : t' ⊆ t) (hab : a ≤ b) : Synthesis s' t' b := by
  intro p hp
  obtain ⟨q, hq, hkeep, hout⟩ := h p (hs.trans hp)
  exact ⟨q, by omega, hkeep, ht.trans hout⟩

/-- Successive constructions add their gate budgets. -/
theorem comp (h : Synthesis s t a) (h' : Synthesis (s ∪ t) u b) :
    Synthesis s u (a + b) := by
  intro p hp
  obtain ⟨q, hq, hpq, ht⟩ := h p hp
  obtain ⟨r, hr, hqr, hu⟩ := h' q (Set.union_subset (hp.trans hpq) ht)
  exact ⟨r, by omega, hpq.trans hqr, hu⟩

/-- Combine two target families, preserving the first while constructing the second. -/
theorem union (h : Synthesis s t a) (h' : Synthesis s u b) :
    Synthesis s (t ∪ u) (a + b) := by
  intro p hp
  obtain ⟨q, hq, hpq, ht⟩ := h p hp
  obtain ⟨r, hr, hqr, hu⟩ := h' q (hp.trans hpq)
  exact ⟨r, by omega, hpq.trans hqr, Set.union_subset (ht.trans hqr) hu⟩

/-- Synthesize an operation whose arguments are already available. -/
theorem gate (op : Op) (args : Fin (signature.Arity op) → BooleanFunction n)
    (hargs : ∀ i, args i ∈ s) :
    Synthesis s {fun x => interpretation op (fun i => args i x)} 1 := by
  classical
  intro p hp
  choose wires hw using fun i => hp (hargs i)
  let line : Line signature n p.1 := ⟨op, wires⟩
  refine ⟨⟨p.1 + 1, p.2.gate line⟩, le_rfl, ?_, ?_⟩
  · rintro f ⟨w, hw⟩
    exact ⟨w.castSucc, fun x => (Program.trace_gate_castSucc _ _ _ _ _).trans (hw x)⟩
  · rw [Set.singleton_subset_iff]
    refine ⟨Fin.last (n + p.1), fun x => ?_⟩
    rw [Program.trace_gate_last]
    change interpretation op (fun i => p.2.trace interpretation x (wires i)) = _
    simp only [hw]

/-- Constants cost one gate. -/
theorem const (value : Bool) : Synthesis s {fun _ => value} 1 :=
  gate (.const value) Fin.elim0 (fun i => Fin.elim0 i)

/-- Apply negation to a synthesized function. -/
theorem not (h : Synthesis s {f} a) : Synthesis s {fun x => !f x} (a + 1) :=
  h.comp (gate .not (fun _ => f) (by simp))

private theorem binary (op : Op)
    (hf : Synthesis s {f} a) (hg : Synthesis s {g} b) :
    Synthesis s {fun x => interpretation op (fun i => if i.val = 0 then f x else g x)}
      (a + b + 1) := by
  simpa only [ite_apply] using (hf.union hg).comp
    (gate op (fun i => if i.val = 0 then f else g) (fun i => by split <;> simp))

/-- Binary conjunction costs one gate beyond its arguments. -/
theorem and (hf : Synthesis s {f} a) (hg : Synthesis s {g} b) :
    Synthesis s {fun x => f x && g x} (a + b + 1) := by
  simpa [interpretation] using binary .and hf hg

/-- Binary disjunction costs one gate beyond its arguments. -/
theorem or (hf : Synthesis s {f} a) (hg : Synthesis s {g} b) :
    Synthesis s {fun x => f x || g x} (a + b + 1) := by
  simpa [interpretation] using binary .or hf hg

/-- Simultaneously synthesize an indexed finite family. -/
theorem family [Fintype ι] (f : ι → BooleanFunction n) (cost : ι → ℕ)
    (h : ∀ i, Synthesis s {f i} (cost i)) :
    Synthesis s (Set.range f) (∑ i, cost i) := by
  classical
  suffices ∀ indices : Finset ι, Synthesis s (f '' (indices : Set ι))
      (∑ i ∈ indices, cost i) by simpa using this Finset.univ
  intro indices
  induction indices using Finset.induction_on with
  | empty => exact of_subset (by simp)
  | @insert i indices hi ih =>
    simpa [Finset.sum_insert hi] using (h i).union ih

/-- Disjoin a finite family of functions. The extra gate supplies the empty disjunction. -/
theorem exists_mem (indices : Finset ι) (f : ι → BooleanFunction n) (cost : ι → ℕ)
    (h : ∀ i ∈ indices, Synthesis s {f i} (cost i)) :
    Synthesis s {fun x => decide (∃ i ∈ indices, f i x = true)}
      ((∑ i ∈ indices, (cost i + 1)) + 1) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simpa using (const (s := s) false)
  | @insert i indices hi ih =>
    have step := (h i (by simp)).or (ih (fun j hj => h j (by simp [hj])))
    simpa [Finset.sum_insert hi, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using step

/-- Conjoin a finite family of functions. The extra gate supplies the empty conjunction. -/
theorem forall_mem (indices : Finset ι) (f : ι → BooleanFunction n) (cost : ι → ℕ)
    (h : ∀ i ∈ indices, Synthesis s {f i} (cost i)) :
    Synthesis s {fun x => decide (∀ i ∈ indices, f i x = true)}
      ((∑ i ∈ indices, (cost i + 1)) + 1) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simpa using (const (s := s) true)
  | @insert i indices hi ih =>
    have step := (h i (by simp)).and (ih (fun j hj => h j (by simp [hj])))
    simpa [Finset.sum_insert hi, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using step

end Synthesis

/-- The coordinate projections supplied by the circuit's inputs. -/
def inputs (n : ℕ) : Set (BooleanFunction n) := Set.range fun i x => x i

/-- A conjunction testing a specified tuple of input bits. -/
theorem synthesis_minterm {k : ℕ} (wires : Fin k → Fin n) (value : Fin k → Bool) :
    Synthesis (inputs n) {fun x => decide ((fun i => x (wires i)) = value)} (2 * k + 1) := by
  have literal (i : Fin k) :
      Synthesis (inputs n) {fun x => decide (x (wires i) = value i)} 1 := by
    have h : Synthesis (inputs n) {fun x => x (wires i)} 0 :=
      Synthesis.of_subset (Set.singleton_subset_iff.mpr ⟨wires i, rfl⟩)
    cases hv : value i
    · simpa [hv] using h.not
    · simpa [hv] using h.mono Set.Subset.rfl Set.Subset.rfl (by omega : 0 ≤ 1)
  have h := Synthesis.forall_mem Finset.univ
    (fun i x => decide (x (wires i) = value i)) (fun _ => 1) (fun i _ => literal i)
  simpa [funext_iff, Nat.mul_comm] using h

/-- Extract a single-output circuit from a synthesis bound on the input projections. -/
theorem Synthesis.exists_circuit {f : BooleanFunction n} {cost : ℕ}
    (h : Synthesis (inputs n) {f} cost) :
    ∃ g ≤ cost, ∃ c : Circuit signature n g 1, c.Computes f := by
  have hin : inputs n ⊆ available ⟨0, .empty⟩ := by
    rintro _ ⟨i, rfl⟩
    exact ⟨Wire.input i, fun x => Program.trace_input _ _ x i⟩
  obtain ⟨⟨g, p⟩, hg, _, hout⟩ := h ⟨0, .empty⟩ hin
  obtain ⟨w, hw⟩ := hout (Set.mem_singleton f)
  exact ⟨g, by simpa using hg, ⟨p, fun _ => w⟩, hw⟩

end Cslib.Circuits.Boolean
