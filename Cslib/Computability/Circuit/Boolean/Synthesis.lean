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

A synthesis bound `Synthesis sources targets cost` states that, starting from any program
whose wires already compute every function in `sources`, at most `cost` further gates suffice
to compute every function in `targets` as well, without discarding anything the starting
program computed.

Bounds are stated relative to an arbitrary starting program, rather than the empty program,
so that constructions can share intermediate results: chaining two bounds
(`Synthesis.comp`) adds their costs, because the second construction may reuse any wire
built by the first. The lemmas below give bounds for constants, negation, binary and finite
conjunction and disjunction, and simultaneous families of functions.
`Synthesis.exists_circuit` turns a bound over the input projections into a single-output
circuit.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

universe u
variable {n : ℕ} {ι : Type u}

/-- The coordinate projections supplied by the circuit's inputs. -/
def inputs (n : ℕ) : Set (BooleanFunction n) := Set.range fun i x => x i

/-- The Boolean functions computed by the wires of `p`, whether input wires or internal
gates. -/
def available {g : ℕ} (p : Program signature n g) : Set (BooleanFunction n) :=
  Set.range (p.wireFunction interpretation)

/-- A function is available exactly when some wire computes it pointwise. -/
theorem mem_available {g : ℕ} {p : Program signature n g} {f : BooleanFunction n} :
    f ∈ available p ↔ ∃ w, ∀ x, p.trace interpretation x w = f x := by
  simp [available, Program.wireFunction, funext_iff]

/-- The input projections are available in every program. -/
theorem inputs_subset_available {g : ℕ} (p : Program signature n g) :
    inputs n ⊆ available p := by
  rintro _ ⟨i, rfl⟩
  exact ⟨Wire.input i, p.wireFunction_input interpretation i⟩

/-- `Synthesis sources targets cost` says that `targets` can be computed from `sources`
using at most `cost` additional gates, without losing anything already computed.

Precisely: for every program `p₁` on whose wires every function in `sources` is available,
there is a program `p₂` such that
* `p₂` has at most `cost` more gates than `p₁`,
* every function available in `p₁` is still available in `p₂`, and
* every function in `targets` is available in `p₂`.

Quantifying over an arbitrary starting program, rather than the empty one, is what lets
constructions share intermediate results: `Synthesis.comp` adds budgets because the second
construction may reuse wires built by the first. -/
def Synthesis (sources targets : Set (BooleanFunction n)) (cost : ℕ) : Prop :=
  ∀ (g₁ : ℕ) (p₁ : Program signature n g₁), sources ⊆ available p₁ →
    ∃ (g₂ : ℕ) (p₂ : Program signature n g₂), g₂ ≤ g₁ + cost ∧
      available p₁ ⊆ available p₂ ∧ targets ⊆ available p₂

namespace Synthesis

variable {s t u : Set (BooleanFunction n)} {a b : ℕ} {f g : BooleanFunction n}

/-- Available functions require no additional gates. -/
theorem of_subset (h : t ⊆ s) : Synthesis s t 0 :=
  fun g p hp => ⟨g, p, by omega, Set.Subset.rfl, h.trans hp⟩

/-- Enlarge the source family, narrow the target family, or increase the budget. -/
theorem mono (h : Synthesis s t a) {s' t' : Set (BooleanFunction n)}
    (hs : s ⊆ s') (ht : t' ⊆ t) (hab : a ≤ b) : Synthesis s' t' b := by
  intro g₁ p hp
  obtain ⟨g₂, q, hq, hkeep, hout⟩ := h g₁ p (hs.trans hp)
  exact ⟨g₂, q, by omega, hkeep, ht.trans hout⟩

/-- Successive constructions add their gate budgets. -/
theorem comp (h : Synthesis s t a) (h' : Synthesis (s ∪ t) u b) :
    Synthesis s u (a + b) := by
  intro g₁ p hp
  obtain ⟨g₂, q, hq, hpq, ht⟩ := h g₁ p hp
  obtain ⟨g₃, r, hr, hqr, hu⟩ := h' g₂ q (Set.union_subset (hp.trans hpq) ht)
  exact ⟨g₃, r, by omega, hpq.trans hqr, hu⟩

/-- Combine two target families, preserving the first while constructing the second. -/
theorem union (h : Synthesis s t a) (h' : Synthesis s u b) :
    Synthesis s (t ∪ u) (a + b) := by
  intro g₁ p hp
  obtain ⟨g₂, q, hq, hpq, ht⟩ := h g₁ p hp
  obtain ⟨g₃, r, hr, hqr, hu⟩ := h' g₂ q (hp.trans hpq)
  exact ⟨g₃, r, by omega, hpq.trans hqr, Set.union_subset (ht.trans hqr) hu⟩

/-- Synthesize an operation whose arguments are already available. -/
theorem gate (op : Op) (args : Fin (signature.Arity op) → BooleanFunction n)
    (hargs : ∀ i, args i ∈ s) :
    Synthesis s {fun x => interpretation op (fun i => args i x)} 1 := by
  classical
  intro g₁ p hp
  choose wires hw using fun i => mem_available.mp (hp (hargs i))
  let line : Line signature n g₁ := ⟨op, wires⟩
  refine ⟨g₁ + 1, p.gate line, le_rfl, ?_, ?_⟩
  · intro f hf
    obtain ⟨w, hw'⟩ := mem_available.mp hf
    exact mem_available.mpr
      ⟨w.castSucc, fun x => (Program.trace_gate_castSucc _ _ _ _ _).trans (hw' x)⟩
  · rw [Set.singleton_subset_iff, mem_available]
    refine ⟨Fin.last (n + g₁), fun x => ?_⟩
    rw [Program.trace_gate_last]
    change interpretation op (fun i => p.trace interpretation x (wires i)) = _
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
  obtain ⟨g, p, hg, _, hout⟩ := h 0 .empty (inputs_subset_available _)
  obtain ⟨w, hw⟩ := mem_available.mp (hout (Set.mem_singleton f))
  exact ⟨g, by simpa using hg, ⟨p, fun _ => w⟩, hw⟩

end Cslib.Circuits.Boolean
