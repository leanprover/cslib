/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Fold
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Data.Set.Lattice.Bounded

/-!
# Simultaneous circuit synthesis

`Synthesis I sources targets cost` bounds the number of additional gates needed to compute
`targets` from `sources` under an interpretation `I`. Every function already available in the
starting program remains available, so successive constructions can share intermediate results.
The signature and its carrier are arbitrary; neither needs to be finite or decidable.

The core rules compose bounds, combine finite families, and apply operations of the signature.
The fold rules accept a bound for combining two arguments, which may itself use several gates.
`Synthesis.exists_circuit_family` selects any finite family of outputs without adding gates;
`Synthesis.exists_circuit` specializes this to a single output.
-/

@[expose] public section

namespace Cslib.Circuits

universe v u w
variable {σ : Signature.{v}} {U : Type u} {n : ℕ} {ι : Type w}
variable {I : Interpretation σ U}

/-- The coordinate projections supplied by the circuit's inputs. -/
def inputs (n : ℕ) : Set ((Fin n → U) → U) := Set.range fun i x => x i

/-- The functions computed by the wires of `p`, whether input wires or internal
gates. -/
def available (I : Interpretation σ U) {g : ℕ} (p : Program σ n g) : Set ((Fin n → U) → U) :=
  Set.range (p.wireFunction I)

/-- A function is available exactly when some wire computes it pointwise. -/
theorem mem_available {g : ℕ} {p : Program σ n g} {f : (Fin n → U) → U} :
    f ∈ available I p ↔ ∃ w, ∀ x, p.trace I x w = f x := by
  simp [available, Program.wireFunction, funext_iff]

/-- The input projections are available in every program. -/
theorem inputs_subset_available {g : ℕ} (p : Program σ n g) :
    inputs n ⊆ available I p := by
  rintro _ ⟨i, rfl⟩
  exact ⟨Wire.input i, p.wireFunction_input I i⟩

/-- `Synthesis I sources targets cost` says that `targets` can be computed from `sources`
using at most `cost` additional gates, without losing anything already computed.

Precisely: for every program `p₁` on whose wires every function in `sources` is available,
there is a program `p₂` such that
* `p₂` has at most `cost` more gates than `p₁`,
* every function available in `p₁` is still available in `p₂`, and
* every function in `targets` is available in `p₂`.

Quantifying over an arbitrary starting program, rather than the empty one, is what lets
constructions share intermediate results: `Synthesis.comp` adds budgets because the second
construction may reuse wires built by the first. -/
def Synthesis (I : Interpretation σ U) (sources targets : Set ((Fin n → U) → U))
    (cost : ℕ) : Prop :=
  ∀ (g₁ : ℕ) (p₁ : Program σ n g₁), sources ⊆ available I p₁ →
    ∃ (g₂ : ℕ) (p₂ : Program σ n g₂), g₂ ≤ g₁ + cost ∧
      available I p₁ ⊆ available I p₂ ∧ targets ⊆ available I p₂

namespace Synthesis

variable {s t t₁ : Set ((Fin n → U) → U)} {a b : ℕ} {f g : (Fin n → U) → U}

/-- Available functions require no additional gates. -/
theorem of_subset (h : t ⊆ s) : Synthesis I s t 0 :=
  fun g p hp => ⟨g, p, by omega, Set.Subset.rfl, h.trans hp⟩

/-- Enlarge the source family, narrow the target family, or increase the budget. -/
theorem mono (h : Synthesis I s t a) {s' t' : Set ((Fin n → U) → U)}
    (hs : s ⊆ s') (ht : t' ⊆ t) (hab : a ≤ b) : Synthesis I s' t' b := by
  intro g₁ p hp
  obtain ⟨g₂, q, hq, hkeep, hout⟩ := h g₁ p (hs.trans hp)
  exact ⟨g₂, q, by omega, hkeep, ht.trans hout⟩

/-- Successive constructions add their gate budgets. -/
theorem comp (h : Synthesis I s t a) (h' : Synthesis I (s ∪ t) t₁ b) :
    Synthesis I s t₁ (a + b) := by
  intro g₁ p hp
  obtain ⟨g₂, q, hq, hpq, ht⟩ := h g₁ p hp
  obtain ⟨g₃, r, hr, hqr, hu⟩ := h' g₂ q (Set.union_subset (hp.trans hpq) ht)
  exact ⟨g₃, r, by omega, hpq.trans hqr, hu⟩

/-- Combine two target families, preserving the first while constructing the second. -/
theorem union (h : Synthesis I s t a) (h' : Synthesis I s t₁ b) :
    Synthesis I s (t ∪ t₁) (a + b) := by
  intro g₁ p hp
  obtain ⟨g₂, q, hq, hpq, ht⟩ := h g₁ p hp
  obtain ⟨g₃, r, hr, hqr, hu⟩ := h' g₂ q (hp.trans hpq)
  exact ⟨g₃, r, by omega, hpq.trans hqr, Set.union_subset (ht.trans hqr) hu⟩

/-- Synthesize an operation whose arguments are already available. -/
theorem gate (op : σ.Op) (args : Fin (σ.Arity op) → (Fin n → U) → U)
    (hargs : ∀ i, args i ∈ s) :
    Synthesis I s {fun x => I op (fun i => args i x)} 1 := by
  classical
  intro g₁ p hp
  choose wires hw using fun i => mem_available.mp (hp (hargs i))
  let line : Line σ n g₁ := ⟨op, wires⟩
  refine ⟨g₁ + 1, p.gate line, le_rfl, ?_, ?_⟩
  · intro f hf
    obtain ⟨w, hw'⟩ := mem_available.mp hf
    exact mem_available.mpr
      ⟨w.castSucc, fun x => (Program.trace_gate_castSucc _ _ _ _ _).trans (hw' x)⟩
  · rw [Set.singleton_subset_iff, mem_available]
    refine ⟨Fin.last (n + g₁), fun x => ?_⟩
    rw [Program.trace_gate_last]
    change I op (fun i => p.trace I x (wires i)) = _
    simp only [hw]

/-- Combine a finite family of target sets, retaining all earlier results. -/
theorem biUnion (indices : Finset ι) (targets : ι → Set ((Fin n → U) → U))
    (cost : ι → ℕ) (h : ∀ i ∈ indices, Synthesis I s (targets i) (cost i)) :
    Synthesis I s (⋃ i ∈ indices, targets i) (∑ i ∈ indices, cost i) := by
  classical
  induction indices using Finset.induction_on with
  | empty => exact of_subset (by simp)
  | @insert i indices hi ih =>
    simpa [Finset.sum_insert hi] using
      (h i (by simp)).union (ih (fun j hj => h j (by simp [hj])))

/-- Combine target sets indexed by a finite type. -/
theorem iUnion [Fintype ι] (targets : ι → Set ((Fin n → U) → U)) (cost : ι → ℕ)
    (h : ∀ i, Synthesis I s (targets i) (cost i)) :
    Synthesis I s (⋃ i, targets i) (∑ i, cost i) := by
  simpa using biUnion Finset.univ targets cost (fun i _ => h i)

/-- Simultaneously synthesize an indexed finite family of functions. -/
theorem family [Fintype ι] (f : ι → (Fin n → U) → U) (cost : ι → ℕ)
    (h : ∀ i, Synthesis I s {f i} (cost i)) :
    Synthesis I s (Set.range f) (∑ i, cost i) := by
  simpa using iUnion (fun i => {f i}) cost h

/-- Synthesize every argument, then apply an operation with one further gate. -/
theorem gate_of_syntheses (op : σ.Op) (args : Fin (σ.Arity op) → (Fin n → U) → U)
    (cost : Fin (σ.Arity op) → ℕ) (h : ∀ i, Synthesis I s {args i} (cost i)) :
    Synthesis I s {fun x => I op (fun i => args i x)} ((∑ i, cost i) + 1) :=
  (family args cost h).comp (gate op args (fun i => Set.mem_union_right _ ⟨i, rfl⟩))

/-- A nullary operation supplies its interpreted constant with one gate. -/
theorem nullary (op : σ.Op) (arity : σ.Arity op = 0) :
    Synthesis I s {fun _ => I op (fun i => Fin.elim0 (Fin.cast arity i))} 1 :=
  gate op (fun i _ => Fin.elim0 (Fin.cast arity i)) (fun i => Fin.elim0 (Fin.cast arity i))

/-- Feed a synthesized function to every argument of an operation, using one further gate.
In particular, this applies a unary operation. -/
theorem unary (h : Synthesis I s {f} a) (op : σ.Op) :
    Synthesis I s {fun x => I op (fun _ => f x)} (a + 1) :=
  h.comp (gate op (fun _ => f) (by simp))

/-- Feed `f` to argument zero and `g` to the remaining arguments, using one further gate.
For a binary operation, these are its two arguments. -/
theorem binary (hf : Synthesis I s {f} a) (hg : Synthesis I s {g} b) (op : σ.Op) :
    Synthesis I s {fun x => I op (fun i => if i.val = 0 then f x else g x)}
      (a + b + 1) := by
  simpa only [ite_apply] using (hf.union hg).comp
    (gate op (fun i => if i.val = 0 then f else g) (fun i => by split <;> simp))

/-- Apply a synthesis bound to two previously synthesized arguments. The combining
construction can use several gates and can reuse either argument. -/
theorem combine {result : (Fin n → U) → U} {c : ℕ}
    (hf : Synthesis I s {f} a) (hg : Synthesis I s {g} b)
    (h : Synthesis I {f, g} {result} c) : Synthesis I s {result} (a + b + c) := by
  apply (hf.union hg).comp
  apply h.mono ?_ Set.Subset.rfl le_rfl
  intro k hk
  exact Set.mem_union_right _ (by simpa [or_comm] using hk)

/-- Fold an ordered list of synthesized functions. No algebraic laws are needed for the
combining operation. The seed and the combining construction have their own gate budgets. -/
theorem foldr (op : U → U → U) (combineCost : ℕ)
    (hop : ∀ f g : (Fin n → U) → U,
      Synthesis I {f, g} {fun x => op (f x) (g x)} combineCost)
    (indices : List ι) (f : ι → (Fin n → U) → U) (cost : ι → ℕ)
    (seed : (Fin n → U) → U) (hseed : Synthesis I s {seed} a)
    (h : ∀ i ∈ indices, Synthesis I s {f i} (cost i)) :
    Synthesis I s {fun x => indices.foldr (fun i acc => op (f i x) acc) (seed x)}
      ((indices.map fun i => cost i + combineCost).sum + a) := by
  induction indices with
  | nil => simpa using hseed
  | cons i indices ih =>
    have step := (h i (by simp)).combine
      (ih (fun j hj => h j (by simp [hj]))) (hop _ _)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using step

/-- Fold a finite set of synthesized functions with a commutative associative operation.
The seed need not be an identity or a constant, and the combining construction may use
several gates. -/
theorem finset_fold (op : U → U → U) [Std.Commutative op] [Std.Associative op]
    (combineCost : ℕ) (hop : ∀ f g : (Fin n → U) → U,
      Synthesis I {f, g} {fun x => op (f x) (g x)} combineCost)
    (indices : Finset ι) (f : ι → (Fin n → U) → U) (cost : ι → ℕ)
    (seed : (Fin n → U) → U) (hseed : Synthesis I s {seed} a)
    (h : ∀ i ∈ indices, Synthesis I s {f i} (cost i)) :
    Synthesis I s {fun x => indices.fold op (seed x) (fun i => f i x)}
      ((∑ i ∈ indices, (cost i + combineCost)) + a) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simpa using hseed
  | @insert i indices hi ih =>
    have step := (h i (by simp)).combine
      (ih (fun j hj => h j (by simp [hj]))) (hop _ _)
    simpa [Finset.fold_insert hi, Finset.sum_insert hi,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using step

/-- Select a finite family of outputs from a synthesis bound. Selecting outputs, including
repeated outputs or an empty family, requires no additional gates. -/
theorem exists_circuit_family {m cost : ℕ} {f : Fin m → (Fin n → U) → U}
    (h : Synthesis I (inputs n) (Set.range f) cost) :
    ∃ g ≤ cost, ∃ c : Circuit σ n g m, ∀ x j, c.eval I x j = f j x := by
  classical
  obtain ⟨g, p, hg, _, hout⟩ := h 0 .empty (inputs_subset_available _)
  choose wires hw using fun j => mem_available.mp (hout ⟨j, rfl⟩)
  exact ⟨g, by simpa using hg, ⟨p, wires⟩, fun x j => hw j x⟩

/-- Extract a single-output circuit from a synthesis bound on the input projections. -/
theorem exists_circuit {cost : ℕ} (h : Synthesis I (inputs n) {f} cost) :
    ∃ g ≤ cost, ∃ c : Circuit σ n g 1, c.Computes I f := by
  have h' : Synthesis I (inputs n) (Set.range fun _ : Fin 1 => f) cost := by
    simpa using h
  obtain ⟨g, hg, c, hc⟩ := h'.exists_circuit_family
  exact ⟨g, hg, c, fun x => hc x 0⟩

end Synthesis
end Cslib.Circuits
