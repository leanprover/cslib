/-
Copyright (c) 2026 patchwright. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: patchwright
-/

module

public import Cslib.Init
public import Mathlib.Order.GaloisConnection.Basic
public import Mathlib.Order.Closure

/-!
# The van Glabbeek spectrum as a Galois connection

The linear time–branching time spectrum of behavioural equivalences is the set
of *testable* equivalences on a process type: those an observer recovers exactly
as indistinguishability under the tests that respect them. This set is the
collection of closed elements of an antitone Galois connection — a *polarity* —
between equivalences and tests.

The two preorders of the connection are:

* equivalences `E : Proc → Proc → Prop`, ordered by pointwise implication
  `E ≤ E' ↔ ∀ p q, E p q → E' p q` (graph inclusion);
* test classes `T : Set (Proc → Ω)`, ordered by `(⊆)`.

The antitone connection is packaged as a monotone `GaloisConnection` into the
order dual on the test side:

  `polarity : GaloisConnection (toDual ∘ respects Ω) (induced Ω ∘ ofDual)`

Its closure operator is `cl Ω = induced Ω ∘ respects Ω`, and the spectrum is the
set of its closed elements. A named spectrum point (`HomTraceEq`) is shown closed
in `Spectrum.TracePoint`; the spectrum is a lattice rather than a chain
(`Spectrum.Antichain`).

The construction is parameterised by `Proc` (the process type) and `Ω` (the
observation type; a test is `Proc → Ω`). `Ω` is carried explicitly because the
closure operator itself mentions only `E`.

## Main definitions

* `induced Ω T`: the equivalence a test class induces.
* `respects Ω E`: the tests constant on every `E`-pair.
* `polarity Ω`: the Galois connection above.
* `cl Ω`: the closure operator `induced Ω ∘ respects Ω`.
* `Testable Ω E`: the proposition that `E` is `cl Ω`-closed.
* `spectrum Ω`: the set of testable equivalences.

## Main statements

* `spectrum_eq_closed_elements`: the testable equivalences are exactly the image
  of `induced`.
* `spectrumCompleteLattice`: the spectrum is a complete lattice under refinement.

## References

* [R.J. van Glabbeek, *The Linear Time – Branching Time Spectrum*][Glabbeek1990],
  extended to silent moves in *Spectrum II* [Glabbeek1993].
* [H. Beohar, *Hennessy-Milner Theorems via Galois Connections*][Beohar2022].
-/

@[expose] public section

namespace Cslib.LTS.Spectrum

open OrderDual (toDual ofDual)

variable {Proc : Type*}

/-- Equivalence induced by a test class `T`: two processes agree on every test
    in `T`. -/
def induced (Ω : Type*) (T : Set (Proc → Ω)) (p q : Proc) : Prop :=
  ∀ t ∈ T, t p = t q

/-- Tests that respect an equivalence `E`: constant on every `E`-pair. -/
def respects (Ω : Type*) (E : Proc → Proc → Prop) : Set (Proc → Ω) :=
  { t | ∀ p q, E p q → t p = t q }

/-- `E` refines `induced Ω T` iff every test in `T` respects `E`. -/
theorem polarity_iff (Ω : Type*) (T : Set (Proc → Ω)) (E : Proc → Proc → Prop) :
    (∀ p q, E p q → induced Ω T p q) ↔ T ⊆ respects Ω E := by
  constructor
  · intro h t ht p q hpq
    exact h p q hpq t ht
  · intro h p q hpq t ht
    exact h ht p q hpq

/-- The polarity: `respects Ω` and `induced Ω` form an antitone Galois connection
    between equivalences (pointwise implication) and test classes (`(⊆)`, into
    the order dual). -/
theorem polarity (Ω : Type*) :
    GaloisConnection (fun E : Proc → Proc → Prop => toDual (respects Ω E))
      (fun T => induced Ω (ofDual T)) := by
  intro E T
  rw [OrderDual.toDual_le]
  simp only [Pi.le_def, le_Prop_eq]
  exact (polarity_iff Ω (ofDual T) E).symm

/-- Every test in `T` respects the equivalence `T` induces. -/
theorem test_subset_respects_induced (Ω : Type*) (T : Set (Proc → Ω)) :
    T ⊆ respects Ω (induced Ω T) :=
  (polarity Ω).l_u_le (toDual T)

/-- Closure operator `induced Ω ∘ respects Ω`, obtained from `polarity` as a
    `ClosureOperator`. -/
def cl (Ω : Type*) : ClosureOperator (Proc → Proc → Prop) :=
  (polarity (Proc := Proc) Ω).closureOperator

/-- `cl Ω E = induced Ω (respects Ω E)`. -/
theorem cl_apply (Ω : Type*) (E : Proc → Proc → Prop) :
    cl Ω E = induced Ω (respects Ω E) :=
  rfl

/-- An equivalence is *testable* iff it is a closed element of `cl Ω`. -/
def Testable (Ω : Type*) (E : Proc → Proc → Prop) : Prop :=
  (cl Ω).IsClosed E

/-- The **van Glabbeek spectrum**: the set of testable equivalences on `Proc`. -/
def spectrum (Ω : Type*) : Set (Proc → Proc → Prop) :=
  { E | Testable Ω E }

/-- `Testable Ω E` iff `cl Ω E` and `E` agree pointwise. -/
theorem testable_iff (Ω : Type*) (E : Proc → Proc → Prop) :
    Testable Ω E ↔ ∀ p q, cl Ω E p q ↔ E p q := by
  rw [Testable, ClosureOperator.isClosed_iff]
  constructor
  · intro h p q
    exact iff_of_eq (congrFun (congrFun h p) q)
  · intro h
    funext p q
    exact propext (h p q)

/-- Every induced equivalence is testable. -/
theorem induced_testable (Ω : Type*) (T : Set (Proc → Ω)) :
    Testable Ω (induced Ω T) :=
  (cl Ω).isClosed_iff.2 ((polarity Ω).u_l_u_eq_u (toDual T))

/-- An equivalence is testable iff it is induced by some test class. -/
theorem spectrum_eq_closed_elements (Ω : Type*) (E : Proc → Proc → Prop) :
    Testable Ω E ↔ ∃ T : Set (Proc → Ω), induced Ω T = E := by
  constructor
  · intro hE
    exact ⟨respects Ω E, (cl Ω).isClosed_iff.1 hE⟩
  · rintro ⟨T, rfl⟩
    exact induced_testable Ω T

/-- The spectrum is a complete lattice under refinement; it is not a chain
    (see `Spectrum.Antichain`). -/
instance spectrumCompleteLattice {Ω : Type*} :
    CompleteLattice ((cl (Proc := Proc) Ω).Closeds) :=
  (cl Ω).gi.liftCompleteLattice

end Cslib.LTS.Spectrum
