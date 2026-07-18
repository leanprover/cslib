/-
Copyright (c) 2026 patchwright. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: patchwright
-/

module

public import Cslib.Init
public import Mathlib.Order.GaloisConnection.Defs
public import Mathlib.Order.Closure

/-!
# Van Glabbeek's spectrum as a Galois connection — the polarity framework

Behavioural equivalences are organised as the closed elements of an antitone
Galois connection ("polarity") between sets of tests (ordered by `⊆`) and
equivalences (ordered by refinement). Following the standard Mathlib idiom, the
antitone connection is stated as a `GaloisConnection` into the order dual:

  `polarity : GaloisConnection (toDual ∘ respects Ω) (induced Ω ∘ ofDual)`

The closure operator on equivalences is then *derived* — it is
`(polarity Ω).closureOperator`, an instance of Mathlib's `ClosureOperator`
(the same pattern as `PhaseSemantics.biorthogonalClosure`), so extensivity,
monotonicity and idempotence are inherited rather than proved by hand. The
Galois-closed equivalences — the "testable" ones — are exactly the image of
`induced`; they form a lattice, not a chain (see `Spectrum.Antichain`).

This module is the Mathlib/`Cslib.Init`-only framework. A concrete named
spectrum point (CSLib's `HomTraceEq`) is shown Galois-closed in
`Spectrum.TracePoint`.

The construction is parameterised by the pair `(Proc, Ω)`: `Proc` is the process
type and `Ω` the observation type (a test is `Proc → Ω`). `Ω` is carried
explicitly because the closure-operator theorems mention only `E` and cannot
recover `Ω` from it.

## Main definitions

* `induced Ω T`: the equivalence a test class `T` induces.
* `respects Ω E`: the tests that respect an equivalence `E`.
* `cl Ω`: the closure operator `induced Ω ∘ respects Ω`, as a Mathlib
  `ClosureOperator`, obtained from `polarity` via
  `GaloisConnection.closureOperator`.
* `Testable Ω E`: `E` is a closed element of `cl Ω` (`(cl Ω).IsClosed E`).

## Main statements

* `polarity`: the antitone Galois connection, as a Mathlib `GaloisConnection`
  into the order dual.
* `induced_testable`: every induced equivalence is closed (from
  `GaloisConnection.u_l_u_eq_u`).
* `cl_extensive`, `cl_monotone`, `cl_idempotent`: inherited from
  `ClosureOperator`.
* `spectrum_eq_closed_elements`: testable ↔ in the image of `induced`.

## References

* [R.J. van Glabbeek, *The Linear Time – Branching Time Spectrum*][Glabbeek1990]
  (extended to silent moves in *Spectrum II* [Glabbeek1993]) — the spectrum of
  behavioural equivalences ordered by refinement.
* [H. Beohar, *Hennessy-Milner Theorems via Galois Connections*][Beohar2022] —
  the reading of those equivalences as the fixed points of an antitone Galois
  connection (polarity) between tests and equivalences.
-/

@[expose] public section

namespace Cslib.LTS.Spectrum

open OrderDual (toDual ofDual)

variable {Proc : Type*}

/-- The equivalence a test class induces: agreement on every test in `T`.
    Antitone in `T` — more tests ⇒ finer (smaller) equivalence. -/
def induced (Ω : Type*) (T : Set (Proc → Ω)) (p q : Proc) : Prop :=
  ∀ t ∈ T, t p = t q

/-- The tests that respect an equivalence `E`: tests constant on every E-pair.
    Antitone in `E` — coarser `E` ⇒ fewer respecting tests. -/
def respects (Ω : Type*) (E : Proc → Proc → Prop) : Set (Proc → Ω) :=
  { t | ∀ p q, E p q → t p = t q }

/-- Pointwise form of the polarity: `E` refines `induced Ω T` iff
    `T ⊆ respects Ω E`. The order-theoretic packaging is `polarity` below. -/
theorem polarity_iff (Ω : Type*) (T : Set (Proc → Ω)) (E : Proc → Proc → Prop) :
    (∀ p q, E p q → induced Ω T p q) ↔ T ⊆ respects Ω E := by
  constructor
  · intro h t ht p q hpq
    exact h p q hpq t ht
  · intro h p q hpq t ht
    exact h ht p q hpq

/-- **Polarity.** `respects Ω` and `induced Ω` form an antitone Galois
    connection between equivalences under refinement and test classes under
    `⊆`. Stated, as is standard in Mathlib, as a (monotone) `GaloisConnection`
    into the order dual `(Set (Proc → Ω))ᵒᵈ`. -/
theorem polarity (Ω : Type*) :
    GaloisConnection (fun E : Proc → Proc → Prop => toDual (respects Ω E))
      (fun T => induced Ω (ofDual T)) := by
  intro E T
  rw [OrderDual.toDual_le]
  simp only [Set.le_eq_subset, Pi.le_def, le_Prop_eq]
  exact (polarity_iff Ω (ofDual T) E).symm

/-- Every test in `T` respects the equivalence `T` induces — the counit
    `l (u b) ≤ b` of `polarity`, read back through the dual. -/
theorem test_subset_respects_induced (Ω : Type*) (T : Set (Proc → Ω)) :
    T ⊆ respects Ω (induced Ω T) :=
  (polarity Ω).l_u_le (toDual T)

/-- Closure operator on equivalences: `induced Ω ∘ respects Ω`, obtained from
    `polarity` via Mathlib's `GaloisConnection.closureOperator`. -/
def cl (Ω : Type*) : ClosureOperator (Proc → Proc → Prop) :=
  (polarity (Proc := Proc) Ω).closureOperator

/-- `cl Ω` acts as `induced Ω ∘ respects Ω`. -/
theorem cl_apply (Ω : Type*) (E : Proc → Proc → Prop) :
    cl Ω E = induced Ω (respects Ω E) :=
  rfl

/-- `cl Ω` is extensive: `E ≤ cl Ω E` — inherited from `ClosureOperator`. -/
theorem cl_extensive (Ω : Type*) (E : Proc → Proc → Prop) : E ≤ cl Ω E :=
  (cl Ω).le_closure E

/-- `cl Ω` is monotone — inherited from `ClosureOperator`. -/
theorem cl_monotone (Ω : Type*) : Monotone (cl (Proc := Proc) Ω) :=
  (cl Ω).monotone

/-- `cl Ω` is idempotent — inherited from `ClosureOperator`. -/
theorem cl_idempotent (Ω : Type*) (E : Proc → Proc → Prop) :
    cl Ω (cl Ω E) = cl Ω E :=
  (cl Ω).idempotent E

/-- An equivalence is TESTABLE iff it is exactly "indistinguishability under
    the tests that respect it" — i.e. a closed element of `cl Ω`. -/
def Testable (Ω : Type*) (E : Proc → Proc → Prop) : Prop :=
  (cl Ω).IsClosed E

/-- Pointwise reading of `Testable`: `cl Ω E` and `E` agree on every pair. -/
theorem testable_iff (Ω : Type*) (E : Proc → Proc → Prop) :
    Testable Ω E ↔ ∀ p q, cl Ω E p q ↔ E p q := by
  rw [Testable, ClosureOperator.isClosed_iff]
  constructor
  · intro h p q
    exact iff_of_eq (congrFun (congrFun h p) q)
  · intro h
    funext p q
    exact propext (h p q)

/-- Every induced equivalence is testable (the image of `induced Ω` is
    contained in the closed elements) — this is `u ∘ l ∘ u = u` for `polarity`
    (`GaloisConnection.u_l_u_eq_u`). -/
theorem induced_testable (Ω : Type*) (T : Set (Proc → Ω)) :
    Testable Ω (induced Ω T) :=
  (cl Ω).isClosed_iff.2 ((polarity Ω).u_l_u_eq_u (toDual T))

/-- **Spectrum = image of `induced` = closed elements.** An equivalence is
    testable (a closed element of `cl Ω`) iff it is exactly the equivalence
    induced by some test class. Forward direction witnessed by
    `T = respects Ω E`. -/
theorem spectrum_eq_closed_elements (Ω : Type*) (E : Proc → Proc → Prop) :
    Testable Ω E ↔ ∃ T : Set (Proc → Ω), induced Ω T = E := by
  constructor
  · intro hE
    exact ⟨respects Ω E, (cl Ω).isClosed_iff.1 hE⟩
  · rintro ⟨T, rfl⟩
    exact induced_testable Ω T

end Cslib.LTS.Spectrum
