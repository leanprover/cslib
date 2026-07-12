/-
Copyright (c) 2026 TODO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TODO
-/

module

public import Cslib.Init

/-!
# Van Glabbeek's spectrum as a Galois connection — the polarity framework

Behavioural equivalences are organised as the fixed points of an antitone Galois
connection ("polarity") between sets of tests (ordered by ⊆) and equivalences
(ordered by refinement). The Galois-closed equivalences — the "testable" ones —
are exactly the image of `induced`; they form a lattice, not a chain
(see `Spectrum.Antichain`).

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
* `cl Ω`: the closure operator `induced Ω ∘ respects Ω`.
* `Testable Ω E`: the fixed-point predicate (`cl Ω E = E`).

## Main statements

* `polarity`: the antitone Galois connection.
* `induced_testable`: every induced equivalence is a fixed point of `cl`.
* `cl_extensive`, `cl_monotone`, `cl_idempotent`: `cl` is a closure operator.
* `spectrum_eq_closed_elements`: testable ↔ in the image of `induced`.
-/

@[expose] public section

namespace Cslib.LTS.Spectrum

variable {Proc : Type*}

/-- The equivalence a test class induces: agreement on every test in `T`.
    Antitone in `T` — more tests ⇒ finer (smaller) equivalence. -/
def induced (Ω : Type*) (T : Set (Proc → Ω)) (p q : Proc) : Prop :=
  ∀ t ∈ T, t p = t q

/-- The tests that respect an equivalence `E`: tests constant on every E-pair.
    Antitone in `E` — coarser `E` ⇒ fewer respecting tests. -/
def respects (Ω : Type*) (E : Proc → Proc → Prop) : Set (Proc → Ω) :=
  { t | ∀ p q, E p q → t p = t q }

/-- **Polarity.** Antitone Galois connection between test classes (⊆) and
    equivalences (refinement): `E` refines `induced Ω T` iff `T ⊆ respects Ω E`. -/
theorem polarity (Ω : Type*) (T : Set (Proc → Ω)) (E : Proc → Proc → Prop) :
    (∀ p q, E p q → induced Ω T p q) ↔ T ⊆ respects Ω E := by
  constructor
  · intro h t ht p q hpq
    exact h p q hpq t ht
  · intro h p q hpq t ht
    exact h ht p q hpq

/-- Every test in `T` respects the equivalence `T` induces (the image fact). -/
theorem test_subset_respects_induced (Ω : Type*) (T : Set (Proc → Ω)) :
    T ⊆ respects Ω (induced Ω T) := by
  intro t ht
  change ∀ p q, induced Ω T p q → t p = t q
  intro p q hpq
  exact hpq t ht

/-- Closure operator on equivalences: `induced Ω ∘ respects Ω`. -/
def cl (Ω : Type*) (E : Proc → Proc → Prop) : Proc → Proc → Prop :=
  induced Ω (respects Ω E)

/-- `cl Ω` is extensive: `E ≤ cl Ω E` (pointwise). -/
theorem cl_extensive (Ω : Type*) (E : Proc → Proc → Prop) (p q : Proc)
    (h : E p q) : cl Ω E p q := by
  intro t ht
  exact ht p q h

/-- `cl Ω` is monotone: `E₁ ≤ E₂ → cl Ω E₁ ≤ cl Ω E₂`. -/
theorem cl_monotone (Ω : Type*) (E₁ E₂ : Proc → Proc → Prop)
    (h : ∀ p q, E₁ p q → E₂ p q) (p q : Proc) (hcl : cl Ω E₁ p q) :
    cl Ω E₂ p q := by
  intro t ht
  exact hcl t (fun a b ha => ht a b (h a b ha))

/-- An equivalence is TESTABLE iff it is exactly "indistinguishability under
    the tests that respect it" — i.e. a fixed point of `cl Ω`. This predicate
    IS the closed-element condition. -/
def Testable (Ω : Type*) (E : Proc → Proc → Prop) : Prop :=
  ∀ p q, cl Ω E p q ↔ E p q

/-- Every induced equivalence is testable (the image of `induced Ω` is contained
    in the fixed points of `cl Ω`). -/
theorem induced_testable (Ω : Type*) (T : Set (Proc → Ω)) :
    Testable Ω (induced Ω T) := by
  intro p q
  constructor
  · intro hcl t ht
    exact hcl t (test_subset_respects_induced Ω T ht)
  · intro hInd t ht
    exact ht p q hInd

/-- `cl Ω` is idempotent: `cl Ω (cl Ω E) = cl Ω E`. `cl Ω E` lies in the image
    of `induced Ω`, hence is a fixed point by `induced_testable`. -/
theorem cl_idempotent (Ω : Type*) (E : Proc → Proc → Prop) (p q : Proc) :
    cl Ω (cl Ω E) p q ↔ cl Ω E p q := by
  have key : Testable Ω (induced Ω (respects Ω E)) := induced_testable Ω (respects Ω E)
  exact key p q

/-- **Spectrum = image of `induced` = closed elements.** An equivalence is
    testable (a fixed point of `cl Ω`) iff it is exactly the equivalence induced
    by some test class. Forward direction witnessed by `T = respects Ω E`. -/
theorem spectrum_eq_closed_elements (Ω : Type*) (E : Proc → Proc → Prop) :
    Testable Ω E ↔ ∃ T : Set (Proc → Ω), induced Ω T = E := by
  constructor
  · intro hE
    refine ⟨respects Ω E, ?_⟩
    change cl Ω E = E
    funext p q
    exact propext (hE p q)
  · rintro ⟨T, rfl⟩
    exact induced_testable Ω T

end Cslib.LTS.Spectrum
