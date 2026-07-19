/-
Copyright (c) 2026 patchwright. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: patchwright
-/

module

public import Cslib.Init
public import Cslib.Foundations.Semantics.LTS.Spectrum.Galois
public import Cslib.Logics.HML.Basic

/-!
# Spectrum bisim point — bisimilarity is Galois-closed (via Hennessy–Milner)

The non-trivial spectrum point. Unlike trace equivalence (`Spectrum.TracePoint`),
bisimilarity is not the kernel of its test map by definition; the
Hennessy–Milner theorem makes it one. CSLib mechanises HM as
`Cslib.Logic.HML.theoryEq_eq_bisimilarity` (`TheoryEq lts = HomBisimilarity lts`
for image-finite LTS), and `TheoryEq` is the equivalence induced by the
HML-theory test class, so:

  `Testable (Set (Proposition Label)) (HomBisimilarity lts)`.
-/

@[expose] public section

namespace Cslib.LTS.Spectrum

open Cslib Cslib.Logic.HML

variable {State Label : Type*} (lts : LTS State Label)

/-- The HML-theory observer test: a state's full theory (set of satisfied HML
    propositions). -/
def hmlTheory (s : State) : Set (Proposition Label) :=
  theory lts s

/-- Test class for the bisim point: the singleton HML-theory observer. -/
def hmlTestClass : Set (State → Set (Proposition Label)) :=
  { f | f = hmlTheory lts }

/-- The equivalence induced by the HML-theory test is CSLib's `TheoryEq`
    (pointwise iff). -/
theorem induced_hml_iff (p q : State) :
    induced (Set (Proposition Label)) (hmlTestClass lts) p q ↔ TheoryEq lts p q := by
  constructor
  · intro h
    exact h _ rfl
  · intro h t ht
    have ht : t = hmlTheory lts := ht
    subst ht
    exact h

/-- Function-equality form of `induced_hml_iff`. -/
theorem induced_hml :
    induced (Set (Proposition Label)) (hmlTestClass lts) = TheoryEq lts := by
  funext p q
  exact propext (induced_hml_iff lts p q)

/-- **Bisim point.** `HomBisimilarity lts` is testable for image-finite LTS, via
    the Hennessy–Milner theorem (`theoryEq_eq_bisimilarity`). -/
theorem HomBisimilarity_testable [image_finite : ∀ s μ, Finite (lts.image s μ)] :
    Testable (Set (Proposition Label)) (HomBisimilarity lts) := by
  rw [← theoryEq_eq_bisimilarity lts, ← induced_hml lts]
  exact induced_testable (Set (Proposition Label)) (hmlTestClass lts)

end Cslib.LTS.Spectrum
