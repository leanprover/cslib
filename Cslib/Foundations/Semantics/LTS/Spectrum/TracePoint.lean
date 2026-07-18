/-
Copyright (c) 2026 patchwright. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: patchwright
-/

module

public import Cslib.Init
public import Cslib.Foundations.Semantics.LTS.TraceEq
public import Cslib.Foundations.Semantics.LTS.Spectrum.Galois

/-!
# Spectrum trace point — trace equivalence is Galois-closed

A concrete named spectrum point: CSLib's homogeneous trace equivalence
(`Cslib.LTS.HomTraceEq`) is a Galois-closed (testable) equivalence, via the
trace-set observer test class (`fun s => lts.traces s`, `Ω = Set (List Label)`).
`HomTraceEq` lies in the image of `induced`, hence is a fixed point of the
closure operator `cl`.

This proves the structural result (TraceEq ∈ closed elements). The standard
testing-semantics refinement — one `Bool` test per trace — gives a finer witness
for the SAME closed element but requires decidability of trace membership; it
does not change the closed-element verdict.

The Hennessy–Milner theorem IS mechanised in CSLib as
`Cslib.Logic.HML.theoryEq_eq_bisimilarity`; the bisim point built on it is in
`Spectrum.BisimPoint`. This file (the trace point, kernel-trivial bottom) does
not use HM — bisimilarity (HM-mediated top) is the companion point there.
-/

@[expose] public section

namespace Cslib.LTS.Spectrum

open Cslib

variable {State Label : Type*} (lts : LTS State Label)

/-- The trace-set observer test: a state's full set of traces. -/
def traceSetTest (s : State) : Set (List Label) :=
  lts.traces s

/-- Test class for the trace point: the singleton trace-set observer. -/
def traceTestClass : Set (State → Set (List Label)) :=
  { f | f = traceSetTest lts }

/-- The equivalence induced by the trace-set test is CSLib's homogeneous trace
    equivalence (pointwise iff). -/
theorem induced_traceSet_iff (p q : State) :
    induced (Set (List Label)) (traceTestClass lts) p q ↔ HomTraceEq lts p q := by
  constructor
  · intro h
    exact h _ rfl
  · intro h t ht
    have ht : t = traceSetTest lts := ht
    subst ht
    exact h

/-- Function-equality form (via `propext`). -/
theorem induced_traceSet :
    induced (Set (List Label)) (traceTestClass lts) = HomTraceEq lts := by
  funext p q
  exact propext (induced_traceSet_iff lts p q)

/-- **Trace point.** CSLib's homogeneous trace equivalence is a Galois-closed
    (testable) equivalence. -/
theorem HomTraceEq_testable :
    Testable (Set (List Label)) (HomTraceEq lts) := by
  rw [← induced_traceSet lts]
  exact induced_testable (Set (List Label)) (traceTestClass lts)

end Cslib.LTS.Spectrum
