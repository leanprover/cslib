/-
Copyright (c) 2026 patchwright. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: patchwright
-/

module

public import Cslib.Init
public import Cslib.Foundations.Semantics.LTS.Spectrum.Galois
public import Cslib.Languages.CCS.Basic
public import Cslib.Languages.CCS.Semantics
public import Cslib.Foundations.Semantics.LTS.HasTau

/-!
# Spectrum may-testing point — may-testing equivalence is Galois-closed

A named point of the van Glabbeek spectrum: (may-)testing equivalence
[De Nicola & Hennessy, 1984]. A *test* is a process together with a distinguished
*success* action; a process `p` *may pass* a test `T` when some computation of
`p ∥ T` performs the success action. Two processes are may-testing-equivalent
when they may-pass exactly the same tests.

Unlike the bisim point — where bisimilarity is connected to the spectrum via the
Hennessy–Milner theorem — may-testing equivalence is, by its standard
definition, exactly the equivalence induced by the class of may-test observers.
Its closedness is therefore definitional (as for `Spectrum.TracePoint`): it is
`induced` of the may-test class, and every induced equivalence is testable.

## References

* [R. De Nicola & M. Hennessy, *Testing Equivalences for Processes*][DeNicolaHennessy1984].
-/

@[expose] public section

namespace Cslib.LTS.Spectrum

open Cslib CCS

variable
  {Name : Type u}
  {Constant : Type v}

/-- `p` *may pass* test `T`: some computation of `p ∥ T` performs `success`
    (it appears among the labels of a multistep computation of the parallel
    composition). Strong, matching `MustTestingPoint.mustPass`. -/
def mayPass (defs : Constant → CCS.Process Name Constant → Prop)
    (success : CCS.Act Name) (p T : CCS.Process Name Constant) : Prop :=
  ∃ μs s', (CCS.lts (defs := defs)).MTr (Process.par p T) μs s' ∧ success ∈ μs

/-- May-testing equivalence: `p` and `q` may-pass exactly the same tests. -/
def MayEquiv (defs : Constant → CCS.Process Name Constant → Prop)
    (success : CCS.Act Name) (p q : CCS.Process Name Constant) : Prop :=
  ∀ T, mayPass defs success p T ↔ mayPass defs success q T

/-- The may-test observer of a process: the set of tests it may-pass. -/
def mayTests (defs : Constant → CCS.Process Name Constant → Prop)
    (success : CCS.Act Name) (p : CCS.Process Name Constant) :
    Set (CCS.Process Name Constant) :=
  { T | mayPass defs success p T }

/-- Test class for the may-testing point: the singleton may-test observer. -/
def mayTestClass (defs : Constant → CCS.Process Name Constant → Prop)
    (success : CCS.Act Name) :
    Set (CCS.Process Name Constant → Set (CCS.Process Name Constant)) :=
  { f | f = mayTests defs success }

/-- The equivalence induced by the may-test observer is may-testing equivalence. -/
theorem induced_mayTests_iff (defs : Constant → CCS.Process Name Constant → Prop)
    (success : CCS.Act Name) (p q : CCS.Process Name Constant) :
    induced (Set (CCS.Process Name Constant)) (mayTestClass defs success) p q ↔
      MayEquiv defs success p q := by
  simp only [induced, mayTestClass, Set.mem_setOf_eq, MayEquiv]
  constructor
  · intro h T
    have heq : mayTests defs success p = mayTests defs success q :=
      h (mayTests defs success) rfl
    rw [Set.ext_iff] at heq
    simp only [mayTests, Set.mem_setOf_eq] at heq
    exact heq T
  · intro h f hf
    subst hf
    ext T
    simp only [mayTests, Set.mem_setOf_eq]
    exact h T

/-- Function-equality form of `induced_mayTests_iff`. -/
theorem induced_mayTests (defs : Constant → CCS.Process Name Constant → Prop)
    (success : CCS.Act Name) :
    induced (Set (CCS.Process Name Constant)) (mayTestClass defs success) =
      MayEquiv defs success := by
  funext p q
  exact propext (induced_mayTests_iff defs success p q)

/-- **May-testing point.** May-testing equivalence is a closed element of the
    spectrum: it is testable for a CCS LTS with a distinguished success action. -/
theorem MayEquiv_testable (defs : Constant → CCS.Process Name Constant → Prop)
    (success : CCS.Act Name) :
    Testable (Set (CCS.Process Name Constant)) (MayEquiv defs success) := by
  rw [← induced_mayTests defs success]
  exact induced_testable (Set (CCS.Process Name Constant)) (mayTestClass defs success)

end Cslib.LTS.Spectrum
