/-
Copyright (c) 2026 patchwright. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: patchwright
-/

module

public import Cslib.Init
public import Cslib.Foundations.Semantics.LTS.Spectrum.Galois
public import Cslib.Foundations.Semantics.LTS.Spectrum.MayTestingPoint
public import Cslib.Languages.CCS.Basic
public import Cslib.Languages.CCS.Semantics
public import Cslib.Foundations.Semantics.LTS.Execution
public import Cslib.Foundations.Semantics.LTS.OmegaExecution

/-!
# Spectrum must-testing point — must-testing equivalence is Galois-closed

The companion to `Spectrum.MayTestingPoint`. A process `p` *must pass* a test
`T` when **every maximal computation** of `p ∥ T` performs the success action.
A maximal computation is either a finite execution whose final state is stuck
(no outgoing transition), or an infinite (`OmegaExecution`) one — so divergence
without success fails must, as does deadlock without success. Two processes are
must-testing-equivalent when they must-pass exactly the same tests.

Like may-testing, must-testing equivalence is by definition the equivalence
induced by the class of must-test observers, so its closedness is definitional
(`induced_testable`).

## References

* [R. De Nicola & M. Hennessy, *Testing Equivalences for Processes*][DeNicolaHennessy1984].
-/

@[expose] public section

namespace Cslib.LTS.Spectrum

open Cslib CCS

variable
  {Name : Type u}
  {Constant : Type v}

/-- A state is *stuck* if it has no outgoing transition: a finite execution
    ending in a stuck state is maximal (cannot be extended). -/
def Stuck (lts : LTS State Label) (s : State) : Prop :=
  ¬ ∃ μ s', lts.Tr s μ s'

/-- `p` *must pass* test `T`: every maximal computation of `p ∥ T` performs
    `success`. A maximal computation is either a finite execution ending in a
    stuck state, or an infinite `OmegaExecution`; in both, success must appear
    among the labels. Divergence-without-success and deadlock-without-success
    both fail must. -/
def mustPass (defs : Constant → CCS.Process Name Constant → Prop)
    (success : CCS.Act Name) (p T : CCS.Process Name Constant) : Prop :=
  (∀ μs s₂ ss,
      (CCS.lts (defs := defs)).Execution (Process.par p T) μs s₂ ss →
      Stuck (CCS.lts (defs := defs)) s₂ →
      success ∈ μs) ∧
  (∀ ss μs,
      (CCS.lts (defs := defs)).OmegaExecution ss μs →
      ss 0 = Process.par p T →
      ∃ i, μs i = success)

/-- Must-testing equivalence: `p` and `q` must-pass exactly the same tests. -/
def MustEquiv (defs : Constant → CCS.Process Name Constant → Prop)
    (success : CCS.Act Name) (p q : CCS.Process Name Constant) : Prop :=
  ∀ T, mustPass defs success p T ↔ mustPass defs success q T

/-- The must-test observer of a process: the set of tests it must-pass. -/
def mustTests (defs : Constant → CCS.Process Name Constant → Prop)
    (success : CCS.Act Name) (p : CCS.Process Name Constant) :
    Set (CCS.Process Name Constant) :=
  { T | mustPass defs success p T }

/-- Test class for the must-testing point: the singleton must-test observer. -/
def mustTestClass (defs : Constant → CCS.Process Name Constant → Prop)
    (success : CCS.Act Name) :
    Set (CCS.Process Name Constant → Set (CCS.Process Name Constant)) :=
  { f | f = mustTests defs success }

/-- The equivalence induced by the must-test observer is must-testing equivalence. -/
theorem induced_mustTests_iff (defs : Constant → CCS.Process Name Constant → Prop)
    (success : CCS.Act Name) (p q : CCS.Process Name Constant) :
    induced (Set (CCS.Process Name Constant)) (mustTestClass defs success) p q ↔
      MustEquiv defs success p q := by
  simp only [induced, mustTestClass, Set.mem_setOf_eq, MustEquiv]
  constructor
  · intro h T
    have heq : mustTests defs success p = mustTests defs success q :=
      h (mustTests defs success) rfl
    rw [Set.ext_iff] at heq
    simp only [mustTests, Set.mem_setOf_eq] at heq
    exact heq T
  · intro h f hf
    subst hf
    ext T
    simp only [mustTests, Set.mem_setOf_eq]
    exact h T

/-- Function-equality form of `induced_mustTests_iff`. -/
theorem induced_mustTests (defs : Constant → CCS.Process Name Constant → Prop)
    (success : CCS.Act Name) :
    induced (Set (CCS.Process Name Constant)) (mustTestClass defs success) =
      MustEquiv defs success := by
  funext p q
  exact propext (induced_mustTests_iff defs success p q)

/-- **Must-testing point.** Must-testing equivalence is a closed element of the
    spectrum: it is testable for a CCS LTS with a distinguished success action. -/
theorem MustEquiv_testable (defs : Constant → CCS.Process Name Constant → Prop)
    (success : CCS.Act Name) :
    Testable (Set (CCS.Process Name Constant)) (MustEquiv defs success) := by
  rw [← induced_mustTests defs success]
  exact induced_testable (Set (CCS.Process Name Constant)) (mustTestClass defs success)

end Cslib.LTS.Spectrum
