/-
Copyright (c) 2026 TODO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TODO
-/

module

public import Cslib.Init
public import Cslib.Foundations.Semantics.LTS.Spectrum.Galois

/-!
# Spectrum antichain — the closed-element lattice is not a chain

The closed-element lattice is NOT totally ordered by refinement: two
incomparable Galois-closed (testable) equivalences exist over a 4-state witness
space. Two test classes `T₁`, `T₂` (Ω = Bool) induce closed equivalences such
that neither refines the other:
  - states a,b are `T₁`-equivalent but `T₂`-distinct;
  - states a,c are `T₂`-equivalent but `T₁`-distinct.
Hence the closed-element lattice contains an antichain → it is a lattice, not a
chain (scale). This is the structural form of the "linear-time/branching-time
spectrum is a lattice, not a linear scale" claim.

(The *named* van Glabbeek antichain — simulation vs failures equivalence —
requires failures semantics, not yet in CSLib; that named instance is separate
from the structural result here.)
-/

@[expose] public section

namespace Cslib.LTS.Spectrum

/-- 4-state witness space. -/
inductive W where
  | a | b | c | d

open W

/-- Test t₁: groups {a,b} (true) vs {c,d} (false). -/
def t1 : W → Bool
  | a | b => true
  | c | d => false

/-- Test t₂: groups {a,c} (true) vs {b,d} (false). -/
def t2 : W → Bool
  | a | c => true
  | b | d => false

/-- Test classes (singletons, written as comprehensions). -/
def T1 : Set (W → Bool) := { f | f = t1 }
def T2 : Set (W → Bool) := { f | f = t2 }

/-- a,b are `T₁`-equivalent but `T₂`-distinct. -/
theorem T1_ab_not_T2_ab : induced Bool T1 a b ∧ ¬ induced Bool T2 a b := by
  refine ⟨?_, ?_⟩
  · intro t ht
    have ht : t = t1 := ht
    subst ht
    rfl
  · intro h
    have hh : t2 a = t2 b := h t2 rfl
    simp only [t2] at hh
    exact Bool.noConfusion hh

/-- a,c are `T₂`-equivalent but `T₁`-distinct. -/
theorem T2_ac_not_T1_ac : induced Bool T2 a c ∧ ¬ induced Bool T1 a c := by
  refine ⟨?_, ?_⟩
  · intro t ht
    have ht : t = t2 := ht
    subst ht
    rfl
  · intro h
    have hh : t1 a = t1 c := h t1 rfl
    simp only [t1] at hh
    exact Bool.noConfusion hh

/-- **The closed-element lattice is not a chain.** There exist two incomparable
    testable (Galois-closed) equivalences. -/
theorem exists_incomparable_closed :
    ∃ E₁ E₂ : W → W → Prop,
      Testable Bool E₁ ∧ Testable Bool E₂ ∧
        ¬ (∀ p q, E₁ p q → E₂ p q) ∧ ¬ (∀ p q, E₂ p q → E₁ p q) := by
  refine ⟨induced Bool T1, induced Bool T2,
          induced_testable Bool T1, induced_testable Bool T2, ?_, ?_⟩
  · intro h
    exact T1_ab_not_T2_ab.2 (h a b T1_ab_not_T2_ab.1)
  · intro h
    exact T2_ac_not_T1_ac.2 (h a c T2_ac_not_T1_ac.1)

end Cslib.LTS.Spectrum
