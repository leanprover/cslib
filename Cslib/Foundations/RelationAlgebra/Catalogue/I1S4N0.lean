/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Coverage
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Models

/-!
# Classification of the ⟨1, 4, 0⟩ catalogue row

There are exactly 3013 isomorphism classes of integral relation algebras with 4 symmetric
diversity atoms and 0 converse pairs. The numbered entries are arranged by increasing canonical
cycle mask; this deterministic order is independent of numbering in any external source.
The unique-index classification proves exhaustiveness and absence of duplicates for arbitrary
relation algebras satisfying `HasSignature A 1 4 0`.

The proof checks all 1048576 choices of Peircean cycle orbits in parallel using truth words,
and distinguishes models by the least cycle profile under identity- and converse-preserving
atom permutations. This module makes no assertion about representability.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0

/-- The explicitly defined cycle tables, ordered by increasing canonical cycle mask. -/
def table (idx : Fin 3013) : IntegralCycleTable 4 0 := (Models.get idx.val).table

/-- The 3013 explicitly listed algebras, with zero-based catalogue indices. -/
abbrev Model (idx : Fin 3013) : Type := Complex (table idx)

private theorem cycles_exhaustive : ∀ bits : Fin 20 → Bool,
    AtomCompositionAssociative (selectedCycles Data.cycleReps bits) →
      ∃ i : Fin 3013, ∃ f,
        AtomRelabelling (selectedCycles Data.cycleReps bits) (table i).cycles f := by
  exact cycles_exhaustive_of_truthTable Data.cycleReps Data.cycleReps_cover
    Data.cycleReps_distinct table Data.rename Data.rename_laws Data.profiles
    Models.profiles_spec Coverage.words
    (fun _ hm => bitAt_cycleWord_of_slots Data.cycleReps Data.slots Data.slots_spec hm)
    Coverage.quads Coverage.quads_lt Coverage.check

private theorem cycles_distinct : ∀ i l : Fin 3013, ∀ f,
    AtomRelabelling (table i).cycles (table l).cycles f → i = l := by
  apply cycles_distinct_of_minimal_profiles Data.cycleReps table Data.rename 0
    Data.rename_zero Data.renamings_exhaustive (fun i p => Data.profiles i.val p.val)
    Models.profiles_spec Models.profiles_minimal
  intro i l h
  apply Models.canonicalMask_strictMono.injective
  change Data.profiles i.val 0 = Data.profiles l.val 0 at h
  simpa only [Models.profiles_zero] using h

/-- Every algebra of this signature is isomorphic to exactly one explicitly listed model. -/
theorem classification (A : Type*) [RelationAlgebra A] (h : HasSignature A 1 4 0) :
    ∃! idx : Fin 3013, Nonempty (RelationAlgebraEquiv A (Model idx)) := by
  exact classification_of_cycle_basis Data.cycleReps Data.cycleReps_cover table
    cycles_exhaustive cycles_distinct A h

end Cslib.RelationAlgebra.Catalogue.I1S4N0
