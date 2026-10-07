/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Counting
public import Cslib.Foundations.RelationAlgebra.SearchProblem

/-!
# Isomorphism class counts from certified search

A presentation checks that a numeric search problem describes exactly the associative cycle
choices and the identity- and converse-preserving atom renamings for its signature. A successful
search certificate then proves the number of isomorphism classes, without listing their models.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Search

/-- A verified interpretation of a numeric search problem as a relation-algebra signature. -/
structure Problem.Presentation (j k : ℕ) (problem : Problem) where
  /-- One representative of each diversity-cycle orbit. -/
  reps : Fin problem.variables → Cycle j k
  /-- Every diversity triple is covered by a basis orbit. -/
  cover : ∀ c : Cycle j k, ∃ i,
    (some c.1, some c.2.1, some c.2.2) ∈ cycleOrbit (reps i)
  /-- Distinct basis indices represent distinct orbits. -/
  distinct : ∀ i l, (some (reps i).1, some (reps i).2.1, some (reps i).2.2) ∈
    cycleOrbit (reps l) ↔ i = l
  /-- Identity constants and cycle variables for the atom composition relation. -/
  slots : ℕ → ℕ → ℕ → ℕ
  /-- The numeric slot lookup has the required interpretation. -/
  slots_spec : CycleSlots reps slots
  /-- The diversity-atom renamings. -/
  renames : Fin problem.permutationCount → DiversityAtom j k → DiversityAtom j k
  /-- The extended atom renamings satisfy the algebraic requirements. -/
  rename_laws : ∀ q, Function.Injective (Option.map (renames q)) ∧
    Option.map (renames q) none = none ∧
    ∀ x : Atom j k, Option.map (renames q) x.converse =
      Atom.converse (Option.map (renames q) x)
  /-- All permitted atom renamings occur in the list. -/
  renames_exhaustive : ∀ f : Atom j k → Atom j k, Function.Injective f → f none = none →
    (∀ x, f x.converse = (f x).converse) → ∃ q, f = Option.map (renames q)
  /-- The numeric permutations stay within the cycle basis. -/
  permutations_bounded : problem.PermutationsBounded
  /-- The numeric permutation action agrees with the actual atom renamings. -/
  action_spec : ∀ (q : Fin problem.permutationCount) (i : Fin problem.variables),
    (some (renames q (reps i).1), some (renames q (reps i).2.1),
      some (renames q (reps i).2.2)) ∈ cycleOrbit
        (reps ⟨problem.permutations q i, permutations_bounded q q.isLt i i.isLt⟩)
  /-- The source quadruple for each equation. -/
  sources : ℕ → Code.Quadruple
  /-- Every listed equation comes from atomic associativity. -/
  sources_spec : sourcesCheck (atomCount j k) problem.equationCount slots
    problem.equations sources = true
  /-- An index of a listed equation for every nontrivial atomic associativity equation. -/
  equationCover : ℕ → ℕ → ℕ → ℕ → ℕ
  /-- No associativity equation is omitted. -/
  equationCover_spec : equationsCoverCheck (atomCount j k) problem.equationCount slots
    problem.equations equationCover = true

variable {j k : ℕ} {problem : Problem}

/-- The complete numeric predicate selects exactly the canonical associative cycle masks. -/
theorem Problem.Presentation.valid_iff (presentation : problem.Presentation j k)
    {mask : ℕ} (hm : mask < 2 ^ problem.variables) :
    problem.valid mask = true ↔
      IsCanonicalMask presentation.reps (fun q => Option.map (presentation.renames q)) mask := by
  rw [Problem.valid_iff, IsCanonicalMask]
  have hassoc := associative_iff_equations presentation.reps presentation.slots
    presentation.slots_spec problem.equations presentation.sources presentation.equationCover
    presentation.sources_spec presentation.equationCover_spec hm
  rw [Code.allBelow_eq_true] at hassoc
  refine and_congr hassoc.symm ?_
  have hprofile (q : Fin problem.permutationCount) :=
    renamedMask_eq_permuteProfile presentation.reps presentation.distinct
      (presentation.renames q)
      (fun i => ⟨problem.permutations q i,
        presentation.permutations_bounded q q.isLt i i.isLt⟩)
      (presentation.action_spec q) hm
  constructor
  · intro h q
    rw [hprofile q]
    exact h q q.isLt
  · intro h q hq
    have hh := h ⟨q, hq⟩
    rw [hprofile ⟨q, hq⟩] at hh
    exact hh

/-- An exact count of the initial search state counts relation-algebra isomorphism classes. -/
theorem Problem.Presentation.count_eq_of_initial (presentation : problem.Presentation j k)
    (result : ℕ)
    (hcount : Counting.ActiveSearch.modelCount problem.variables problem.constraints
      (Counting.ActiveSearch.initial problem.constraints) = result) :
    isomorphismClassCount j k = result := by
  rw [isomorphismClassCount_eq_canonicalMaskCount presentation.reps presentation.cover
    presentation.distinct (fun q => Option.map (presentation.renames q))
    presentation.rename_laws presentation.renames_exhaustive,
    canonicalMaskCount_eq_card_filter presentation.reps
      (fun q => Option.map (presentation.renames q)) problem.valid
      (fun _ hm => presentation.valid_iff hm)]
  rw [Counting.ActiveSearch.modelCount_initial_masks] at hcount
  exact hcount

/-- A checked search certificate proves the number of relation-algebra isomorphism classes. -/
theorem Problem.Presentation.count_eq_of_check (presentation : problem.Presentation j k)
    (certificate : Counting.Certificate) (result : ℕ)
    (hcheck : problem.check certificate = some result) :
    isomorphismClassCount j k = result := by
  apply presentation.count_eq_of_initial result
  exact Counting.check_sound
    (Counting.ActiveSearch.rules_sound
      (problem.constraints_sound presentation.permutations_bounded))
    certificate (Counting.ActiveSearch.initial problem.constraints) result hcheck

end Cslib.RelationAlgebra.Search
