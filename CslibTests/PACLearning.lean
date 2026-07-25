import Cslib.MachineLearning.PACLearning.VersionSpace

namespace CslibTests.PACLearning

open Cslib.MachineLearning.PACLearning

/-- A learner on two samples over a singleton domain that predicts the first label. -/
def firstLabelLearner : Learner Unit Bool 2 :=
  fun S _ => (S 0).2

/-- Two different labels for the same point form an unrealizable sample. -/
def contradictorySample : LabeledSample Unit Bool 2 :=
  fun i => if i = 0 then ((), false) else ((), true)

theorem contradictorySample_not_realizable :
    ¬ Realizable (Set.univ : ConceptClass Unit Bool) contradictorySample := by
  rintro ⟨c, _, hc⟩
  simpa [contradictorySample] using
    (hc (0 : Fin 2)).trans (hc (1 : Fin 2)).symm

/-- Regression: consistency does not require a learner to fit an unrealizable
contradictory sample. -/
theorem firstLabelLearner_consistent :
    IsConsistent firstLabelLearner (Set.univ : ConceptClass Unit Bool) := by
  intro S hS
  obtain ⟨c, _, hc⟩ := hS
  rw [mem_versionSpace_iff]
  refine ⟨Set.mem_univ _, fun i => ?_⟩
  change (S 0).2 = (S i).2
  calc
    (S 0).2 = c (S 0).1 := hc 0
    _ = c (S i).1 := congrArg c (Subsingleton.elim _ _)
    _ = (S i).2 := (hc i).symm

example :
    firstLabelLearner contradictorySample (contradictorySample 1).1 ≠
      (contradictorySample 1).2 := by
  simp [firstLabelLearner, contradictorySample]

/-- A realizable sample used to guard the positive consistency guarantee. -/
def constantTrueSample : LabeledSample Unit Bool 2 :=
  fun _ => ((), true)

theorem constantTrueSample_realizable :
    Realizable (Set.univ : ConceptClass Unit Bool) constantTrueSample := by
  refine ⟨fun _ => true, Set.mem_univ _, ?_⟩
  intro i
  rfl

example (i : Fin 2) :
    firstLabelLearner constantTrueSample (constantTrueSample i).1 =
      (constantTrueSample i).2 :=
  firstLabelLearner_consistent.output_agrees
    constantTrueSample constantTrueSample_realizable i

end CslibTests.PACLearning
