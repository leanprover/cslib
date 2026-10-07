/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.SearchReasons

/-!
# Cached bundles of constraint retirements

A bundle combines positive cached reasons into three numeric masks. Its composition is checked
once using the validated reason table. Each later use checks the combined requirements and
retires all the indicated constraints with one mask operation.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Search

open Counting

/-- Numeric masks sufficient to retire several constraints together. -/
structure BundleData where
  /-- Constraints justified by the constituent reasons. -/
  constraints : ℕ
  /-- Variables that must be true. -/
  onReq : ℕ
  /-- Variables that must be false. -/
  offReq : ℕ

/-- The combined requirements of a bundle. -/
def BundleData.cube (bundle : BundleData) : Cube := ⟨bundle.onReq, bundle.offReq⟩

/-- Compare numeric bundle data using kernel-reducible natural-number equality. -/
def BundleData.beq (bundle other : BundleData) : Bool :=
  Nat.beq bundle.constraints other.constraints && Nat.beq bundle.onReq other.onReq &&
    Nat.beq bundle.offReq other.offReq

/-- Successful numeric comparison identifies the complete bundle. -/
theorem BundleData.beq_eq_true (bundle other : BundleData) :
    bundle.beq other = true ↔ bundle = other := by
  rcases bundle with ⟨constraints, onReq, offReq⟩
  rcases other with ⟨otherConstraints, otherOnReq, otherOffReq⟩
  simp [beq, Nat.beq_eq, and_assoc]

/-- Add one reason to the combined requirement and constraint masks. -/
def BundleData.add (bundle : BundleData) (reason : ReasonData) : BundleData :=
  ⟨(1 <<< reason.constraint) ||| bundle.constraints,
    reason.onReq ||| bundle.onReq, reason.offReq ||| bundle.offReq⟩

/-- Every indicated constraint holds throughout the combined requirement cube. -/
def BundleData.Sound (bundle : BundleData) (problem : Problem) : Prop :=
  ∀ bits : Fin problem.variables → Bool, bundle.cube.Matches problem.variables bits →
    ∀ i < problem.constraints.size, Code.bitAt bundle.constraints i = true →
      problem.constraints.eval i (choiceMask bits) = true

/-- A matching combined cube satisfies both constituent requirement cubes. -/
theorem BundleData.add_matches (bundle : BundleData) (reason : ReasonData)
    {r : ℕ} {bits : Fin r → Bool} (hm : (bundle.add reason).cube.Matches r bits) :
    reason.cube.Matches r bits ∧ bundle.cube.Matches r bits := by
  constructor <;> constructor
  · intro i hi
    apply hm.1 i
    simp only [add, cube, ReasonData.cube, Code.bitAt_eq_testBit, Nat.testBit_or,
      Bool.or_eq_true] at hi ⊢
    exact Or.inl hi
  · intro i hi
    apply hm.2 i
    simp only [add, cube, ReasonData.cube, Code.bitAt_eq_testBit, Nat.testBit_or,
      Bool.or_eq_true] at hi ⊢
    exact Or.inl hi
  · intro i hi
    apply hm.1 i
    simp only [add, cube, Code.bitAt_eq_testBit, Nat.testBit_or,
      Bool.or_eq_true] at hi ⊢
    exact Or.inr hi
  · intro i hi
    apply hm.2 i
    simp only [add, cube, Code.bitAt_eq_testBit, Nat.testBit_or,
      Bool.or_eq_true] at hi ⊢
    exact Or.inr hi

/-- Combining an already sound bundle and a positive reason preserves soundness. -/
theorem BundleData.add_sound {bundle : BundleData} {reason : ReasonData} {problem : Problem}
    (hb : bundle.Sound problem) (hr : reason.Sound problem) (hp : reason.positive = true) :
    (bundle.add reason).Sound problem := by
  intro bits hm i hi hc
  have hm' := bundle.add_matches reason hm
  simp only [add, Code.bitAt_eq_testBit, Nat.testBit_or, Bool.or_eq_true,
    Nat.one_shiftLeft, Nat.testBit_two_pow] at hc
  rcases hc with hc | hc
  · have he : reason.constraint = i := by simpa using hc
    subst i
    simpa only [hp] using hr.eval bits hm'.1
  · exact hb bits hm'.2 i hi (by simpa only [Code.bitAt_eq_testBit] using hc)

/-- Compose bounded positive reason indices without rechecking the original constraints. -/
def BundleData.compose (table : ReasonTable) : List ℕ → Option BundleData
  | [] => some ⟨0, 0, 0⟩
  | index :: rest =>
    if Nat.blt index table.size && (table.lookup index).positive then do
      let bundle ← compose table rest
      return bundle.add (table.lookup index)
    else none

/-- Composition uses only the semantics already proved for the reason table. -/
theorem BundleData.compose_sound (problem : Problem) (hp : problem.PermutationsBounded)
    (table : ReasonTable) (hvalid : table.Valid problem) (indices : List ℕ)
    (bundle : BundleData) (h : compose table indices = some bundle) : bundle.Sound problem := by
  induction indices generalizing bundle with
  | nil =>
    simp only [compose, Option.some.injEq] at h
    subst bundle
    intro bits hm i hi hc
    simp [Code.bitAt_eq_testBit] at hc
  | cons index rest ih =>
    simp only [compose] at h
    split at h
    · rename_i hcheck
      simp only [Bool.and_eq_true, Nat.blt_eq] at hcheck
      cases he : compose table rest with
      | none => simp [he] at h
      | some previous =>
        have hb : previous.add (table.lookup index) = bundle := by simpa [he] using h
        subst bundle
        exact add_sound (ih previous he)
          (problem.reasonValid_sound hp _ (hvalid index hcheck.1)) hcheck.2
    · contradiction

/-- Validate positive reasons against a fixed cube while accumulating only constraint coverage. -/
def BundleData.checkReasons (bundle : BundleData) (table : ReasonTable) : List ℕ → ℕ → Bool
  | [], covered => Nat.beq covered bundle.constraints
  | index :: rest, covered =>
    Nat.blt index table.size && (table.lookup index).positive &&
      (table.lookup index).matchesCheck bundle.cube &&
      bundle.checkReasons table rest (covered ||| (1 <<< (table.lookup index).constraint))

/-- Checked positive reasons justify every constraint in the final coverage mask. -/
theorem BundleData.checkReasons_sound (problem : Problem) (hp : problem.PermutationsBounded)
    (table : ReasonTable) (hvalid : table.Valid problem) (bundle : BundleData)
    (indices : List ℕ) (covered : ℕ)
    (hcovered : ∀ bits : Fin problem.variables → Bool,
      bundle.cube.Matches problem.variables bits → ∀ i < problem.constraints.size,
        Code.bitAt covered i = true → problem.constraints.eval i (choiceMask bits) = true)
    (h : bundle.checkReasons table indices covered = true) : bundle.Sound problem := by
  induction indices generalizing covered with
  | nil =>
    simp only [checkReasons, Nat.beq_eq] at h
    subst covered
    exact hcovered
  | cons index rest ih =>
    simp only [checkReasons, Bool.and_eq_true, Nat.blt_eq] at h
    apply ih _ _ h.2
    intro bits hm i hi hc
    simp only [Code.bitAt_eq_testBit, Nat.testBit_or, Bool.or_eq_true,
      Nat.one_shiftLeft, Nat.testBit_two_pow] at hc
    rcases hc with hc | hc
    · exact hcovered bits hm i hi (by simpa only [Code.bitAt_eq_testBit] using hc)
    · have he : (table.lookup index).constraint = i := by simpa using hc
      subst i
      have hs := problem.reasonValid_sound hp _ (hvalid index h.1.1.1)
      simpa only [h.1.1.2] using
        hs.eval bits ((table.lookup index).matches_of_check h.1.2 hm)

/-- Decode a fixed number of reason indices from consecutive fields, lowest field first. -/
def decodeBundleIndices (width : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | count + 1, code =>
    match Code.field code 0 width with
    | 0 => 0 :: decodeBundleIndices width count (code >>> width)
    | index + 1 => (index + 1) :: decodeBundleIndices width count (code >>> width)

/-- Numeric bundle data and independent lists witnessing its composition. -/
structure BundleTable where
  /-- Number of stored bundles. -/
  size : ℕ
  /-- Numeric data used by the search checker. -/
  lookup : ℕ → BundleData
  /-- Cached reason indices used only during validation. -/
  reasons : ℕ → List ℕ

/-- Check one stored bundle against the positive reasons covering its constraint mask. -/
def BundleTable.checkEntry (table : BundleTable) (reasons : ReasonTable) (index : ℕ) : Bool :=
  (table.lookup index).checkReasons reasons (table.reasons index) 0

/-- Every bundle passes the positive-reason coverage and requirement checks. -/
def BundleTable.Valid (table : BundleTable) (reasons : ReasonTable) : Prop :=
  ∀ i < table.size, table.checkEntry reasons i = true

/-- Entry validation reuses cached reason soundness without inspecting original constraints. -/
theorem BundleTable.checkEntry_sound (problem : Problem) (hp : problem.PermutationsBounded)
    (reasons : ReasonTable) (hvalid : reasons.Valid problem) (table : BundleTable) (index : ℕ)
    (h : table.checkEntry reasons index = true) : (table.lookup index).Sound problem := by
  apply BundleData.checkReasons_sound problem hp reasons hvalid _ _ 0 _ h
  intro bits hm i hi hc
  simp [Code.bitAt_eq_testBit] at hc

/-- Check a bounded block of bundle entries, ignoring positions beyond the table. -/
def BundleTable.checkBlock (table : BundleTable) (reasons : ReasonTable)
    (blockSize block : ℕ) : Bool :=
  Code.allBelow (fun offset =>
    let index := block * blockSize + offset
    !Nat.blt index table.size || table.checkEntry reasons index) blockSize

/-- Independent bounded block proofs establish validity without repeating composition. -/
theorem BundleTable.valid_of_blocks (table : BundleTable) (reasons : ReasonTable)
    (blockSize : ℕ) (hpos : 0 < blockSize)
    (hblocks : ∀ block < table.size / blockSize + 1,
      table.checkBlock reasons blockSize block = true) : table.Valid reasons := by
  intro i hi
  have hblock : i / blockSize < table.size / blockSize + 1 :=
    Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt hi))
  have h := Code.allBelow_eq_true.mp (hblocks (i / blockSize) hblock)
    (i % blockSize) (Nat.mod_lt i hpos)
  have he : i / blockSize * blockSize + i % blockSize = i := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod i blockSize
  have hlt : Nat.blt i table.size = true := Nat.blt_eq.mpr hi
  simpa only [he, hlt, Bool.not_true, Bool.false_or] using h

/-- Check active membership and both combined requirement masks. -/
def BundleData.matchesCheck (bundle : BundleData) (state : ActiveSearch.State) : Bool :=
  Nat.beq (Nat.land bundle.constraints state.active) bundle.constraints &&
    Nat.beq (Nat.land bundle.onReq state.cube.on) bundle.onReq &&
    Nat.beq (Nat.land bundle.offReq state.cube.off) bundle.offReq

/-- A successful use check extends the combined requirement cube. -/
theorem BundleData.matches_of_check (bundle : BundleData) {r : ℕ}
    {state : ActiveSearch.State} {bits : Fin r → Bool}
    (h : bundle.matchesCheck state = true) (hm : state.cube.Matches r bits) :
    bundle.cube.Matches r bits := by
  simp only [matchesCheck, Bool.and_eq_true] at h
  exact ReasonData.matches_of_check ⟨0, true, bundle.onReq, bundle.offReq⟩
    (by simp only [ReasonData.matchesCheck, h.1.2, h.2, Bool.and_self]) hm

/-- Toggling a mask of already true constraints preserves validity of an assignment. -/
theorem valid_toggleBundle_iff (constraints : ActiveSearch.Constraints) (active mask remove : ℕ)
    (he : ∀ i < constraints.size, Code.bitAt remove i = true →
      constraints.eval i mask = true) :
    ActiveSearch.valid constraints (active ^^^ remove) mask = true ↔
      ActiveSearch.valid constraints active mask = true := by
  rw [ActiveSearch.valid_iff, ActiveSearch.valid_iff]
  constructor <;> intro h i hi hb
  · cases hc : Code.bitAt remove i
    · apply h i hi
      simpa only [Code.bitAt_eq_testBit, Nat.testBit_xor,
        show remove.testBit i = false by simpa only [Code.bitAt_eq_testBit] using hc,
        Bool.xor_false] using hb
    · exact he i hi hc
  · cases hc : Code.bitAt remove i
    · apply h i hi
      simpa only [Code.bitAt_eq_testBit, Nat.testBit_xor,
        show remove.testBit i = false by simpa only [Code.bitAt_eq_testBit] using hc,
        Bool.xor_false] using hb
    · exact he i hi hc

/-- Rules use individual reasons for conflicts and composed bundles for retirement. -/
def Problem.bundleRules (problem : Problem) (reasons : ReasonTable) (bundles : BundleTable) :
    Rules ActiveSearch.State :=
  { problem.reasonRules reasons with
    simplifyCheck := fun state witness =>
      Nat.blt witness bundles.size && (bundles.lookup witness).matchesCheck state
    simplify := fun state witness =>
      ⟨state.cube, state.active ^^^ (bundles.lookup witness).constraints⟩ }

/-- Cached bundle rules preserve the exact count of the original problem. -/
theorem Problem.bundleRules_sound (problem : Problem) (hp : problem.PermutationsBounded)
    (reasons : ReasonTable) (hvalid : reasons.Valid problem)
    (bundles : BundleTable) (hbundles : bundles.Valid reasons) :
    Counting.Sound (problem.bundleRules reasons bundles)
      (ActiveSearch.modelCount problem.variables problem.constraints) where
  reject := (problem.reasonRules_sound hp reasons hvalid).reject
  accept := (problem.reasonRules_sound hp reasons hvalid).accept
  split := (problem.reasonRules_sound hp reasons hvalid).split
  simplify state witness h := by
    change (Nat.blt witness bundles.size && (bundles.lookup witness).matchesCheck state) = true at h
    simp only [Bool.and_eq_true, Nat.blt_eq] at h
    have hs := bundles.checkEntry_sound problem hp reasons hvalid witness (hbundles witness h.1)
    unfold ActiveSearch.modelCount Cube.modelCount
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro bits hb
    have hm : state.cube.Matches problem.variables bits := (Finset.mem_filter.mp hb).2
    exact (valid_toggleBundle_iff problem.constraints state.active (choiceMask bits)
      (bundles.lookup witness).constraints
      (hs bits ((bundles.lookup witness).matches_of_check h.2 hm))).symm
  lookup := (problem.reasonRules_sound hp reasons hvalid).lookup

/-- Check a numeric certificate using independent reason, bundle, and reference data. -/
def Problem.checkBundleDataChunk (problem : Problem) (reasons : ReasonTable)
    (bundles : BundleTable) (references : ℕ → Option (CountData ActiveSearch.State))
    (state : ActiveSearch.State) (certificate : Certificate) : Option ℕ :=
  Counting.check
    (withReferencesData (problem.bundleRules reasons bundles) ActiveSearch.State.beq references)
    state certificate

/-- Separately validated tables and references give the exact original model count. -/
theorem Problem.checkBundleDataChunk_sound (problem : Problem) (hp : problem.PermutationsBounded)
    (reasons : ReasonTable) (hvalid : reasons.Valid problem)
    (bundles : BundleTable) (hbundles : bundles.Valid reasons)
    (references : ℕ → Option (CountData ActiveSearch.State))
    (hrefs : ReferencesValid (ActiveSearch.modelCount problem.variables problem.constraints)
      references) (state : ActiveSearch.State) (certificate : Certificate) (result : ℕ)
    (hcheck : problem.checkBundleDataChunk reasons bundles references state certificate =
      some result) :
    ActiveSearch.modelCount problem.variables problem.constraints state = result :=
  Counting.check_sound
    (withReferencesData_sound (problem.bundleRules_sound hp reasons hvalid bundles hbundles)
      ActiveSearch.State.beq (fun state other => (ActiveSearch.State.beq_eq_true state other).mp)
      references hrefs) certificate state result hcheck

end Cslib.RelationAlgebra.Search
