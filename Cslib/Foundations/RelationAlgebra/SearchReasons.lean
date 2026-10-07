/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.SearchChunks
public import Cslib.Foundations.RelationAlgebra.SearchBitCount

/-!
# Cached reasons for certified search

A reason describes a small cube on which one constraint is always true or always false.
Its validity is checked once, independently of the counting certificate. Later uses need only
check that the current cube extends the reason's requirements. Numeric reason tables are kept
separate from their validity proofs, so checking a search chunk does not repeat these proofs.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Search

open Counting

/-- Closed numeric table data with balanced branch selection during kernel reduction. -/
inductive LookupTree (α : Type*) where
  /-- An absent entry, interpreted using the lookup default. -/
  | empty
  /-- A stored value. -/
  | leaf (value : α)
  /-- Indices below the pivot use the left subtree; all others use the right subtree. -/
  | branch (pivot : ℕ) (left right : LookupTree α)

/-- Look up a numeric index without substituting it throughout a large table expression. -/
def LookupTree.get (default : α) : LookupTree α → ℕ → α
  | .empty, _ => default
  | .leaf value, _ => value
  | .branch pivot left right, index =>
    if Nat.blt index pivot then get default left index else get default right index

/-- Numeric data describing sufficient assignments for the value of one constraint. -/
structure ReasonData where
  /-- The constraint justified by this reason. -/
  constraint : ℕ
  /-- Whether every matching assignment satisfies or falsifies the constraint. -/
  positive : Bool
  /-- Variables that must be true. -/
  onReq : ℕ
  /-- Variables that must be false. -/
  offReq : ℕ

/-- The partial assignment on which a reason is valid. -/
def ReasonData.cube (reason : ReasonData) : Cube := ⟨reason.onReq, reason.offReq⟩

/-- Check that a current cube contains all assignments required by the reason. -/
def ReasonData.matchesCheck (reason : ReasonData) (cube : Cube) : Bool :=
  Nat.beq (Nat.land reason.onReq cube.on) reason.onReq &&
    Nat.beq (Nat.land reason.offReq cube.off) reason.offReq

/-- Extending the requirement masks also extends the reason's semantic cube. -/
theorem ReasonData.matches_of_check (reason : ReasonData) {r : ℕ} {cube : Cube}
    {bits : Fin r → Bool} (h : reason.matchesCheck cube = true) (hm : cube.Matches r bits) :
    reason.cube.Matches r bits := by
  simp only [matchesCheck, Bool.and_eq_true, Nat.beq_eq] at h
  have hon : MaskSubset reason.onReq cube.on := h.1
  have hoff : MaskSubset reason.offReq cube.off := h.2
  constructor
  · intro i hi
    apply hm.1 i
    simpa only [Code.bitAt_eq_testBit] using
      maskSubset_iff.mp hon i (by simpa only [ReasonData.cube, Code.bitAt_eq_testBit] using hi)
  · intro i hi
    apply hm.2 i
    simpa only [Code.bitAt_eq_testBit] using
      maskSubset_iff.mp hoff i (by simpa only [ReasonData.cube, Code.bitAt_eq_testBit] using hi)

/-- A reason refers to an actual constraint and determines its value throughout its cube. -/
structure ReasonData.Sound (problem : Problem) (reason : ReasonData) : Prop where
  /-- The constraint index is valid. -/
  constraint_lt : reason.constraint < problem.constraints.size
  /-- Every completion of the requirement masks has the advertised constraint value. -/
  eval : ∀ bits : Fin problem.variables → Bool, reason.cube.Matches problem.variables bits →
    problem.constraints.eval reason.constraint (choiceMask bits) = reason.positive

/-- Validate a reason using the original proved partial-assignment checker. -/
def Problem.reasonValid (problem : Problem) (reason : ReasonData) : Bool :=
  Nat.blt reason.constraint problem.constraints.size &&
    if reason.positive then problem.constraints.settled reason.constraint reason.cube
    else problem.constraints.conflict reason.constraint reason.cube

/-- An independently validated reason has the required pointwise semantics. -/
theorem Problem.reasonValid_sound (problem : Problem) (hp : problem.PermutationsBounded)
    (reason : ReasonData) (h : problem.reasonValid reason = true) : reason.Sound problem := by
  simp only [reasonValid, Bool.and_eq_true, Nat.blt_eq] at h
  refine ⟨h.1, fun bits hm => ?_⟩
  cases hb : reason.positive
  · exact (problem.constraints_sound hp).conflict reason.constraint h.1 reason.cube bits
      (by simpa only [hb, Bool.false_eq_true, ↓reduceIte] using h.2) hm
  · exact (problem.constraints_sound hp).settled reason.constraint h.1 reason.cube bits
      (by simpa only [hb, ↓reduceIte] using h.2) hm

/-- A finite numeric reason table; its semantic validation is supplied separately. -/
structure ReasonTable where
  /-- Number of stored reasons. -/
  size : ℕ
  /-- Numeric lookup, implemented independently of the proof of validity. -/
  lookup : ℕ → ReasonData

/-- Every in-range entry passes the original partial-assignment checker. -/
def ReasonTable.Valid (table : ReasonTable) (problem : Problem) : Prop :=
  ∀ i < table.size, problem.reasonValid (table.lookup i) = true

/-- Check a bounded block of reason entries; positions past the end are ignored. -/
def ReasonTable.checkBlock (table : ReasonTable) (problem : Problem)
    (blockSize block : ℕ) : Bool :=
  Code.allBelow (fun offset =>
    let index := block * blockSize + offset
    !Nat.blt index table.size || problem.reasonValid (table.lookup index)) blockSize

/-- Independent block proofs establish validity of the whole table without reducing it again. -/
theorem ReasonTable.valid_of_blocks (table : ReasonTable) (problem : Problem) (blockSize : ℕ)
    (hpos : 0 < blockSize)
    (hblocks : ∀ block < table.size / blockSize + 1,
      table.checkBlock problem blockSize block = true) : table.Valid problem := by
  intro i hi
  have hblock : i / blockSize < table.size / blockSize + 1 :=
    Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt hi))
  have h := Code.allBelow_eq_true.mp (hblocks (i / blockSize) hblock)
    (i % blockSize) (Nat.mod_lt i hpos)
  have he : i / blockSize * blockSize + i % blockSize = i := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod i blockSize
  have hlt : Nat.blt i table.size = true := Nat.blt_eq.mpr hi
  simpa only [he, hlt, Bool.not_true, Bool.false_or] using h

/-- Rules whose witnesses name cached reasons instead of rerunning constraint predicates. -/
def Problem.reasonRules (problem : Problem) (table : ReasonTable) : Rules ActiveSearch.State :=
  { ActiveSearch.rules problem.variables problem.constraints with
    freeCount := fun state => Cube.fastFreeCount problem.variables state.cube
    rejectCheck := fun state witness =>
      let reason := table.lookup witness
      Nat.blt witness table.size && !reason.positive &&
        Code.bitAt state.active reason.constraint && reason.matchesCheck state.cube
    simplifyCheck := fun state witness =>
      let reason := table.lookup witness
      Nat.blt witness table.size && reason.positive &&
        Code.bitAt state.active reason.constraint && reason.matchesCheck state.cube
    simplify := fun state witness => ActiveSearch.retire state (table.lookup witness).constraint }

/-- Cached reasons preserve the exact model count of the original constraint problem. -/
theorem Problem.reasonRules_sound (problem : Problem) (hp : problem.PermutationsBounded)
    (table : ReasonTable) (hvalid : table.Valid problem) :
    Counting.Sound (problem.reasonRules table)
      (ActiveSearch.modelCount problem.variables problem.constraints) where
  reject state witness h := by
    change (Nat.blt witness table.size && !(table.lookup witness).positive &&
      Code.bitAt state.active (table.lookup witness).constraint &&
      (table.lookup witness).matchesCheck state.cube) = true at h
    simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.blt_eq] at h
    have hs := problem.reasonValid_sound hp _ (hvalid witness h.1.1.1)
    apply Cube.modelCount_eq_zero
    intro bits hm
    have hf := hs.eval bits ((table.lookup witness).matches_of_check h.2 hm)
    rw [h.1.1.2] at hf
    apply Bool.eq_false_iff.mpr
    intro hv
    have ht := (ActiveSearch.valid_iff problem.constraints state.active (choiceMask bits)).mp hv
      (table.lookup witness).constraint hs.constraint_lt h.1.2
    rw [hf] at ht
    contradiction
  accept state h := by
    change ActiveSearch.modelCount problem.variables problem.constraints state =
      Cube.fastFreeCount problem.variables state.cube
    rw [Cube.fastFreeCount_eq]
    exact (ActiveSearch.rules_sound (problem.constraints_sound hp)).accept state h
  split := (ActiveSearch.rules_sound (problem.constraints_sound hp)).split
  simplify state witness h := by
    change (Nat.blt witness table.size && (table.lookup witness).positive &&
      Code.bitAt state.active (table.lookup witness).constraint &&
      (table.lookup witness).matchesCheck state.cube) = true at h
    simp only [Bool.and_eq_true, Nat.blt_eq] at h
    have hs := problem.reasonValid_sound hp _ (hvalid witness h.1.1.1)
    change ActiveSearch.modelCount problem.variables problem.constraints state =
      ActiveSearch.modelCount problem.variables problem.constraints
        (ActiveSearch.retire state (table.lookup witness).constraint)
    unfold ActiveSearch.modelCount Cube.modelCount
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro bits hb
    have hm : state.cube.Matches problem.variables bits := (Finset.mem_filter.mp hb).2
    have he := hs.eval bits ((table.lookup witness).matches_of_check h.2 hm)
    rw [h.1.1.2] at he
    exact (ActiveSearch.valid_toggle_iff problem.constraints state.active (choiceMask bits)
      (table.lookup witness).constraint he).symm
  lookup := (ActiveSearch.rules_sound (problem.constraints_sound hp)).lookup

/-- Check one search chunk using cached reasons and previously certified counts. -/
def Problem.checkReasonChunk (problem : Problem) (table : ReasonTable)
    (references : ℕ → Option problem.CertifiedCount) (state : ActiveSearch.State)
    (certificate : Certificate) : Option ℕ :=
  Counting.check (withReferences (problem.reasonRules table) ActiveSearch.State.beq references)
    state certificate

/-- A successful chunk with a validated reason table gives the exact original model count. -/
theorem Problem.checkReasonChunk_sound (problem : Problem) (hp : problem.PermutationsBounded)
    (table : ReasonTable) (hvalid : table.Valid problem)
    (references : ℕ → Option problem.CertifiedCount) (state : ActiveSearch.State)
    (certificate : Certificate) (result : ℕ)
    (hcheck : problem.checkReasonChunk table references state certificate = some result) :
    ActiveSearch.modelCount problem.variables problem.constraints state = result :=
  Counting.check_sound
    (withReferences_sound (problem.reasonRules_sound hp table hvalid)
      ActiveSearch.State.beq (fun state other => (ActiveSearch.State.beq_eq_true state other).mp)
      references) certificate state result hcheck

/-- Package a chunk proved with cached reasons for use by later chunks. -/
def Problem.certifyReasonChunk (problem : Problem) (hp : problem.PermutationsBounded)
    (table : ReasonTable) (hvalid : table.Valid problem)
    (references : ℕ → Option problem.CertifiedCount) (state : ActiveSearch.State)
    (certificate : Certificate) (result : ℕ)
    (hcheck : problem.checkReasonChunk table references state certificate = some result) :
    problem.CertifiedCount :=
  ⟨state, result, problem.checkReasonChunk_sound hp table hvalid references state certificate
    result hcheck⟩

/-- Check a reason-based chunk using reference data that contains no count proofs. -/
def Problem.checkReasonDataChunk (problem : Problem) (table : ReasonTable)
    (references : ℕ → Option (CountData ActiveSearch.State)) (state : ActiveSearch.State)
    (certificate : Certificate) : Option ℕ :=
  Counting.check (withReferencesData (problem.reasonRules table) ActiveSearch.State.beq references)
    state certificate

/-- Numeric chunk checks and separately proved references establish the original model count. -/
theorem Problem.checkReasonDataChunk_sound (problem : Problem) (hp : problem.PermutationsBounded)
    (table : ReasonTable) (hvalid : table.Valid problem)
    (references : ℕ → Option (CountData ActiveSearch.State))
    (hrefs : ReferencesValid (ActiveSearch.modelCount problem.variables problem.constraints)
      references)
    (state : ActiveSearch.State) (certificate : Certificate) (result : ℕ)
    (hcheck : problem.checkReasonDataChunk table references state certificate = some result) :
    ActiveSearch.modelCount problem.variables problem.constraints state = result :=
  Counting.check_sound
    (withReferencesData_sound (problem.reasonRules_sound hp table hvalid)
      ActiveSearch.State.beq (fun state other => (ActiveSearch.State.beq_eq_true state other).mp)
      references hrefs) certificate state result hcheck

end Cslib.RelationAlgebra.Search
