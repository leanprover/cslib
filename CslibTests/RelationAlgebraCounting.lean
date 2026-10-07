/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

import Cslib.Foundations.RelationAlgebra.SearchBundles
import Cslib.Foundations.RelationAlgebra.SearchData

/-!
# Certified relation-algebra search regressions

Independent small problems exercise exact counts, forced assignments, constraint retirement,
chunk references, and cached reasons. Concrete checks use kernel reduction. Count examples also
instantiate the corresponding soundness theorem.
-/

namespace CslibTests.RelationAlgebraCounting

open Cslib.RelationAlgebra Cslib.RelationAlgebra.Search Cslib.RelationAlgebra.Counting

-- String data elaborates to exact Nat literals, including values beyond machine-word bounds.
example : nat_lit% "0" = 0 := rfl
example : nat_lit% "00017" = 17 := rfl
example : nat_lit% "18446744073709551616" = 18446744073709551616 := rfl
example : nat_lit% "340282366920938463463\
  374607431768211456" = 340282366920938463463374607431768211456 := rfl

/-- error: expected a nonempty string of decimal digits -/
#guard_msgs in
#check nat_lit% "12x"

/-- error: expected a nonempty string of decimal digits -/
#guard_msgs in
#check nat_lit% ""

-- Certificate literals construct the same ordinary data as explicit constructors.
example : certificate_lit% "a" [] = Certificate.accept := rfl
example : certificate_lit% "r 17" [] = Certificate.reject 17 := rfl
example : certificate_lit% "c 2" [] = Certificate.reference 2 := rfl
example : certificate_lit% "b 0 f 1 0 2 s 3 a f 1 1 4 s 5 a" [] =
    Certificate.branch 0 (.force 1 false 2 (.simplify 3 .accept))
      (.force 1 true 4 (.simplify 5 .accept)) := rfl

private def literalHelper : Certificate := .simplify 9 .accept

example : certificate_lit% "b 0 h 0 \
  h 0" [literalHelper] = Certificate.branch 0 literalHelper literalHelper := rfl

/-- error: invalid certificate literal: unknown instruction tag -/
#guard_msgs in
#check certificate_lit% "x" []

/-- error: invalid certificate literal: unexpected end of input -/
#guard_msgs in
#check certificate_lit% "b 0 a" []

/-- error: invalid certificate literal: expected a decimal index -/
#guard_msgs in
#check certificate_lit% "r x" []

/-- error: invalid certificate literal: forced value must be 0 or 1 -/
#guard_msgs in
#check certificate_lit% "f 0 2 1 a" []

/-- error: invalid certificate literal: helper index out of range -/
#guard_msgs in
#check certificate_lit% "h 0" []

/-- error: invalid certificate literal: trailing input -/
#guard_msgs in
#check certificate_lit% "a a" []

-- Closed lookup trees return defaults and distinguish the two sides of a pivot.
example : LookupTree.get (17 : ℕ) .empty 99 = 17 := by decide +kernel
example : LookupTree.get (0 : ℕ) (.branch 4 (.leaf 11) (.leaf 22)) 3 = 11 := by decide +kernel
example : LookupTree.get (0 : ℕ) (.branch 4 (.leaf 11) (.leaf 22)) 4 = 22 := by decide +kernel

-- Byte counting respects empty, partial, complete, and multi-byte widths.
example : Cube.fastFreeCount 0 ⟨1, 1⟩ = 1 := by decide +kernel
example : Cube.fastFreeCount 7 ⟨1, 64⟩ = 32 := by decide +kernel
example : Cube.fastFreeCount 8 ⟨1, 64⟩ = 64 := by decide +kernel
example : Cube.fastFreeCount 8 ⟨255, 0⟩ = 1 := by decide +kernel
example : Cube.fastFreeCount 9 ⟨255, 0⟩ = 2 := by decide +kernel
example : Cube.fastFreeCount 35 ⟨17179869184, 1⟩ = 8589934592 := by decide +kernel

-- Requirements outside the bounded variable set do not change the free count.
example : Cube.fastFreeCount 7 ⟨128, 256⟩ = 128 := by decide +kernel
example : Cube.fastFreeCount 35 ⟨34359738368, 0⟩ = 34359738368 := by decide +kernel

private def equalityProblem : Problem :=
  ⟨2, 1, fun _ => ⟨[1], [2]⟩, 0, fun _ i => i⟩

private def equalityCertificate : Certificate :=
  .branch 0 (.force 1 false 0 (.simplify 0 .accept))
    (.force 1 true 0 (.simplify 0 .accept))

-- Equality of two Boolean variables has the two models 00 and 11.
example : equalityProblem.check equalityCertificate = some 2 := by decide +kernel

example : ((Finset.range 4).filter fun mask => equalityProblem.valid mask = true).card = 2 := by
  apply equalityProblem.check_sound (certificate := equalityCertificate)
  · simp [Problem.PermutationsBounded, equalityProblem]
  · decide +kernel

private def swapProblem : Problem :=
  ⟨2, 0, fun _ => ⟨[], []⟩, 1, fun _ i => 1 - i⟩

private def swapCertificate : Certificate :=
  .branch 1 (.branch 0 (.simplify 0 .accept) (.simplify 0 .accept))
    (.force 0 true 0 (.simplify 0 .accept))

-- Canonicality under swapping two bits retains 00, 01, and 11.
example : swapProblem.check swapCertificate = some 3 := by decide +kernel

-- Invalid acceptance, witnesses, assignments, and retired constraints are rejected.
example : equalityProblem.check .accept = none := by decide +kernel
example : equalityProblem.check (.simplify 0 .accept) = none := by decide +kernel
example : equalityProblem.check (.reject 0) = none := by decide +kernel
example : equalityProblem.check
    (.force 0 true 0 (.force 1 true 0 (.simplify 0 .accept))) = none := by decide +kernel
example : equalityProblem.check (.reject 1) = none := by decide +kernel
example : equalityProblem.check (.simplify 1 .accept) = none := by decide +kernel
example : equalityProblem.check (.branch 2 .accept .accept) = none := by decide +kernel
example : (Problem.mk 2 0 (fun _ => ⟨[], []⟩) 0 (fun _ i => i)).check
    (.branch 0 (.branch 0 .accept .accept) .accept) = none := by
  decide +kernel
example : Counting.check (ActiveSearch.rules 2 equalityProblem.constraints)
    ⟨⟨1, 1⟩, 0⟩ .accept = none := by decide +kernel

private def equalityLowCount : equalityProblem.CertifiedCount :=
  equalityProblem.certify
    (by simp [Problem.PermutationsBounded, equalityProblem])
    (fun _ => none) ⟨⟨0, 1⟩, 1⟩ (.force 1 false 0 (.simplify 0 .accept)) 1 (by decide +kernel)

private def equalityReferences (index : ℕ) : Option equalityProblem.CertifiedCount :=
  if Nat.beq index 0 then some equalityLowCount else none

-- A reference checks its presence and every component of its state.
example : equalityProblem.checkChunk equalityReferences ⟨⟨0, 1⟩, 1⟩ (.reference 0) = some 1 := by
  decide +kernel
example : equalityProblem.checkChunk equalityReferences ⟨⟨0, 1⟩, 1⟩ (.reference 1) = none := by
  decide +kernel
example : equalityProblem.checkChunk equalityReferences ⟨⟨1, 1⟩, 1⟩ (.reference 0) = none := by
  decide +kernel
example : equalityProblem.checkChunk equalityReferences ⟨⟨0, 0⟩, 1⟩ (.reference 0) = none := by
  decide +kernel
example : equalityProblem.checkChunk equalityReferences ⟨⟨0, 1⟩, 0⟩ (.reference 0) = none := by
  decide +kernel

private def equalityReasons : ReasonTable where
  size := 4
  lookup
    | 0 => ⟨0, false, 1, 2⟩
    | 1 => ⟨0, false, 2, 1⟩
    | 2 => ⟨0, true, 0, 3⟩
    | 3 => ⟨0, true, 3, 0⟩
    | _ => ⟨99, true, 0, 0⟩

-- Block proofs compose without rechecking the whole table; the last block may be empty.
private theorem equalityReasons_valid : equalityReasons.Valid equalityProblem := by
  apply equalityReasons.valid_of_blocks equalityProblem 2 (by decide)
  intro block hb
  change block < 3 at hb
  have h : block = 0 ∨ block = 1 ∨ block = 2 := by omega
  rcases h with rfl | rfl | rfl <;> decide +kernel

example : equalityReasons.checkBlock equalityProblem 2 2 = true := by decide +kernel

private def equalityReasonCertificate : Certificate :=
  .branch 0 (.force 1 false 1 (.simplify 2 .accept))
    (.force 1 true 0 (.simplify 3 .accept))

private def equalityReasonCount : equalityProblem.CertifiedCount :=
  equalityProblem.certifyReasonChunk
    (by simp [Problem.PermutationsBounded, equalityProblem])
    equalityReasons equalityReasons_valid (fun _ => none)
    (ActiveSearch.initial equalityProblem.constraints) equalityReasonCertificate 2
    (by decide +kernel)

example : ActiveSearch.modelCount equalityProblem.variables equalityProblem.constraints
    (ActiveSearch.initial equalityProblem.constraints) = 2 :=
  equalityReasonCount.proof

-- Reason validation checks the constraint, polarity, and bounded requirement masks.
example : equalityProblem.reasonValid ⟨1, true, 0, 0⟩ = false := by decide +kernel
example : equalityProblem.reasonValid ⟨0, true, 1, 2⟩ = false := by decide +kernel
example : equalityProblem.reasonValid ⟨0, false, 3, 0⟩ = false := by decide +kernel
example : equalityProblem.reasonValid ⟨0, true, 4, 0⟩ = false := by decide +kernel
example : equalityProblem.reasonValid ⟨0, true, 0, 4⟩ = false := by decide +kernel
example : (ReasonTable.mk 1 fun _ => ⟨0, true, 1, 2⟩).checkBlock equalityProblem 2 0 = false := by
  decide +kernel

-- Every use checks the table bound, both requirement masks, the polarity, and active membership.
example : equalityProblem.checkReasonChunk (ReasonTable.mk 0 fun _ => ⟨0, false, 1, 2⟩)
    (fun _ => none) ⟨⟨1, 2⟩, 1⟩ (.reject 0) = none := by decide +kernel
example : equalityProblem.checkReasonChunk equalityReasons (fun _ => none)
    ⟨⟨0, 2⟩, 1⟩ (.reject 0) = none := by decide +kernel
example : equalityProblem.checkReasonChunk equalityReasons (fun _ => none)
    ⟨⟨1, 0⟩, 1⟩ (.reject 0) = none := by decide +kernel
example : equalityProblem.checkReasonChunk equalityReasons (fun _ => none)
    ⟨⟨0, 3⟩, 1⟩ (.reject 2) = none := by decide +kernel
example : equalityProblem.checkReasonChunk equalityReasons (fun _ => none)
    ⟨⟨1, 2⟩, 1⟩ (.simplify 0 .accept) = none := by decide +kernel
example : equalityProblem.checkReasonChunk equalityReasons (fun _ => none)
    ⟨⟨1, 2⟩, 0⟩ (.reject 0) = none := by decide +kernel
example : equalityProblem.checkReasonChunk equalityReasons (fun _ => none)
    ⟨⟨0, 3⟩, 1⟩ (.simplify 2 (.simplify 2 (.simplify 2 .accept))) = none := by decide +kernel

-- Cached permutation reasons use the same semantic validation as equation reasons.
example : swapProblem.reasonValid ⟨0, true, 1, 2⟩ = true := by decide +kernel
example : swapProblem.reasonValid ⟨0, false, 2, 1⟩ = true := by decide +kernel
example : swapProblem.reasonValid ⟨0, true, 2, 1⟩ = false := by decide +kernel

-- Counts proved by the original checker can also be referenced by the reason-based checker.
example : equalityProblem.checkReasonChunk equalityReasons equalityReferences
    (ActiveSearch.initial equalityProblem.constraints)
    (.branch 0 (.reference 0) (.force 1 true 0 (.simplify 3 .accept))) = some 2 := by
  decide +kernel

-- Numeric references contain no proofs; their validity is established independently below.
private def equalityDataReferences : ℕ → Option (CountData ActiveSearch.State)
  | 0 => some ⟨⟨⟨0, 1⟩, 1⟩, 1⟩
  | _ => none

example : equalityProblem.checkReasonDataChunk equalityReasons equalityDataReferences
    ⟨⟨0, 1⟩, 1⟩ (.reference 0) = some 1 := by decide +kernel
example : equalityProblem.checkReasonDataChunk equalityReasons equalityDataReferences
    ⟨⟨0, 0⟩, 1⟩ (.reference 0) = none := by decide +kernel
example : equalityProblem.checkReasonDataChunk equalityReasons equalityDataReferences
    ⟨⟨0, 1⟩, 1⟩ (.reference 1) = none := by decide +kernel

private def equalityDataCertificate : Certificate :=
  .branch 0 (.reference 0) (.force 1 true 0 (.simplify 3 .accept))

private theorem equalityData_checked : equalityProblem.checkReasonDataChunk equalityReasons
    equalityDataReferences (ActiveSearch.initial equalityProblem.constraints)
    equalityDataCertificate = some 2 := by decide +kernel

-- An earlier count theorem supplies the semantic obligation without entering the numeric check.
private theorem equalityDataReferences_valid :
    ReferencesValid (ActiveSearch.modelCount equalityProblem.variables equalityProblem.constraints)
      equalityDataReferences := by
  intro index data h
  cases index with
  | zero =>
    change some ⟨⟨⟨0, 1⟩, 1⟩, 1⟩ = some data at h
    cases h
    exact equalityLowCount.proof
  | succ index => simp [equalityDataReferences] at h

private def wideReferenceProblem : Problem :=
  ⟨35, 0, fun _ => ⟨[], []⟩, 0, fun _ i => i⟩

private def wideReferenceState : ActiveSearch.State := ⟨⟨0, 0⟩, 0⟩

private def wideReferenceData : CountData ActiveSearch.State :=
  ⟨wideReferenceState, 34359738368⟩

private def wideReferences : ℕ → Option (CountData ActiveSearch.State)
  | 0 => some wideReferenceData
  | _ => none

private theorem wideReference_count :
    ActiveSearch.modelCount wideReferenceProblem.variables wideReferenceProblem.constraints
      wideReferenceState = 34359738368 :=
  wideReferenceProblem.checkChunk_sound
    (by simp [Problem.PermutationsBounded, wideReferenceProblem])
    (fun _ => none) wideReferenceState .accept 34359738368 (by decide +kernel)

-- Reference transport must not unfold the finite-set count of 2^35 assignments.
example : ReferencesValid
    (ActiveSearch.modelCount wideReferenceProblem.variables wideReferenceProblem.constraints)
    wideReferences := by
  intro index data h
  unfold wideReferences at h
  split at h
  · exact CountData.count_eq_of_some_eq wideReferenceState 34359738368 wideReference_count h
  · exact False.elim (Option.some_ne_none data h.symm)

example : ActiveSearch.modelCount equalityProblem.variables equalityProblem.constraints
    (ActiveSearch.initial equalityProblem.constraints) = 2 :=
  equalityProblem.checkReasonDataChunk_sound
    (by simp [Problem.PermutationsBounded, equalityProblem]) equalityReasons equalityReasons_valid
    equalityDataReferences equalityDataReferences_valid
    (ActiveSearch.initial equalityProblem.constraints)
    equalityDataCertificate 2 equalityData_checked

-- Incorrect stored counts cannot satisfy the separate semantic reference obligation.
example : ¬ReferencesValid
    (ActiveSearch.modelCount equalityProblem.variables equalityProblem.constraints)
    (fun _ => some (⟨⟨⟨0, 1⟩, 1⟩, 99⟩ : CountData ActiveSearch.State)) := by
  intro h
  have hw := h 0 ⟨⟨⟨0, 1⟩, 1⟩, 99⟩ rfl
  change ActiveSearch.modelCount equalityProblem.variables equalityProblem.constraints
    ⟨⟨0, 1⟩, 1⟩ = 99 at hw
  have hc : ActiveSearch.modelCount equalityProblem.variables equalityProblem.constraints
      ⟨⟨0, 1⟩, 1⟩ = 1 := equalityLowCount.proof
  omega

private def bundleProblem : Problem :=
  ⟨2, 2, fun i => if i = 0 then ⟨[1], [2]⟩ else ⟨[], []⟩, 0, fun _ i => i⟩

private def bundleReasons : ReasonTable where
  size := 5
  lookup
    | 0 => ⟨0, false, 1, 2⟩
    | 1 => ⟨0, false, 2, 1⟩
    | 2 => ⟨0, true, 0, 3⟩
    | 3 => ⟨0, true, 3, 0⟩
    | _ => ⟨1, true, 0, 0⟩

private theorem bundleReasons_valid : bundleReasons.Valid bundleProblem := by
  apply bundleReasons.valid_of_blocks bundleProblem 5 (by decide)
  intro block hb
  change block < 2 at hb
  have h : block = 0 ∨ block = 1 := by omega
  rcases h with rfl | rfl <;> decide +kernel

private def equalityBundles : BundleTable where
  size := 2
  lookup
    | 0 => ⟨3, 0, 3⟩
    | _ => ⟨3, 3, 0⟩
  reasons
    | 0 => [2, 4]
    | _ => [3, 4]

-- Compact witnesses decode low fields first and ignore all input when the count is zero.
example : decodeBundleIndices 3 3 273 = [1, 2, 4] := by decide +kernel
example : decodeBundleIndices 3 0 273 = [] := by decide +kernel

private theorem equalityBundles_valid : equalityBundles.Valid bundleReasons := by
  apply equalityBundles.valid_of_blocks bundleReasons 2 (by decide)
  intro block hb
  change block < 2 at hb
  have h : block = 0 ∨ block = 1 := by omega
  rcases h with rfl | rfl <;> decide +kernel

private def bundleCertificate : Certificate :=
  .branch 0 (.force 1 false 1 (.simplify 0 .accept))
    (.force 1 true 0 (.simplify 1 .accept))

-- One bundle retires two different constraints; conflict witnesses still name individual reasons.
example : bundleProblem.checkBundleDataChunk bundleReasons equalityBundles (fun _ => none)
    (ActiveSearch.initial bundleProblem.constraints) bundleCertificate = some 2 := by decide +kernel

example : ActiveSearch.modelCount bundleProblem.variables bundleProblem.constraints
    (ActiveSearch.initial bundleProblem.constraints) = 2 := by
  apply bundleProblem.checkBundleDataChunk_sound
    (by simp [Problem.PermutationsBounded, bundleProblem]) bundleReasons bundleReasons_valid
    equalityBundles equalityBundles_valid (fun _ => none) (by intro _ _ h; cases h)
    (ActiveSearch.initial bundleProblem.constraints) bundleCertificate 2
  decide +kernel

-- Composition rejects negative and out-of-range reasons, even when the fallback reason is positive.
example : BundleData.compose bundleReasons [0] = none := by decide +kernel
example : BundleData.compose bundleReasons [5] = none := by decide +kernel
example : (BundleTable.mk 1 (fun _ => ⟨1, 1, 2⟩) (fun _ => [0])).checkEntry
    bundleReasons 0 = false := by decide +kernel
example : (BundleTable.mk 1 (fun _ => ⟨2, 0, 0⟩) (fun _ => [5])).checkEntry
    bundleReasons 0 = false := by decide +kernel

-- Validation detects unsupported constraints and weakened requirement masks.
example : (BundleTable.mk 1 (fun _ => ⟨7, 0, 3⟩) (fun _ => [2, 4])).checkEntry
    bundleReasons 0 = false := by decide +kernel
example : (BundleTable.mk 1 (fun _ => ⟨3, 1, 0⟩) (fun _ => [3, 4])).checkEntry
    bundleReasons 0 = false := by decide +kernel
example : (BundleTable.mk 1 (fun _ => ⟨3, 0, 1⟩) (fun _ => [2, 4])).checkEntry
    bundleReasons 0 = false := by decide +kernel

-- Runtime checks enforce bounds, both requirements, and membership of every retired constraint.
example : bundleProblem.checkBundleDataChunk bundleReasons
    (BundleTable.mk 0 (fun _ => ⟨3, 3, 0⟩) (fun _ => [3, 4])) (fun _ => none)
    ⟨⟨3, 0⟩, 3⟩ (.simplify 0 .accept) = none := by decide +kernel
example : bundleProblem.checkBundleDataChunk bundleReasons equalityBundles (fun _ => none)
    ⟨⟨1, 0⟩, 3⟩ (.simplify 1 .accept) = none := by decide +kernel
example : bundleProblem.checkBundleDataChunk bundleReasons equalityBundles (fun _ => none)
    ⟨⟨0, 1⟩, 3⟩ (.simplify 0 .accept) = none := by decide +kernel
example : bundleProblem.checkBundleDataChunk bundleReasons equalityBundles (fun _ => none)
    ⟨⟨3, 0⟩, 3⟩ (.simplify 1 (.simplify 1 (.simplify 1 .accept))) = none := by decide +kernel

end CslibTests.RelationAlgebraCounting
