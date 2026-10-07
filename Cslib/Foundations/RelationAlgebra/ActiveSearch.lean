/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.SearchCertificate
public import Cslib.Foundations.RelationAlgebra.FastClassification
public import Cslib.Foundations.RelationAlgebra.FastTruthTable

/-!
# Retiring settled constraints during certified search

Search states retain only the constraints still relevant to their cube. A simplification witness
retires one constraint after checking that every completion satisfies it. All descendants can then
skip that constraint, and an empty active mask certifies a whole cube at once.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Counting.ActiveSearch

/-- A finite indexed family of Boolean constraints with partial-assignment checks. -/
structure Constraints where
  /-- Number of constraints. -/
  size : ℕ
  /-- Evaluate one constraint on a complete assignment mask. -/
  eval : ℕ → ℕ → Bool
  /-- Check that a constraint fails on every completion of a cube. -/
  conflict : ℕ → Cube → Bool
  /-- Check that a constraint holds on every completion of a cube. -/
  settled : ℕ → Cube → Bool

/-- A cube together with the bit mask of constraints still needing attention. -/
structure State where
  /-- The partial assignment. -/
  cube : Cube
  /-- One bit for each constraint that has not yet been retired. -/
  active : ℕ

/-- Compare all three numeric masks without an opaque derived equality instance. -/
def State.beq (state other : State) : Bool :=
  Nat.beq state.cube.on other.cube.on && Nat.beq state.cube.off other.cube.off &&
    Nat.beq state.active other.active

/-- Successful mask comparison means exact equality of search states. -/
theorem State.beq_eq_true (state other : State) : state.beq other = true ↔ state = other := by
  rcases state with ⟨⟨on, off⟩, active⟩
  rcases other with ⟨⟨otherOn, otherOff⟩, otherActive⟩
  simp [State.beq, Nat.beq_eq]

/-- Every active constraint must hold. Inactive constraints impose no condition. -/
def valid (constraints : Constraints) (active mask : ℕ) : Bool :=
  Code.allBelow (fun i => !Code.bitAt active i || constraints.eval i mask) constraints.size

/-- The mathematical number of satisfying completions of a search state. -/
def modelCount (r : ℕ) (constraints : Constraints) (state : State) : ℕ :=
  state.cube.modelCount r (fun bits => valid constraints state.active (choiceMask bits))

/-- Soundness of the two partial-assignment checks. -/
structure Constraints.Sound (r : ℕ) (constraints : Constraints) : Prop where
  /-- A checked conflict falsifies the constraint throughout the cube. -/
  conflict : ∀ i < constraints.size, ∀ cube bits, constraints.conflict i cube = true →
    cube.Matches r bits → constraints.eval i (choiceMask bits) = false
  /-- A checked settled constraint holds throughout the cube. -/
  settled : ∀ i < constraints.size, ∀ cube bits, constraints.settled i cube = true →
    cube.Matches r bits → constraints.eval i (choiceMask bits) = true

/-- Remove an active constraint after its settled check succeeds. -/
def retire (state : State) (witness : ℕ) : State :=
  ⟨state.cube, state.active ^^^ (1 <<< witness)⟩

/-- Counting rules that use explicit conflict and constraint-retirement witnesses. -/
def rules (r : ℕ) (constraints : Constraints) : Rules State where
  rejectCheck state witness := Nat.blt witness constraints.size &&
    Code.bitAt state.active witness && constraints.conflict witness state.cube
  acceptCheck state := Nat.beq state.active 0 && state.cube.disjointCheck
  splitCheck state index := state.cube.splitCheck r index
  assign state index value := ⟨state.cube.assign index value, state.active⟩
  freeCount state := state.cube.freeCount r
  simplifyCheck state witness := Nat.blt witness constraints.size &&
    Code.bitAt state.active witness && constraints.settled witness state.cube
  simplify := retire

/-- Boolean checking of the active family has the expected pointwise interpretation. -/
theorem valid_iff (constraints : Constraints) (active mask : ℕ) :
    valid constraints active mask = true ↔
      ∀ i < constraints.size, Code.bitAt active i = true → constraints.eval i mask = true := by
  simp only [valid, Code.allBelow_eq_true, Code.not_or_eq_true]

/-- Toggling one bit leaves every other bit unchanged. -/
theorem bitAt_toggle (active index i : ℕ) :
    Code.bitAt (active ^^^ (1 <<< index)) i =
      if i = index then !Code.bitAt active i else Code.bitAt active i := by
  simp only [Code.bitAt_eq_testBit, Nat.testBit_xor, Nat.one_shiftLeft, Nat.testBit_two_pow]
  by_cases h : i = index
  · subst index
    cases active.testBit i <;> simp
  · simp [h, Ne.symm h]

/-- Retiring an active constraint that is true preserves validity of a complete assignment. -/
theorem valid_toggle_iff (constraints : Constraints) (active mask index : ℕ)
    (he : constraints.eval index mask = true) :
    valid constraints (active ^^^ (1 <<< index)) mask = true ↔
      valid constraints active mask = true := by
  rw [valid_iff, valid_iff]
  constructor <;> intro h i hi hb
  · by_cases heq : i = index
    · simpa only [heq] using he
    · exact h i hi (by simpa only [bitAt_toggle, ite_eq_right heq] using hb)
  · by_cases heq : i = index
    · simpa only [heq] using he
    · apply h i hi
      simpa only [bitAt_toggle, ite_eq_right heq] using hb

/-- A checked retired constraint can be omitted from the exact model count. -/
theorem modelCount_retire {r : ℕ} {constraints : Constraints}
    (sound : constraints.Sound r) (state : State) {witness : ℕ}
    (hi : witness < constraints.size) (hs : constraints.settled witness state.cube = true) :
    modelCount r constraints state = modelCount r constraints (retire state witness) := by
  unfold modelCount Cube.modelCount
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro bits hb
  have hm : state.cube.Matches r bits := (Finset.mem_filter.mp hb).2
  exact (valid_toggle_iff constraints state.active (choiceMask bits) witness
    (sound.settled witness hi state.cube bits hs hm)).symm

/-- The active-constraint counting rules satisfy all obligations of the generic checker. -/
theorem rules_sound {r : ℕ} {constraints : Constraints} (sound : constraints.Sound r) :
    Counting.Sound (rules r constraints) (modelCount r constraints) where
  reject state witness h := by
    change (Nat.blt witness constraints.size && Code.bitAt state.active witness &&
      constraints.conflict witness state.cube) = true at h
    simp only [Bool.and_eq_true, Nat.blt_eq] at h
    apply Cube.modelCount_eq_zero
    intro bits hm
    have hf := sound.conflict witness h.1.1 state.cube bits h.2 hm
    apply Bool.eq_false_iff.mpr
    intro hv
    have ht := (valid_iff constraints state.active (choiceMask bits)).mp hv
      witness h.1.1 h.1.2
    rw [hf] at ht
    contradiction
  accept state h := by
    change (Nat.beq state.active 0 && state.cube.disjointCheck) = true at h
    simp only [Bool.and_eq_true, Nat.beq_eq] at h
    apply Cube.modelCount_eq_freeCount _ _ (state.cube.consistentCheck_of_disjoint r h.2)
    intro bits _
    apply (valid_iff constraints state.active (choiceMask bits)).mpr
    intro i _ hb
    simp [h.1, Code.bitAt_eq_testBit] at hb
  split state index h := Cube.modelCount_split_of_check _ _ h
  simplify state witness h := by
    change (Nat.blt witness constraints.size && Code.bitAt state.active witness &&
      constraints.settled witness state.cube) = true at h
    simp only [Bool.and_eq_true, Nat.blt_eq] at h
    exact modelCount_retire sound state h.1.1 h.2
  lookup _ _ _ h := by cases h

/-- Initially all constraints are active and all variables are free. -/
def initial (constraints : Constraints) : State := ⟨⟨0, 0⟩, Code.truthOnes constraints.size⟩

/-- The initial active mask selects the entire constraint family. -/
theorem valid_initial (constraints : Constraints) (mask : ℕ) :
    valid constraints (initial constraints).active mask =
      Code.allBelow (fun i => constraints.eval i mask) constraints.size := by
  apply Bool.eq_iff_iff.mpr
  rw [valid_iff, Code.allBelow_eq_true]
  simp only [initial, Code.bitAt_truthOnes, decide_eq_true_eq]
  tauto

/-- The initial state's exact count is the number of assignments satisfying every constraint. -/
theorem modelCount_initial (r : ℕ) (constraints : Constraints) :
    modelCount r constraints (initial constraints) =
      (Finset.univ.filter fun bits : Fin r → Bool =>
        Code.allBelow (fun i => constraints.eval i (choiceMask bits))
          constraints.size = true).card := by
  unfold modelCount
  rw [show (initial constraints).cube = ⟨0, 0⟩ from rfl, Cube.modelCount_empty]
  simp only [valid_initial]

/-- Reading and repacking a bounded assignment mask leaves it unchanged. -/
theorem choiceMask_bits {r mask : ℕ} (hm : mask < 2 ^ r) :
    choiceMask (fun i : Fin r => Code.bitAt mask i) = mask := by
  apply Code.eq_of_testBit_eq_of_lt (choiceMask_lt _) hm
  intro i hi
  simpa only [Code.bitAt_eq_testBit] using
    bitAt_choiceMask (fun j : Fin r => Code.bitAt mask j) ⟨i, hi⟩

/-- Boolean assignments are in bijection with bounded natural-number masks. -/
def assignmentMaskEquiv (r : ℕ) : (Fin r → Bool) ≃ Fin (2 ^ r) where
  toFun bits := ⟨choiceMask bits, choiceMask_lt bits⟩
  invFun mask i := Code.bitAt mask i
  left_inv bits := by
    funext i
    exact bitAt_choiceMask bits i
  right_inv mask := Fin.ext (choiceMask_bits mask.isLt)

/-- Counting Boolean assignments agrees with counting their distinct bounded masks. -/
theorem card_assignments_eq_card_masks (r : ℕ) (predicate : ℕ → Bool) :
    (Finset.univ.filter fun bits : Fin r → Bool => predicate (choiceMask bits) = true).card =
      ((Finset.range (2 ^ r)).filter fun mask => predicate mask = true).card := by
  apply Finset.card_bij (fun bits _ => choiceMask bits)
  · intro bits hb
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (choiceMask_lt bits), (Finset.mem_filter.mp hb).2⟩
  · intro left _ right _ he
    apply (assignmentMaskEquiv r).injective
    exact Fin.ext he
  · intro mask hm
    obtain ⟨hm, hp⟩ := Finset.mem_filter.mp hm
    have hlt := Finset.mem_range.mp hm
    refine ⟨fun i : Fin r => Code.bitAt mask i, ?_, choiceMask_bits hlt⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, choiceMask_bits hlt, hp]

/-- The initial exact count can equivalently be stated over natural-number assignment masks. -/
theorem modelCount_initial_masks (r : ℕ) (constraints : Constraints) :
    modelCount r constraints (initial constraints) =
      ((Finset.range (2 ^ r)).filter fun mask =>
        Code.allBelow (fun i => constraints.eval i mask) constraints.size = true).card := by
  rw [modelCount_initial]
  exact card_assignments_eq_card_masks r
    (fun mask => Code.allBelow (fun i => constraints.eval i mask) constraints.size)

end Cslib.RelationAlgebra.Counting.ActiveSearch
