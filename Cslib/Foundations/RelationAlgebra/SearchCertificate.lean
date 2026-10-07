/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.FastCycles
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.BigOperators

/-!
# Certificates for finite model counts

A certificate partitions a search space, rejects inconsistent branches using explicit witnesses,
and counts a whole cube when every completion is a model. Forced assignments are justified by
rejecting the opposite branch. The search procedure need not be trusted: the checker and its
soundness theorem are independent of the procedure that constructs certificates.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Counting

/-- A finite search certificate. Each branch fixes one previously unassigned Boolean variable. -/
inductive Certificate where
  /-- A witness that the current cube contains no models. -/
  | reject (witness : ℕ)
  /-- Every completion of the current cube is a model. -/
  | accept
  /-- Partition the current cube by the value of a variable. -/
  | branch (index : ℕ) (low high : Certificate)
  /-- Reject the opposite value of a variable before continuing with its forced value. -/
  | force (index : ℕ) (value : Bool) (witness : ℕ) (next : Certificate)
  /-- Change the search representation after checking that the model count is preserved. -/
  | simplify (witness : ℕ) (next : Certificate)
  /-- Reuse a previously proved count for exactly the current state. -/
  | reference (index : ℕ)

/-- Executable operations used by the certificate checker. -/
structure Rules (State : Type*) where
  /-- Check an explicit rejection witness. -/
  rejectCheck : State → ℕ → Bool
  /-- Check that all completions are models. -/
  acceptCheck : State → Bool
  /-- Check that a variable may be used to partition the current state. -/
  splitCheck : State → ℕ → Bool
  /-- Restrict a state by one Boolean value. -/
  assign : State → ℕ → Bool → State
  /-- Number of completions when all completions are models. -/
  freeCount : State → ℕ
  /-- Check a simplification witness, for example retiring constraints already settled by a cube. -/
  simplifyCheck : State → ℕ → Bool
  /-- Apply a checked simplification to the search state. -/
  simplify : State → ℕ → State
  /-- Look up an independently certified count, if reference support is enabled. -/
  lookup : State → ℕ → Option ℕ := fun _ _ => none

/-- Check a certificate and return its exact count, failing on any invalid step. -/
def check (rules : Rules State) (state : State) : Certificate → Option ℕ
  | .reject witness => if rules.rejectCheck state witness then some 0 else none
  | .accept => if rules.acceptCheck state then some (rules.freeCount state) else none
  | .branch index low high =>
    if rules.splitCheck state index then do
      let lowCount ← check rules (rules.assign state index false) low
      let highCount ← check rules (rules.assign state index true) high
      return lowCount + highCount
    else none
  | .force index value witness next =>
    if rules.splitCheck state index &&
        rules.rejectCheck (rules.assign state index (!value)) witness then
      check rules (rules.assign state index value) next
    else none
  | .simplify witness next =>
    if rules.simplifyCheck state witness then check rules (rules.simplify state witness) next
    else none
  | .reference index => rules.lookup state index

/-- Mathematical obligations for the local operations of a counting checker. -/
structure Sound (rules : Rules State) (count : State → ℕ) : Prop where
  /-- A checked rejection witness excludes every model. -/
  reject : ∀ state witness, rules.rejectCheck state witness = true → count state = 0
  /-- A checked accepting leaf counts every completion. -/
  accept : ∀ state, rules.acceptCheck state = true → count state = rules.freeCount state
  /-- A checked split is a disjoint, exhaustive partition. -/
  split : ∀ state index, rules.splitCheck state index = true →
    count state = count (rules.assign state index false) +
      count (rules.assign state index true)
  /-- A checked simplification preserves the number of models. -/
  simplify : ∀ state witness, rules.simplifyCheck state witness = true →
    count state = count (rules.simplify state witness)
  /-- Every successful reference lookup supplies the specified count of its current state. -/
  lookup : ∀ state index result, rules.lookup state index = some result → count state = result

/-- Every successful certificate returns the mathematically specified count. -/
theorem check_sound {rules : Rules State} {count : State → ℕ} (sound : Sound rules count)
    (certificate : Certificate) (state : State) (result : ℕ)
    (h : check rules state certificate = some result) : count state = result := by
  induction certificate generalizing state result with
  | reject witness =>
    simp only [check] at h
    split at h
    · cases h
      exact sound.reject _ _ ‹_›
    · contradiction
  | accept =>
    simp only [check] at h
    split at h
    · cases h
      exact sound.accept _ ‹_›
    · contradiction
  | branch index low high ihLow ihHigh =>
    simp only [check] at h
    split at h
    · rename_i hs
      cases hl : check rules (rules.assign state index false) low with
      | none => simp [hl] at h
      | some lowCount =>
        cases hh : check rules (rules.assign state index true) high with
        | none => simp [hl, hh] at h
        | some highCount =>
          simp only [hl, hh] at h
          change some (lowCount + highCount) = some result at h
          injection h with h
          rw [sound.split state index hs, ihLow _ _ hl, ihHigh _ _ hh, h]
    · contradiction
  | force index value witness next ih =>
    simp only [check] at h
    split at h
    · rename_i hs
      simp only [Bool.and_eq_true] at hs
      obtain ⟨hs, hr⟩ := hs
      have hz := sound.reject _ _ hr
      have hc := ih _ _ h
      have hp := sound.split state index hs
      cases value <;> simp_all
    · contradiction
  | simplify witness next ih =>
    simp only [check] at h
    split at h
    · exact (sound.simplify _ _ ‹_›).trans (ih _ _ h)
    · contradiction
  | reference index => exact sound.lookup state index result h

/-- A Boolean cube stored as masks of indices required to be true and false. -/
structure Cube where
  /-- Variables required to be true. -/
  on : ℕ
  /-- Variables required to be false. -/
  off : ℕ

namespace Cube

/-- Whether a Boolean assignment satisfies the requirements of a cube. -/
def Matches (r : ℕ) (cube : Cube) (bits : Fin r → Bool) : Prop :=
  (∀ i : Fin r, Code.bitAt cube.on i = true → bits i = true) ∧
  (∀ i : Fin r, Code.bitAt cube.off i = true → bits i = false)

instance (r : ℕ) (cube : Cube) (bits : Fin r → Bool) : Decidable (cube.Matches r bits) := by
  unfold Matches
  infer_instance

/-- All assignments extending a cube. This is a specification, not a computation in the checker. -/
def assignments (r : ℕ) (cube : Cube) : Finset (Fin r → Bool) :=
  Finset.univ.filter (cube.Matches r)

/-- The exact number of models extending a cube. -/
def modelCount (r : ℕ) (valid : (Fin r → Bool) → Bool) (cube : Cube) : ℕ :=
  ((cube.assignments r).filter fun bits => valid bits = true).card

/-- Restrict a cube by one index. -/
def assign (cube : Cube) (index : ℕ) (value : Bool) : Cube :=
  if value then ⟨cube.on ||| (1 <<< index), cube.off⟩
  else ⟨cube.on, cube.off ||| (1 <<< index)⟩

/-- A legal split chooses an in-range index that has not yet been assigned. -/
def splitCheck (r : ℕ) (cube : Cube) (index : ℕ) : Bool :=
  Nat.blt index r && !(Code.bitAt cube.on index) && !(Code.bitAt cube.off index)

/-- Check that no in-range index is required to have both Boolean values. -/
def consistentCheck (r : ℕ) (cube : Cube) : Bool :=
  Code.allBelow (fun i => !(Code.bitAt cube.on i && Code.bitAt cube.off i)) r

/-- Check consistency of all assigned indices with one primitive mask intersection. -/
def disjointCheck (cube : Cube) : Bool := Nat.beq (Nat.land cube.on cube.off) 0

/-- Disjoint requirement masks are consistent on every bounded set of variables. -/
theorem consistentCheck_of_disjoint (cube : Cube) (r : ℕ) (h : cube.disjointCheck = true) :
    cube.consistentCheck r = true := by
  apply Code.allBelow_eq_true.mpr
  intro i _
  have he : cube.on &&& cube.off = 0 := Nat.beq_eq.mp h
  have hb := congrArg (fun mask => mask.testBit i) he
  simp only [Nat.testBit_and, Nat.zero_testBit] at hb
  simp only [Code.bitAt_eq_testBit, hb, Bool.not_false]

/-- Whether an index is still free. -/
def isFree (cube : Cube) (index : ℕ) : Bool :=
  !(Code.bitAt cube.on index) && !(Code.bitAt cube.off index)

/-- Count the free indices using a primitive recursion with no finite-set computation. -/
def freeVariables (cube : Cube) : ℕ → ℕ :=
  Nat.rec 0 (fun i count => if cube.isFree i then count + 1 else count)

/-- The number of completions of a consistent cube. -/
def freeCount (r : ℕ) (cube : Cube) : ℕ := 2 ^ cube.freeVariables r

/-- The possible values of a single index of a cube. -/
def values (cube : Cube) (index : ℕ) : Finset Bool :=
  Finset.univ.filter fun value =>
    (Code.bitAt cube.on index = true → value = true) ∧
      (Code.bitAt cube.off index = true → value = false)

/-- A cube is the Cartesian product of the choices at its indices. -/
theorem assignments_eq_pi (r : ℕ) (cube : Cube) :
    cube.assignments r = Fintype.piFinset (fun i : Fin r => cube.values i) := by
  ext bits
  simp only [assignments, values, Finset.mem_filter, Finset.mem_univ, true_and,
    Fintype.mem_piFinset, Matches, forall_and]

/-- A consistent index has two choices when free, and one choice otherwise. -/
theorem card_values {r : ℕ} (cube : Cube) (hc : cube.consistentCheck r = true)
    (i : Fin r) : (cube.values i).card = if cube.isFree i then 2 else 1 := by
  have h := Code.allBelow_eq_true.mp hc i i.isLt
  cases hon : Code.bitAt cube.on i <;> cases hoff : Code.bitAt cube.off i <;>
    simp [values, isFree, hon, hoff, Finset.filter_insert, Finset.filter_singleton] at h ⊢

/-- Products of the independent Boolean choices give the power of two used by the checker. -/
theorem prod_free_choices (cube : Cube) (r : ℕ) :
    (∏ i : Fin r, if cube.isFree i then 2 else 1) = 2 ^ cube.freeVariables r := by
  induction r with
  | zero => simp [freeVariables]
  | succ r ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih]
    by_cases hf : cube.isFree r = true <;> simp [freeVariables, hf, pow_succ]

/-- A consistent cube has exactly one completion for each assignment to its free indices. -/
theorem card_assignments {r : ℕ} (cube : Cube) (hc : cube.consistentCheck r = true) :
    (cube.assignments r).card = cube.freeCount r := by
  rw [assignments_eq_pi, Fintype.card_piFinset]
  simpa only [card_values cube hc, freeCount] using prod_free_choices cube r

/-- Rejecting every completion makes the exact model count zero. -/
theorem modelCount_eq_zero {r : ℕ} (valid : (Fin r → Bool) → Bool) (cube : Cube)
    (h : ∀ bits, cube.Matches r bits → valid bits = false) : cube.modelCount r valid = 0 := by
  unfold modelCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro bits hb hv
  have hm : cube.Matches r bits := (Finset.mem_filter.mp hb).2
  rw [h bits hm] at hv
  contradiction

/-- When every completion is accepted, a consistent cube contributes a power of two. -/
theorem modelCount_eq_freeCount {r : ℕ} (valid : (Fin r → Bool) → Bool) (cube : Cube)
    (hc : cube.consistentCheck r = true)
    (h : ∀ bits, cube.Matches r bits → valid bits = true) :
    cube.modelCount r valid = cube.freeCount r := by
  unfold modelCount
  have hf : (cube.assignments r).filter (fun bits => valid bits = true) = cube.assignments r := by
    apply Finset.filter_eq_self.mpr
    intro bits hb
    exact h bits (Finset.mem_filter.mp hb).2
  rw [hf, card_assignments cube hc]

/-- Assigning an in-range index adds exactly one condition on the Boolean assignment. -/
theorem matches_assign {r : ℕ} (cube : Cube) {index : ℕ} (hi : index < r)
    (value : Bool) (bits : Fin r → Bool) :
    (cube.assign index value).Matches r bits ↔
      cube.Matches r bits ∧ bits ⟨index, hi⟩ = value := by
  have hvalue (b : Bool) :
      (∀ i : Fin r, index = i.val → bits i = b) ↔ bits ⟨index, hi⟩ = b := by
    constructor
    · exact fun h => h ⟨index, hi⟩ rfl
    · intro h i he
      have : i = ⟨index, hi⟩ := Fin.ext he.symm
      simpa only [this] using h
  cases value <;>
    simp only [assign, Bool.false_eq_true, ↓reduceIte, Matches, Code.bitAt_eq_testBit,
      Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true,
      decide_eq_true_eq, or_imp, forall_and, hvalue] <;> tauto

/-- Partition a cube's model count by an in-range index. -/
theorem modelCount_split {r : ℕ} (valid : (Fin r → Bool) → Bool) (cube : Cube)
    {index : ℕ} (hi : index < r) :
    cube.modelCount r valid = (cube.assign index false).modelCount r valid +
      (cube.assign index true).modelCount r valid := by
  let models := (cube.assignments r).filter fun bits => valid bits = true
  have hfalse : ((cube.assign index false).assignments r).filter
      (fun bits => valid bits = true) = models.filter (fun bits => bits ⟨index, hi⟩ = false) := by
    ext bits
    simp only [models, assignments, Finset.mem_filter, Finset.mem_univ, true_and,
      matches_assign cube hi]
    tauto
  have htrue : ((cube.assign index true).assignments r).filter
      (fun bits => valid bits = true) = models.filter (fun bits => ¬bits ⟨index, hi⟩ = false) := by
    ext bits
    simp only [models, assignments, Finset.mem_filter, Finset.mem_univ, true_and,
      matches_assign cube hi, Bool.not_eq_false]
    tauto
  rw [modelCount, modelCount, modelCount, hfalse, htrue]
  exact (Finset.card_filter_add_card_filter_not (s := models)
    (fun bits : Fin r → Bool => bits ⟨index, hi⟩ = false)).symm

/-- A checked split supplies an exhaustive, disjoint partition of the models. -/
theorem modelCount_split_of_check {r : ℕ} (valid : (Fin r → Bool) → Bool) (cube : Cube)
    {index : ℕ} (h : cube.splitCheck r index = true) :
    cube.modelCount r valid = (cube.assign index false).modelCount r valid +
      (cube.assign index true).modelCount r valid := by
  simp only [splitCheck, Bool.and_eq_true, Nat.blt_eq] at h
  exact modelCount_split valid cube h.1.1

/-- Basic cube rules, with a consistency check at accepting leaves. -/
def rules (r : ℕ) (rejectCheck : Cube → ℕ → Bool) (acceptCheck : Cube → Bool) : Rules Cube where
  rejectCheck := rejectCheck
  acceptCheck cube := cube.consistentCheck r && acceptCheck cube
  splitCheck := Cube.splitCheck r
  assign := Cube.assign
  freeCount := Cube.freeCount r
  simplifyCheck _ _ := false
  simplify cube _ := cube

/-- Pointwise sound rejection and acceptance checks suffice to instantiate the count checker. -/
theorem rules_sound {r : ℕ} (valid : (Fin r → Bool) → Bool)
    (rejectCheck : Cube → ℕ → Bool) (acceptCheck : Cube → Bool)
    (rejectSound : ∀ cube witness bits, rejectCheck cube witness = true →
      cube.Matches r bits → valid bits = false)
    (acceptSound : ∀ cube bits, acceptCheck cube = true →
      cube.Matches r bits → valid bits = true) :
    Sound (rules r rejectCheck acceptCheck) (modelCount r valid) where
  reject cube witness h := modelCount_eq_zero valid cube fun bits hm =>
    rejectSound cube witness bits h hm
  accept cube h := by
    change (cube.consistentCheck r && acceptCheck cube) = true at h
    simp only [Bool.and_eq_true] at h
    exact modelCount_eq_freeCount valid cube h.1 fun bits hm => acceptSound cube bits h.2 hm
  split cube index h := modelCount_split_of_check valid cube h
  simplify _ _ h := by cases h
  lookup _ _ _ h := by cases h

/-- The empty cube places no restriction on an assignment. -/
@[simp]
theorem matches_empty (r : ℕ) (bits : Fin r → Bool) : (⟨0, 0⟩ : Cube).Matches r bits := by
  simp [Matches, Code.bitAt]

/-- The initial count is the number of all satisfying Boolean assignments. -/
theorem modelCount_empty (r : ℕ) (valid : (Fin r → Bool) → Bool) :
    modelCount r valid ⟨0, 0⟩ = (Finset.univ.filter fun bits => valid bits = true).card := by
  simp [modelCount, assignments]

end Cube

end Cslib.RelationAlgebra.Counting
