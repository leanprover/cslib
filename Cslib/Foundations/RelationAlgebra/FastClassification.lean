/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.FastCycles
public import Cslib.Foundations.RelationAlgebra.FiniteClassification

/-!
# Numeric certificates for finite relation-algebra classifications

A bit mask chooses Peircean cycle orbits. Numeric associativity and relabelling checks then
certify the complete enumeration without repeatedly constructing finite sets of cycles.
-/

@[expose] public section

namespace Cslib.RelationAlgebra

open Code

variable {j k r : ℕ}

/-- Encode a finite vector of cycle choices as a natural-number bit mask. -/
def choiceMask (bits : Fin r → Bool) : ℕ :=
  bitsOf (fun i => if h : i < r then bits ⟨i, h⟩ else false) r

theorem choiceMask_lt (bits : Fin r → Bool) : choiceMask bits < 2 ^ r := bitsOf_lt _ _

@[simp]
theorem bitAt_choiceMask (bits : Fin r → Bool) (i : Fin r) :
    bitAt (choiceMask bits) i = bits i := by
  rw [choiceMask, bitAt_bitsOf i.isLt, dite_eq_left i.isLt]

/-- Assemble the numeric table from the chosen Peircean orbits and the identity cycles. -/
def cycleChoiceCode (reps : Fin r → Cycle j k) (mask : ℕ) : ℕ :=
  Nat.lor (identityCode j k) (orBelow (fun i =>
    if h : i < r then cond (bitAt mask i) (orbitCode (reps ⟨i, h⟩)) 0 else 0) r)

theorem encodesTable_cycleChoiceCode (reps : Fin r → Cycle j k) (mask : ℕ) :
    EncodesTable (selectedCycles reps (fun i => bitAt mask i)) (cycleChoiceCode reps mask) := by
  intro x y z
  have hor : bitAt (orBelow (fun i =>
      if h : i < r then cond (bitAt mask i) (orbitCode (reps ⟨i, h⟩)) 0 else 0) r)
      (index (atomCount j k) x.code y.code z.code) = true ↔
      ∃ i : Fin r, bitAt mask i = true ∧ (x, y, z) ∈ cycleOrbit (reps i) := by
    rw [bitAt_eq_testBit, testBit_orBelow]
    constructor
    · rintro ⟨i, hi, h⟩
      rw [dite_eq_left hi] at h
      cases hb : bitAt mask i
      · simp [hb] at h
      · refine ⟨⟨i, hi⟩, hb, ?_⟩
        simpa only [hb, Bool.cond_true, ← bitAt_eq_testBit, bitAt_orbitCode,
          decide_eq_true_iff] using h
    · rintro ⟨i, hi, h⟩
      refine ⟨i, i.isLt, ?_⟩
      rw [dite_eq_left i.isLt, hi, Bool.cond_true, ← bitAt_eq_testBit, bitAt_orbitCode]
      exact decide_eq_true h
  rw [Bool.eq_iff_iff, decide_eq_true_iff, cycleClosure_selectedCycles,
    cycleChoiceCode, bitAt_eq_testBit, Nat.lor_eq, Nat.testBit_or, Bool.or_eq_true,
    ← bitAt_eq_testBit, identityCode, bitAt_tripleCode, decide_eq_true_iff,
    ← bitAt_eq_testBit, hor]
  simp only [or_assoc]

namespace Code

/-- Compare every table bit with its image under a renaming of atom codes. -/
def relabelCheck (n source target : ℕ) (rename : ℕ → ℕ) : Bool :=
  allBelow (fun x => allBelow (fun y => allBelow (fun z =>
    Bool.beq (bitAt source (index n x y z))
      (bitAt target (index n (rename x) (rename y) (rename z)))) n) n) n

end Code

/-- A successful numeric relabelling check preserves the corresponding atom-cycle relation. -/
theorem cycleClosure_iff_of_relabelCheck {source target : Finset (Cycle j k)}
    {sourceCode targetCode : ℕ} (hs : EncodesTable source sourceCode)
    (ht : EncodesTable target targetCode) (f : Atom j k → Atom j k) (rename : ℕ → ℕ)
    (hf : ∀ x, (f x).code = rename x.code)
    (h : relabelCheck (atomCount j k) sourceCode targetCode rename = true) :
    ∀ x y z, cycleClosure source x y z ↔ cycleClosure target (f x) (f y) (f z) := by
  intro x y z
  have hc := allBelow_eq_true.mp h x.code x.code_lt
  have hc := allBelow_eq_true.mp hc y.code y.code_lt
  have hc := allBelow_eq_true.mp hc z.code z.code_lt
  change (bitAt sourceCode (index (atomCount j k) x.code y.code z.code) ==
    bitAt targetCode (index (atomCount j k) (rename x.code) (rename y.code)
      (rename z.code))) = true at hc
  rw [beq_iff_eq, ← hf x, ← hf y, ← hf z, hs, ht] at hc
  simpa only [decide_eq_true_eq] using (Bool.eq_iff_iff.mp hc)

/-- Numeric relabelling, with the elementary laws on atoms, gives an atom relabelling. -/
theorem atomRelabelling_of_relabelCheck {source target : Finset (Cycle j k)}
    {sourceCode targetCode : ℕ} (hs : EncodesTable source sourceCode)
    (ht : EncodesTable target targetCode) (f : Atom j k → Atom j k) (rename : ℕ → ℕ)
    (hf : ∀ x, (f x).code = rename x.code) (hinj : Function.Injective f)
    (hn : f none = none) (hc : ∀ x, f x.converse = (f x).converse)
    (h : relabelCheck (atomCount j k) sourceCode targetCode rename = true) :
    AtomRelabelling source target f :=
  ⟨hinj, hn, hc, cycleClosure_iff_of_relabelCheck hs ht f rename hf h⟩

namespace Code

/-- Check that each associative choice of cycle orbits has its specified relabelling. -/
def classificationCheck (n r : ℕ) (source target : ℕ → ℕ) (rename : ℕ → ℕ → ℕ) : Bool :=
  allBelow (fun mask => !assocCheck n (source mask) ||
    relabelCheck n (source mask) (target mask) (rename mask)) (2 ^ r)

end Code

/-- A numeric enumeration certificate proves exhaustiveness of the listed cycle tables. -/
theorem cycles_exhaustive_of_check {m p : ℕ} (reps : Fin r → Cycle j k)
    (models : Fin m → IntegralCycleTable j k) (modelCodes : Fin m → ℕ)
    (hmodels : ∀ i, EncodesTable (models i).cycles (modelCodes i))
    (renames : Fin p → Atom j k → Atom j k) (renameCodes : Fin p → ℕ → ℕ)
    (hcodes : ∀ i x, (renames i x).code = renameCodes i x.code)
    (hrenames : ∀ i, Function.Injective (renames i) ∧ renames i none = none ∧
      ∀ x, renames i x.converse = (renames i x).converse)
    (witness : ℕ → Fin m × Fin p)
    (h : classificationCheck (atomCount j k) r (cycleChoiceCode reps)
      (fun mask => modelCodes (witness mask).1)
      (fun mask => renameCodes (witness mask).2) = true) :
    ∀ bits : Fin r → Bool, AtomCompositionAssociative (selectedCycles reps bits) →
      ∃ i : Fin m, ∃ f, AtomRelabelling (selectedCycles reps bits) (models i).cycles f := by
  intro bits ha
  let mask := choiceMask bits
  have he : EncodesTable (selectedCycles reps bits) (cycleChoiceCode reps mask) := by
    simpa only [mask, bitAt_choiceMask] using encodesTable_cycleChoiceCode reps mask
  have hc := (assocCheck_iff he).mpr ha
  have hh := allBelow_eq_true.mp h mask (choiceMask_lt bits)
  have hr := not_or_eq_true.mp hh hc
  let w := witness mask
  exact ⟨w.1, renames w.2, atomRelabelling_of_relabelCheck he (hmodels w.1)
    (renames w.2) (renameCodes w.2) (hcodes w.2) (hrenames w.2).1
    (hrenames w.2).2.1 (hrenames w.2).2.2 hr⟩

namespace Code

/-- Check a predicate on `Fin n` using the primitive bounded loop. -/
def allFin {n : ℕ} (p : Fin n → Bool) : Bool :=
  allBelow (fun i => if h : i < n then p ⟨i, h⟩ else false) n

theorem allFin_eq_true {n : ℕ} {p : Fin n → Bool} : allFin p = true ↔ ∀ i, p i = true := by
  rw [allFin, allBelow_eq_true]
  constructor
  · intro h i
    simpa only [dite_eq_left i.isLt] using h i i.isLt
  · intro h i hi
    simpa only [dite_eq_left hi] using h ⟨i, hi⟩

/-- Check that the identity profiles of different models are not related by any renaming. -/
def profileDistinctCheck {m p : ℕ} (profiles : Fin m → Fin p → ℕ) (identity : Fin p) : Bool :=
  allFin fun i => allFin fun j => allFin fun q =>
    !Nat.beq (profiles i identity) (profiles j q) || Nat.beq i.val j.val

/-- Match a cycle profile first, checking associativity only for unmatched choices. -/
def profileClassificationCheck (n r : ℕ) (source profile : ℕ → ℕ) : Bool :=
  allBelow (fun mask => Nat.beq mask (profile mask) || !assocCheck n (source mask)) (2 ^ r)

end Code

/-- A numeric profile certificate proves that no two listed models are isomorphic. -/
theorem profileCode_injective_of_check {m p : ℕ} (profiles : Fin m → Fin p → ℕ)
    (identity : Fin p) (h : profileDistinctCheck profiles identity = true) :
    ∀ i j q, profiles i identity = profiles j q → i = j := by
  intro i j q he
  have h := allFin_eq_true.mp (allFin_eq_true.mp (allFin_eq_true.mp h i) j) q
  apply Fin.ext
  exact Nat.beq_eq.mp (not_or_eq_true.mp h (Nat.beq_eq.mpr he))

/-- Certified cycle profiles give an exhaustive classification without comparing full tables. -/
theorem cycles_exhaustive_of_profileCheck {m p : ℕ} (reps : Fin r → Cycle j k)
    (cover : ∀ c : Cycle j k, ∃ i, (some c.1, some c.2.1, some c.2.2) ∈ cycleOrbit (reps i))
    (distinct : ∀ i l, (some (reps i).1, some (reps i).2.1, some (reps i).2.2) ∈
      cycleOrbit (reps l) ↔ i = l)
    (models : Fin m → IntegralCycleTable j k) (renames : Fin p → Atom j k → Atom j k)
    (hrenames : ∀ i, Function.Injective (renames i) ∧ renames i none = none ∧
      ∀ x, renames i x.converse = (renames i x).converse)
    (profiles : Fin m → Fin p → ℕ)
    (hprofiles : ∀ i p, choiceMask (fun c => decide (cycleClosure (models i).cycles
      (renames p (some (reps c).1)) (renames p (some (reps c).2.1))
      (renames p (some (reps c).2.2)))) = profiles i p)
    (witness : ℕ → Fin m × Fin p)
    (h : profileClassificationCheck (atomCount j k) r (cycleChoiceCode reps)
      (fun mask => profiles (witness mask).1 (witness mask).2) = true) :
    ∀ bits : Fin r → Bool, AtomCompositionAssociative (selectedCycles reps bits) →
      ∃ i : Fin m, ∃ f, AtomRelabelling (selectedCycles reps bits) (models i).cycles f := by
  intro bits ha
  let mask := choiceMask bits
  have he : EncodesTable (selectedCycles reps bits) (cycleChoiceCode reps mask) := by
    simpa only [mask, bitAt_choiceMask] using encodesTable_cycleChoiceCode reps mask
  have hc := (assocCheck_iff he).mpr ha
  have hh := allBelow_eq_true.mp h mask (choiceMask_lt bits)
  rw [hc, Bool.not_true, Bool.or_false, Nat.beq_eq] at hh
  let w := witness mask
  refine ⟨w.1, renames w.2, atomRelabelling_of_cycle_basis reps cover
    (hrenames w.2).1 (hrenames w.2).2.1 (hrenames w.2).2.2 ?_⟩
  intro i
  rw [cycleClosure_selectedCycles_rep reps distinct]
  have hm : choiceMask bits = choiceMask (fun c => decide (cycleClosure (models w.1).cycles
      (renames w.2 (some (reps c).1)) (renames w.2 (some (reps c).2.1))
      (renames w.2 (some (reps c).2.2)))) := hh.trans (hprofiles w.1 w.2).symm
  have hb := congrArg (fun code => bitAt code i) hm
  simp only [bitAt_choiceMask] at hb
  rw [hb, decide_eq_true_iff]

end Cslib.RelationAlgebra
