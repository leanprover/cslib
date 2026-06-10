/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.Decidability.AxiomMatcher
public import Cslib.Logics.Bimodal.Metalogic.Decidability.TraceCertificate

/-!
# Branch Closure Detection for Tableau Decision Procedure

This module implements closure detection for tableau branches. A branch is
closed if it contains a logical contradiction, which can arise from:

1. **Contradiction**: Both T(phi) and F(phi) for some formula phi
2. **Bot positive**: T(bot) is present (bottom asserted true)
3. **Axiom negation**: F(axiom instance) where the axiom is valid

## Main Definitions

- `ClosureReason`: Witness type explaining why a branch closed
  (defined in TraceCertificate.lean, re-exported here)
- `checkBotPos`: Check for T(bot)
- `checkContradiction`: Check for complementary pair T(phi), F(phi)
- `checkAxiomNeg`: Check for negated axiom instance F(axiom)
- `findClosure`: Combined closure detection
- `isClosed` / `isOpen`: Boolean checks
- `ClosedBranch` / `OpenBranch`: Witness-carrying types
- `BranchStatus`: Classification of branch as closed or open

## Monotonicity

Key structural property: closure is monotonic under branch extension.
If a branch is closed, adding more signed formulas keeps it closed.
This is proved as `closed_extend_closed`.

## Implementation Notes

The closure detection integrates with the `matchAxiom` function from
AxiomMatcher.lean to identify negated axiom instances. When F(phi) is
in the branch and phi matches an axiom pattern, the branch closes because
axioms are valid in all models.

Ported from BimodalLogic/Metalogic/Decidability/Closure.lean with
adaptations for universe-polymorphic `Formula Atom`.

## References

* Gore, R. (1999). Tableau Methods for Modal and Temporal Logics
-/

set_option linter.style.longLine false

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.Decidability

open Cslib.Logic.Bimodal

-- ClosureReason is defined in TraceCertificate.lean and imported transitively
-- through AxiomMatcher.lean -> Tableau.lean -> TraceCertificate.lean (circular would be bad)
-- Actually TraceCertificate imports Tableau, and AxiomMatcher imports Tableau.
-- ClosureReason is in TraceCertificate which is imported separately.
-- Let's verify the import chain: AxiomMatcher -> Tableau -> SignedFormula
-- TraceCertificate -> Tableau -> SignedFormula
-- We need to also import TraceCertificate for ClosureReason.

variable {Atom : Type u} [DecidableEq Atom] [Hashable Atom]

/-!
## BEq Lawfulness for SignedFormula

The `SignedFormula` type derives both `DecidableEq` and `BEq`. We need
`LawfulBEq` for monotonicity proofs (to convert between `==` and `=`).

Since `BEq` is derived from `DecidableEq` for these types, `a == b` is
definitionally `decide (a = b)`, so `LawfulBEq` follows directly.
-/

-- Note: SignedFormula derives `DecidableEq` (but not `BEq` separately), so
-- its BEq instance comes from `DecidableEq` and is definitionally `decide (a = b)`.
-- This makes it `LawfulBEq` by construction.

/-- BEq reflexivity for `SignedFormula Atom`. -/
theorem SignedFormula.beq_self (sf : SignedFormula Atom) : (sf == sf) = true :=
  decide_eq_true rfl

/-- If `sf1 == sf2 = true` then `sf1 = sf2`. -/
theorem SignedFormula.eq_of_beq_eq_true {sf1 sf2 : SignedFormula Atom}
    (h : (sf1 == sf2) = true) : sf1 = sf2 :=
  of_decide_eq_true h

/-!
## Closure Detection Functions
-/

/--
Check if a branch contains T(bot) at any label.
Records the label at which T(bot) was found.
-/
def checkBotPos (b : Branch Atom) : Option (ClosureReason Atom) :=
  b.findSome? fun sf =>
    if sf.sign == .pos && sf.formula == .bot then some (.botPos sf.label) else none

/--
Check if a branch contains a direct contradiction (both T(phi) and F(phi)
at the same label). Returns the formula and label that cause the
contradiction if found.
-/
def checkContradiction (b : Branch Atom) : Option (ClosureReason Atom) :=
  b.findSome? fun sf =>
    if sf.isPos ∧ b.hasNegAt sf.formula sf.label then
      some (.contradiction sf.formula sf.label)
    else
      none

/--
Check if a branch contains F(axiom) for some axiom instance.
Uses `matchAxiom` from AxiomMatcher to identify axiom patterns.
-/
def checkAxiomNeg (b : Branch Atom) (fc : FrameClass := .Base) :
    Option (ClosureReason Atom) :=
  b.findSome? fun sf =>
    if sf.isNeg then
      match matchAxiom sf.formula with
      | some ⟨φ, witness⟩ =>
          if sf.formula = φ then
            if witness.minFrameClass ≤ fc then
              some (.axiomNeg φ witness sf.label)
            else
              none
          else
            none
      | none => none
    else
      none

/--
Find a closure reason for a branch if one exists.
Checks in order: T(bot), contradiction, negated axiom.
-/
def findClosure (b : Branch Atom) (fc : FrameClass := .Base) :
    Option (ClosureReason Atom) :=
  checkBotPos b <|> checkContradiction b <|> checkAxiomNeg b fc

/--
Check if a branch is closed (has any closure reason).
-/
def isClosed (b : Branch Atom) (fc : FrameClass := .Base) : Bool :=
  (findClosure b fc).isSome

/--
Check if a branch is open (not closed).
-/
def isOpen (b : Branch Atom) (fc : FrameClass := .Base) : Bool :=
  ¬isClosed b fc

/-!
## Closure Witness Types
-/

/--
A closed branch is a branch together with a witness for its closure.
-/
structure ClosedBranch (Atom : Type u) [DecidableEq Atom] [Hashable Atom] where
  /-- The branch contents. -/
  branch : Branch Atom
  /-- Evidence for why the branch is closed. -/
  reason : ClosureReason Atom

/--
An open branch is a branch that has no closure reason.
-/
structure OpenBranch (Atom : Type u) [DecidableEq Atom] [Hashable Atom]
    (fc : FrameClass := .Base) where
  /-- The branch contents. -/
  branch : Branch Atom
  /-- Evidence that the branch is open (no closure reason found). -/
  notClosed : findClosure branch fc = none

/--
Classification of a branch as either closed or open.
-/
inductive BranchStatus (Atom : Type u) [DecidableEq Atom] where
  /-- Branch is closed with a reason. -/
  | closed (reason : ClosureReason Atom)
  /-- Branch is open (not closed). -/
  | open

/--
Classify a branch as closed or open.
-/
def classifyBranch (b : Branch Atom) (fc : FrameClass := .Base) :
    BranchStatus Atom :=
  match findClosure b fc with
  | some reason => .closed reason
  | none => .open

/-!
## Monotonicity Lemmas

These lemmas establish that closure checks are monotonic: if a branch is
closed, extending it with more formulas keeps it closed.
-/

/--
hasNeg is monotonic: if `b` contains F(phi), then `x :: b` also contains F(phi).
-/
theorem hasNeg_mono (b : Branch Atom) (x : SignedFormula Atom)
    (φ : Formula Atom) :
    Branch.hasNeg b φ → Branch.hasNeg (x :: b) φ := by
  intro h
  simp only [Branch.hasNeg, Branch.contains, List.any_cons] at h ⊢
  simp only [Bool.or_eq_true]
  right
  exact h

/--
hasPos is monotonic: if `b` contains T(phi), then `x :: b` also contains T(phi).
-/
theorem hasPos_mono (b : Branch Atom) (x : SignedFormula Atom)
    (φ : Formula Atom) :
    Branch.hasPos b φ → Branch.hasPos (x :: b) φ := by
  intro h
  simp only [Branch.hasPos, Branch.contains, List.any_cons] at h ⊢
  simp only [Bool.or_eq_true]
  right
  exact h

/--
hasNegAt is monotonic: if `b` contains F(phi) at label `l`, then `x :: b` also does.
-/
theorem hasNegAt_mono (b : Branch Atom) (x : SignedFormula Atom)
    (φ : Formula Atom) (l : Label) :
    Branch.hasNegAt b φ l → Branch.hasNegAt (x :: b) φ l := by
  intro h
  simp only [Branch.hasNegAt, Branch.contains, List.any_cons] at h ⊢
  simp only [Bool.or_eq_true]
  right
  exact h

/--
hasPosAt is monotonic: if `b` contains T(phi) at label `l`, then `x :: b` also does.
-/
theorem hasPosAt_mono (b : Branch Atom) (x : SignedFormula Atom)
    (φ : Formula Atom) (l : Label) :
    Branch.hasPosAt b φ l → Branch.hasPosAt (x :: b) φ l := by
  intro h
  simp only [Branch.hasPosAt, Branch.contains, List.any_cons] at h ⊢
  simp only [Bool.or_eq_true]
  right
  exact h

/--
hasBotPos is monotonic: if `b` contains T(bot), then `x :: b` also contains T(bot).
-/
theorem hasBotPos_mono (b : Branch Atom) (x : SignedFormula Atom) :
    Branch.hasBotPos b → Branch.hasBotPos (x :: b) := by
  intro h
  simp only [Branch.hasBotPos, List.any_cons] at h ⊢
  simp only [Bool.or_eq_true]
  right
  exact h

/--
checkBotPos is monotonic: if it succeeds on `b`, it succeeds on `x :: b`.
-/
theorem checkBotPos_mono (b : Branch Atom) (x : SignedFormula Atom) :
    (checkBotPos b).isSome → (checkBotPos (x :: b)).isSome := by
  intro h
  rw [checkBotPos, List.findSome?_isSome_iff] at h
  obtain ⟨sf, hsf_mem, hsf_cond⟩ := h
  rw [checkBotPos, List.findSome?_isSome_iff]
  exact ⟨sf, List.mem_cons_of_mem x hsf_mem, hsf_cond⟩

/--
checkContradiction is monotonic: if it succeeds on `b`, it succeeds on `x :: b`.
-/
theorem checkContradiction_mono (b : Branch Atom) (x : SignedFormula Atom) :
    (checkContradiction b).isSome → (checkContradiction (x :: b)).isSome := by
  intro h
  rw [checkContradiction, List.findSome?_isSome_iff] at h
  obtain ⟨sf, hsf_mem, hsf_cond⟩ := h
  rw [checkContradiction, List.findSome?_isSome_iff]
  refine ⟨sf, List.mem_cons_of_mem x hsf_mem, ?_⟩
  simp only [Option.isSome_iff_exists] at hsf_cond ⊢
  obtain ⟨reason, hreason⟩ := hsf_cond
  split_ifs at hreason with hcond
  -- The condition was true for b; show it's still true for x :: b
  · obtain ⟨hpos, hneg⟩ := hcond
    have hneg' : Branch.hasNegAt (x :: b) sf.formula sf.label :=
      hasNegAt_mono b x sf.formula sf.label hneg
    use ClosureReason.contradiction sf.formula sf.label
    split_ifs with hcond'
    · rfl
    · push Not at hcond'
      exact absurd hneg' (hcond' hpos)

/--
checkAxiomNeg is monotonic: if it succeeds on `b`, it succeeds on `x :: b`.
The axiom check is branch-independent (only depends on the formula pattern).
-/
theorem checkAxiomNeg_mono (b : Branch Atom) (x : SignedFormula Atom)
    (fc : FrameClass := .Base) :
    (checkAxiomNeg b fc).isSome → (checkAxiomNeg (x :: b) fc).isSome := by
  intro h
  rw [checkAxiomNeg, List.findSome?_isSome_iff] at h
  obtain ⟨sf, hsf_mem, hsf_cond⟩ := h
  rw [checkAxiomNeg, List.findSome?_isSome_iff]
  exact ⟨sf, List.mem_cons_of_mem x hsf_mem, hsf_cond⟩

/-!
## Closure Properties

These theorems require careful reasoning about how `findSome?` interacts
with branch extension. The proofs are non-trivial because `checkContradiction`
captures the branch in its lambda, creating a dependency between the branch
being searched and the condition being checked.
-/

/--
A closed branch remains closed when extended.
Adding more formulas cannot "undo" a contradiction.
-/
theorem closed_extend_closed (b : Branch Atom) (sf : SignedFormula Atom)
    (fc : FrameClass := .Base) :
    isClosed b fc → isClosed (sf :: b) fc := by
  intro h
  simp only [isClosed, findClosure] at h ⊢
  rw [Option.isSome_iff_exists] at h
  obtain ⟨r, hr⟩ := h
  rw [Option.orElse_eq_some] at hr
  rcases hr with hbot | ⟨_, hr'⟩
  · -- checkBotPos b = some r
    have hsome : (checkBotPos (sf :: b)).isSome := checkBotPos_mono b sf (by simp [hbot])
    simp only [Option.isSome_iff_exists] at hsome
    obtain ⟨r', hr'⟩ := hsome
    rw [Option.isSome_iff_exists]
    exact ⟨r', by simp [hr']⟩
  · -- checkBotPos b = none, and (checkContradiction b <|> checkAxiomNeg b fc) = some r
    rw [Option.orElse_eq_some] at hr'
    rcases hr' with hcontra | ⟨_, hax⟩
    · -- checkContradiction b = some r
      have hsome : (checkContradiction (sf :: b)).isSome :=
        checkContradiction_mono b sf (by simp [hcontra])
      cases hbot' : checkBotPos (sf :: b) with
      | some _ => rfl
      | none =>
        simp only [Option.isSome_iff_exists] at hsome
        obtain ⟨r', hr''⟩ := hsome
        rw [Option.isSome_iff_exists]
        exact ⟨r', by simp [hr'']⟩
    · -- checkAxiomNeg b fc = some r
      have hsome : (checkAxiomNeg (sf :: b) fc).isSome :=
        checkAxiomNeg_mono b sf fc (by simp [hax])
      cases hbot' : checkBotPos (sf :: b) with
      | some _ => rfl
      | none =>
        cases hcontra' : checkContradiction (sf :: b) with
        | some _ => rfl
        | none =>
          simp only [Option.isSome_iff_exists] at hsome
          obtain ⟨r', hr''⟩ := hsome
          rw [Option.isSome_iff_exists]
          exact ⟨r', by simp [hr'']⟩

/--
If a branch has T(phi) (at initial label) and we add F(phi) (at initial label),
it becomes closed.
-/
theorem add_neg_causes_closure (b : Branch Atom) (φ : Formula Atom)
    (fc : FrameClass := .Base) :
    Branch.hasPos b φ → isClosed (SignedFormula.neg φ :: b) fc := by
  intro hpos
  simp only [isClosed, findClosure]
  cases hbot : checkBotPos (SignedFormula.neg φ :: b) with
  | some _ => rfl
  | none =>
    -- The extended branch has F(phi) at the head (at initial label)
    have hasNegAtPhi :
        Branch.hasNegAt (SignedFormula.neg φ :: b) φ Label.initial = true := by
      simp only [Branch.hasNegAt, Branch.contains, SignedFormula.neg,
        List.any_cons, Bool.or_eq_true]
      left
      exact SignedFormula.beq_self _
    -- Show checkContradiction succeeds by finding the witness from hpos
    have hcontra :
        (checkContradiction (SignedFormula.neg φ :: b)).isSome := by
      rw [checkContradiction, List.findSome?_isSome_iff]
      simp only [Branch.hasPos, Branch.contains, List.any_eq_true] at hpos
      obtain ⟨witness, hwit_mem, hwit_eq⟩ := hpos
      have hwit_eq' : witness = SignedFormula.pos φ :=
        SignedFormula.eq_of_beq_eq_true hwit_eq
      refine ⟨witness, List.mem_cons_of_mem (SignedFormula.neg φ) hwit_mem, ?_⟩
      simp only [Option.isSome_iff_exists]
      use ClosureReason.contradiction witness.formula witness.label
      rw [hwit_eq']
      simp only [SignedFormula.pos, SignedFormula.isPos, hasNegAtPhi,
        decide_true, and_self, ↓reduceIte]
    simp only [Option.isSome_iff_exists] at hcontra ⊢
    obtain ⟨r, hr⟩ := hcontra
    exact ⟨r, by simp [hr]⟩

/-!
## Closure Detection Statistics
-/

/--
Count potential contradictions in a branch (for heuristic guidance).
Counts formulas that have their negation present.
-/
def countPotentialContradictions (b : Branch Atom) : Nat :=
  b.filter (fun sf => sf.isPos ∧ b.hasNegAt sf.formula sf.label)
    |>.length

/--
Count negated axiom instances in a branch.
-/
def countNegatedAxioms (b : Branch Atom) : Nat :=
  b.filter (fun sf => sf.isNeg ∧ (matchAxiom sf.formula).isSome)
    |>.length

end Cslib.Logic.Bimodal.Metalogic.Decidability
