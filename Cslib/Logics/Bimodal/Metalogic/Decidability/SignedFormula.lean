/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import Cslib.Logics.Bimodal.Syntax.Formula
import Cslib.Logics.Bimodal.Syntax.Subformulas

/-!
# Signed Formula and Branch Types for Tableau Decidability

This module defines the core types for tableau-based decision procedures:
- `Sign`: Positive (asserted true) or negative (asserted false)
- `SignedFormula`: A formula with a sign
- `Branch`: A list of signed formulas representing a tableau branch

## Main Definitions

- `Sign`: Inductive type with `pos` and `neg` constructors
- `SignedFormula`: Structure combining sign and formula
- `Branch`: Type alias for `List SignedFormula`
- `Formula.subformulas`: Collect all subformulas of a formula
- `subformulaClosure`: Compute the subformula closure

## Implementation Notes

The tableau method works by maintaining branches of signed formulas.
A positive sign means the formula is asserted true, negative means false.
The tableau systematically expands formulas until branches close (contradiction)
or saturate (open branch = countermodel).

Ported from BimodalLogic with universe-polymorphic `Formula Atom` replacing
monomorphic `Formula`.

## References

* Gore, R. (1999). Tableau Methods for Modal and Temporal Logics
* Wu, M. Verified Decision Procedures for Modal Logics (Lean formalization)
-/

/-!
## Hashable and Complexity for Formula

These definitions extend `Cslib.Logic.Bimodal.Formula` with `Hashable`,
`complexity`, and `subformulas` needed by the decidability module.
They must be in the `Cslib.Logic.Bimodal` namespace so that dot notation
on `Formula Atom` resolves correctly.
-/

namespace Cslib.Logic.Bimodal

variable {Atom : Type*} [DecidableEq Atom]

/-- Hash function for `Formula Atom`. Defined as a standalone recursive function
to avoid instance resolution issues in the `Hashable` instance definition. -/
def Formula.hashFormula [Hashable Atom] : Formula Atom → UInt64
  | .atom a => mixHash 0 (hash a)
  | .bot => 1
  | .imp φ₁ φ₂ => mixHash 2 (mixHash φ₁.hashFormula φ₂.hashFormula)
  | .box φ => mixHash 3 φ.hashFormula
  | .untl φ₁ φ₂ => mixHash 4 (mixHash φ₁.hashFormula φ₂.hashFormula)
  | .snce φ₁ φ₂ => mixHash 5 (mixHash φ₁.hashFormula φ₂.hashFormula)

instance [Hashable Atom] : Hashable (Formula Atom) where
  hash := Formula.hashFormula

/--
Structural complexity of a formula (number of connectives + 1).

This is a simple recursive measure that treats all connectives uniformly.
Used for fuel computation in tableau expansion.
-/
def Formula.complexity : Formula Atom → Nat
  | .atom _ => 1
  | .bot => 1
  | .imp φ ψ => 1 + φ.complexity + ψ.complexity
  | .box φ => 1 + φ.complexity
  | .untl φ ψ => 1 + φ.complexity + ψ.complexity
  | .snce φ ψ => 1 + φ.complexity + ψ.complexity

-- Subformulas, subformulaCount, and associated theorems are now defined in
-- Cslib.Logics.Bimodal.Syntax.Subformulas (imported above)

end Cslib.Logic.Bimodal

/-!
## Decidability Module Types
-/

namespace Cslib.Logic.Bimodal.Metalogic.Decidability

open Cslib.Logic.Bimodal

/-!
## World and Time Index Types
-/

/-- World index for multi-world modal reasoning in labeled tableaux. -/
abbrev WorldIndex := Nat

/-- Time index for temporal reasoning in labeled tableaux. -/
abbrev TimeIndex := Nat

/--
A label combining world and time indices for tableau signed formulas.
Each signed formula carries a label indicating the world and time at which
it is asserted.
-/
structure Label : Type where
  /-- The world at which the formula is evaluated. -/
  world : WorldIndex
  /-- The time at which the formula is evaluated. -/
  time : TimeIndex
  deriving Repr, DecidableEq, BEq, Hashable

namespace Label

/-- The initial label at world 0, time 0. -/
def initial : Label := { world := 0, time := 0 }

/-- BEq on Label decomposes to component BEq. -/
theorem beq_eq (l1 l2 : Label) :
    (l1 == l2) = (l1.world == l2.world && l1.time == l2.time) := by
  cases l1; cases l2; rfl

/-- BEq on Label is reflexive. -/
theorem beq_refl (l : Label) : (l == l) = true := by
  rw [beq_eq]
  simp only [beq_self_eq_true, Bool.and_self]

instance : ReflBEq Label where
  rfl := beq_refl _

/-- BEq on Label is injective. -/
theorem eq_of_beq {l1 l2 : Label} (h : (l1 == l2) = true) : l1 = l2 := by
  rw [beq_eq] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  cases l1; cases l2
  simp only [mk.injEq]
  exact h

instance : LawfulBEq Label where
  eq_of_beq := eq_of_beq
  rfl := beq_refl _

end Label

/-!
## Sign Type
-/

/--
Sign for signed formulas in tableau calculus.

- `pos`: Formula is asserted to be true
- `neg`: Formula is asserted to be false
-/
inductive Sign : Type where
  | pos : Sign
  | neg : Sign
  deriving Repr, DecidableEq, BEq, Hashable, Inhabited

namespace Sign

/-- Flip the sign. -/
def flip : Sign → Sign
  | pos => neg
  | neg => pos

@[simp]
theorem flip_flip (s : Sign) : s.flip.flip = s := by
  cases s <;> rfl

@[simp]
theorem flip_pos : Sign.pos.flip = Sign.neg := rfl

@[simp]
theorem flip_neg : Sign.neg.flip = Sign.pos := rfl

/-- BEq on Sign is reflexive. -/
instance : ReflBEq Sign where
  rfl := fun {s} => by cases s <;> decide

/-- BEq on Sign is injective: if `s1 == s2 = true` then `s1 = s2`. -/
theorem eq_of_beq {s1 s2 : Sign} (h : (s1 == s2) = true) : s1 = s2 := by
  cases s1 <;> cases s2
  · rfl
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · rfl

instance : LawfulBEq Sign where
  eq_of_beq := eq_of_beq
  rfl := by intro s; cases s <;> decide

end Sign

/-!
## Signed Formula Type
-/

variable (Atom : Type*) [DecidableEq Atom] [Hashable Atom]

/--
A signed formula is a formula with a sign indicating truth assertion.

- `sign = pos`: The formula is asserted to be true
- `sign = neg`: The formula is asserted to be false

In tableau calculus, we start with the negation of the goal (sign = neg)
and expand until all branches close or we find an open saturated branch.
-/
structure SignedFormula : Type _ where
  /-- The sign indicating truth or falsity assertion. -/
  sign : Sign
  /-- The formula being signed. -/
  formula : Formula Atom
  /-- The world/time label for this assertion. -/
  label : Label
  deriving DecidableEq, Hashable

variable {Atom}

namespace SignedFormula

/-- Create a positive signed formula (asserted true). -/
def pos (φ : Formula Atom) (l : Label := Label.initial) :
    SignedFormula Atom := ⟨.pos, φ, l⟩

/-- Create a negative signed formula (asserted false). -/
def neg (φ : Formula Atom) (l : Label := Label.initial) :
    SignedFormula Atom := ⟨.neg, φ, l⟩

/-- Flip the sign of a signed formula, preserving the label. -/
def flip (sf : SignedFormula Atom) : SignedFormula Atom :=
  ⟨sf.sign.flip, sf.formula, sf.label⟩

omit [DecidableEq Atom] [Hashable Atom] in
@[simp]
theorem flip_flip (sf : SignedFormula Atom) : sf.flip.flip = sf := by
  simp [flip, Sign.flip_flip]

/-- Check if this is a positive signed formula. -/
def isPos (sf : SignedFormula Atom) : Bool := sf.sign = .pos

/-- Check if this is a negative signed formula. -/
def isNeg (sf : SignedFormula Atom) : Bool := sf.sign = .neg

/-- Get the complexity of the signed formula (same as formula complexity). -/
def complexity (sf : SignedFormula Atom) : Nat := sf.formula.complexity

end SignedFormula

/-!
## Branch Type
-/

/--
A branch is a list of signed formulas in a tableau.

Branches grow as tableau rules are applied. A branch is closed if it
contains a contradiction (both T(φ) and F(φ) for some formula φ, or T(⊥)).
A branch is open if it is saturated (all rules applied) and not closed.
-/
abbrev Branch (Atom : Type u) [DecidableEq Atom] [Hashable Atom] :=
  List (SignedFormula Atom)

namespace Branch

/-- Empty branch. -/
def empty : Branch Atom := []

/-- Check if branch contains a specific signed formula. -/
def contains (b : Branch Atom) (sf : SignedFormula Atom) : Bool :=
  b.any (· == sf)

/-- Check if branch contains a positive formula at the initial label. -/
def hasPos (b : Branch Atom) (φ : Formula Atom) : Bool :=
  b.contains (SignedFormula.pos φ)

/-- Check if branch contains a negative formula at the initial label. -/
def hasNeg (b : Branch Atom) (φ : Formula Atom) : Bool :=
  b.contains (SignedFormula.neg φ)

/-- Check if branch contains T(φ) at a specific label. -/
def hasPosAt (b : Branch Atom) (φ : Formula Atom) (l : Label) : Bool :=
  b.contains (SignedFormula.pos φ l)

/-- Check if branch contains F(φ) at a specific label. -/
def hasNegAt (b : Branch Atom) (φ : Formula Atom) (l : Label) : Bool :=
  b.contains (SignedFormula.neg φ l)

/-- Check if branch contains T(⊥) at any label. -/
def hasBotPos (b : Branch Atom) : Bool :=
  b.any fun sf => sf.sign == .pos && sf.formula == .bot

/--
Check if branch has a direct contradiction: both T(φ) and F(φ) at the
same label. Returns `some φ` if contradiction found, `none` otherwise.
-/
def findContradiction (b : Branch Atom) : Option (Formula Atom) :=
  b.findSome? fun sf =>
    if sf.isPos ∧ b.hasNegAt sf.formula sf.label then some sf.formula
    else none

/-- Check if branch has any contradiction (T(⊥) or complementary pair). -/
def hasContradiction (b : Branch Atom) : Bool :=
  b.hasBotPos || b.findContradiction.isSome

/-- Get all positive formulas in the branch. -/
def positives (b : Branch Atom) : List (Formula Atom) :=
  b.filterMap fun sf => if sf.isPos then some sf.formula else none

/-- Get all negative formulas in the branch. -/
def negatives (b : Branch Atom) : List (Formula Atom) :=
  b.filterMap fun sf => if sf.isNeg then some sf.formula else none

/-- Extend branch with a signed formula. -/
def extend (b : Branch Atom) (sf : SignedFormula Atom) : Branch Atom :=
  sf :: b

/-- Extend branch with multiple signed formulas. -/
def extendMany (b : Branch Atom) (sfs : List (SignedFormula Atom)) :
    Branch Atom := sfs ++ b

/-- Total complexity of all formulas in branch. -/
def totalComplexity (b : Branch Atom) : Nat :=
  b.foldl (fun acc sf => acc + sf.complexity) 0

/--
Collect all distinct world indices from signed formulas in the branch.
Used by S5 modal rules to know which worlds exist for universal
propagation.
-/
def knownWorlds (b : Branch Atom) : List WorldIndex :=
  (b.map (·.label.world)).eraseDups

/--
Maximum world index in the branch (0 if empty).
Used to compute the next fresh world index.
-/
def maxWorld (b : Branch Atom) : WorldIndex :=
  b.foldl (fun acc sf => max acc sf.label.world) 0

/--
Next fresh world index (one past the maximum).
Used by existential modal rules to introduce witness worlds.
-/
def nextWorld (b : Branch Atom) : WorldIndex :=
  b.maxWorld + 1

/--
Collect all T(□A) formulas in the branch (positive box formulas).
These are universal modal formulas that must be propagated to every
known world.
-/
def boxPosFormulas (b : Branch Atom) : List (SignedFormula Atom) :=
  b.filter fun sf =>
    match sf.sign, sf.formula with
    | .pos, .box _ => true
    | _, _ => false

/--
Collect all F(◇A) formulas in the branch (negative diamond formulas).
Diamond encoding: ◇A = ¬□¬A = (.imp (.box (.imp A .bot)) .bot)
-/
def diamondNegFormulas (b : Branch Atom) : List (SignedFormula Atom) :=
  b.filter fun sf =>
    match sf.sign, sf.formula with
    | .neg, .imp (.box (.imp _ .bot)) .bot => true
    | _, _ => false

/--
Collect all distinct time indices from signed formulas in the branch.
Used by temporal rules to know which times exist for universal
propagation.
-/
def knownTimes (b : Branch Atom) : List TimeIndex :=
  (b.map (·.label.time)).eraseDups

/--
Maximum time index in the branch (0 if empty).
Used to compute the next fresh time index.
-/
def maxTime (b : Branch Atom) : TimeIndex :=
  b.foldl (fun acc sf => max acc sf.label.time) 0

/--
Next fresh time index (one past the maximum).
Used by existential temporal rules to introduce witness times.
-/
def nextTime (b : Branch Atom) : TimeIndex :=
  b.maxTime + 1

/--
Collect all T(GA) formulas in the branch (positive all-future formulas).
G(A) = ¬F(¬A) = ¬(¬A U ⊤) = imp (untl (imp A bot) (imp bot bot)) bot
-/
def allFuturePosFormulas (b : Branch Atom) : List (SignedFormula Atom) :=
  b.filter fun sf =>
    match sf.sign, sf.formula with
    | .pos, .allFuture _ => true
    | _, _ => false

/--
Collect all F(FA) formulas in the branch (negative some-future formulas).
F(A) = A U ⊤ = untl A (imp bot bot)
-/
def someFutureNegFormulas (b : Branch Atom) : List (SignedFormula Atom) :=
  b.filter fun sf =>
    match sf.sign, sf.formula with
    | .neg, .someFuture _ => true
    | _, _ => false

/--
Collect all T(HA) formulas in the branch (positive all-past formulas).
H(A) = ¬P(¬A) = ¬(¬A S ⊤) = imp (snce (imp A bot) (imp bot bot)) bot
-/
def allPastPosFormulas (b : Branch Atom) : List (SignedFormula Atom) :=
  b.filter fun sf =>
    match sf.sign, sf.formula with
    | .pos, .allPast _ => true
    | _, _ => false

/--
Collect all F(PA) formulas in the branch (negative some-past formulas).
P(A) = A S ⊤ = snce A (imp bot bot)
-/
def somePastNegFormulas (b : Branch Atom) : List (SignedFormula Atom) :=
  b.filter fun sf =>
    match sf.sign, sf.formula with
    | .neg, .somePast _ => true
    | _, _ => false

/--
Collect all F(U(event, guard)) formulas in the branch (negative Until
formulas) where guard is NOT Formula.top (i.e., not someFuture).
-/
def untlNegFormulas (b : Branch Atom) : List (SignedFormula Atom) :=
  b.filter fun sf =>
    match sf.sign, sf.formula with
    | .neg, .untl _ guard => guard != Formula.top
    | _, _ => false

/--
Collect all F(S(event, guard)) formulas in the branch (negative Since
formulas) where guard is NOT Formula.top (i.e., not somePast).
-/
def snceNegFormulas (b : Branch Atom) : List (SignedFormula Atom) :=
  b.filter fun sf =>
    match sf.sign, sf.formula with
    | .neg, .snce _ guard => guard != Formula.top
    | _, _ => false

/--
Collect all T(U(event, guard)) formulas in the branch (positive Until
formulas) where guard is NOT Formula.top (i.e., not someFuture).
-/
def untlPosFormulas (b : Branch Atom) : List (SignedFormula Atom) :=
  b.filter fun sf =>
    match sf.sign, sf.formula with
    | .pos, .untl _ guard => guard != Formula.top
    | _, _ => false

/--
Collect all T(S(event, guard)) formulas in the branch (positive Since
formulas) where guard is NOT Formula.top (i.e., not somePast).
-/
def sncePosFormulas (b : Branch Atom) : List (SignedFormula Atom) :=
  b.filter fun sf =>
    match sf.sign, sf.formula with
    | .pos, .snce _ guard => guard != Formula.top
    | _, _ => false

/--
Collect all T(GA) formulas at a specific time (across all worlds).
Used by world-creation rules to propagate temporal universals.
-/
def allFuturePosAtTime (b : Branch Atom) (t : TimeIndex) :
    List (SignedFormula Atom) :=
  b.filter fun sf =>
    match sf.sign, sf.formula with
    | .pos, .allFuture _ => sf.label.time == t
    | _, _ => false

/--
Collect all T(HA) formulas at a specific time (across all worlds).
-/
def allPastPosAtTime (b : Branch Atom) (t : TimeIndex) :
    List (SignedFormula Atom) :=
  b.filter fun sf =>
    match sf.sign, sf.formula with
    | .pos, .allPast _ => sf.label.time == t
    | _, _ => false

/--
Collect all F(FA) formulas at a specific time (across all worlds).
-/
def someFutureNegAtTime (b : Branch Atom) (t : TimeIndex) :
    List (SignedFormula Atom) :=
  b.filter fun sf =>
    match sf.sign, sf.formula with
    | .neg, .someFuture _ => sf.label.time == t
    | _, _ => false

/--
Collect all F(PA) formulas at a specific time (across all worlds).
-/
def somePastNegAtTime (b : Branch Atom) (t : TimeIndex) :
    List (SignedFormula Atom) :=
  b.filter fun sf =>
    match sf.sign, sf.formula with
    | .neg, .somePast _ => sf.label.time == t
    | _, _ => false

/--
Collect all F(U(event, guard)) formulas at a specific time,
where guard is NOT Formula.top.
-/
def untlNegAtTime (b : Branch Atom) (t : TimeIndex) :
    List (SignedFormula Atom) :=
  b.filter fun sf =>
    match sf.sign, sf.formula with
    | .neg, .untl _ guard =>
      guard != Formula.top && sf.label.time == t
    | _, _ => false

/--
Collect all F(S(event, guard)) formulas at a specific time,
where guard is NOT Formula.top.
-/
def snceNegAtTime (b : Branch Atom) (t : TimeIndex) :
    List (SignedFormula Atom) :=
  b.filter fun sf =>
    match sf.sign, sf.formula with
    | .neg, .snce _ guard =>
      guard != Formula.top && sf.label.time == t
    | _, _ => false

/--
Collect all T(□A) formulas at a specific world and time.
-/
def boxPosAtWorldTime (b : Branch Atom) (w : WorldIndex)
    (t : TimeIndex) : List (SignedFormula Atom) :=
  b.filter fun sf =>
    match sf.sign, sf.formula with
    | .pos, .box _ =>
      sf.label.world == w && sf.label.time == t
    | _, _ => false

/--
Collect all F(◇A) formulas at a specific world and time.
Diamond encoding: ◇A = ¬□¬A = (.imp (.box (.imp A .bot)) .bot)
-/
def diamondNegAtWorldTime (b : Branch Atom) (w : WorldIndex)
    (t : TimeIndex) : List (SignedFormula Atom) :=
  b.filter fun sf =>
    match sf.sign, sf.formula with
    | .neg, .imp (.box (.imp _ .bot)) .bot =>
      sf.label.world == w && sf.label.time == t
    | _, _ => false

end Branch

/-!
## Eventuality Tracking
-/

variable (Atom)

/--
An eventuality records a pending obligation from an Until or Since
formula. Until eventualities require the event to be witnessed at some
future time; Since eventualities require the event at some past time.
-/
structure Eventuality : Type _ where
  /-- The Until/Since formula that generated this eventuality. -/
  formula : Formula Atom
  /-- The label (world, time) at which the eventuality was introduced. -/
  label : Label
  /-- true for Until (future-directed), false for Since (past-directed). -/
  isUntil : Bool
  deriving DecidableEq, BEq

/--
Tracks pending eventualities on a tableau branch.
Provides operations to add new eventualities and mark them as fulfilled.
-/
structure EventualityTracker : Type _ where
  /-- List of pending eventualities. -/
  pending : List (Eventuality Atom)

variable {Atom}

namespace EventualityTracker

/-- Empty tracker with no pending eventualities. -/
def empty : EventualityTracker Atom := { pending := [] }

/-- Add a new eventuality to track. -/
def add (tracker : EventualityTracker Atom)
    (e : Eventuality Atom) : EventualityTracker Atom :=
  { pending := e :: tracker.pending }

/-- Remove a fulfilled eventuality (by formula and label match). -/
def fulfill (tracker : EventualityTracker Atom)
    (formula : Formula Atom) (label : Label) :
    EventualityTracker Atom :=
  { pending := tracker.pending.filter fun e =>
      !(e.formula == formula && e.label == label) }

/-- Check if there are any pending eventualities. -/
def hasPending (tracker : EventualityTracker Atom) : Bool :=
  !tracker.pending.isEmpty

/-- Get pending eventualities at a specific time index. -/
def pendingAtTime (tracker : EventualityTracker Atom)
    (t : TimeIndex) : List (Eventuality Atom) :=
  tracker.pending.filter fun e => e.label.time == t

/-- Check if an eventuality is fulfilled (no longer pending). -/
def isFulfilled (tracker : EventualityTracker Atom)
    (e : Eventuality Atom) : Bool :=
  !tracker.pending.any (· == e)

end EventualityTracker

/-!
## Subset Blocking for Temporal Tableau Termination

Subset blocking prevents infinite temporal chains in tableau expansion.
When a new time point t' has signed formulas that are a subset of an
ancestor time point t, further expansion from t' is blocked.
-/

namespace Branch

/--
Collect all signed formulas on a branch at a given time index.
-/
def formulasAtTime (b : Branch Atom) (t : TimeIndex) :
    List (SignedFormula Atom) :=
  b.filter fun sf => sf.label.time == t

/--
Extract the "time type" of a time point: the set of (sign, formula)
pairs at that time, deduplicated.
-/
def timeType (b : Branch Atom) (t : TimeIndex) :
    List (Sign × Formula Atom) :=
  ((b.formulasAtTime t).map fun sf =>
    (sf.sign, sf.formula)).eraseDups

/--
Check if the time type at `t1` is a subset of the time type at `t2`.
-/
def isSubsetBlocked (b : Branch Atom) (t_new t_anc : TimeIndex) :
    Bool :=
  let typeNew := b.timeType t_new
  let typeAnc := b.timeType t_anc
  typeNew.all fun pair => typeAnc.any fun pair' => pair == pair'

end Branch

/-!
## Time Ordering Constraints
-/

/--
Time ordering constraints for abstract temporal order tracking.
Each constraint `(a, b)` means `a` is strictly before `b` in the abstract
temporal order (a < b).
-/
structure TimeOrdering : Type where
  /-- List of ordering constraints. -/
  constraints : List (TimeIndex × TimeIndex)
  deriving Repr

namespace TimeOrdering

/-- Empty time ordering with no constraints. -/
def empty : TimeOrdering := { constraints := [] }

/-- Initial ordering: time 0 exists implicitly, no constraints needed. -/
def initWithTime0 : TimeOrdering := empty

/-- Add a future constraint: `t_new` is strictly after `t`. -/
def addFuture (ord : TimeOrdering) (t t_new : TimeIndex) :
    TimeOrdering :=
  { constraints := (t, t_new) :: ord.constraints }

/-- Add a past constraint: `t_new` is strictly before `t`. -/
def addPast (ord : TimeOrdering) (t t_new : TimeIndex) :
    TimeOrdering :=
  { constraints := (t_new, t) :: ord.constraints }

/-- Find all times strictly after `t`. -/
def futureOf (ord : TimeOrdering) (t : TimeIndex) : List TimeIndex :=
  ord.constraints.filterMap fun (a, b) =>
    if a == t then some b else none

/-- Find all times strictly before `t`. -/
def pastOf (ord : TimeOrdering) (t : TimeIndex) : List TimeIndex :=
  ord.constraints.filterMap fun (a, b) =>
    if b == t then some a else none

/-- Count distinct time indices appearing in the ordering constraints. -/
def timeCount (ord : TimeOrdering) : Nat :=
  let allTimes := ord.constraints.foldl (fun acc (a, b) =>
    let acc' := if acc.contains a then acc else a :: acc
    if acc'.contains b then acc' else b :: acc') ([] : List TimeIndex)
  allTimes.length

end TimeOrdering

/-!
## Subset Blocking (requires TimeOrdering)
-/

/--
Compute the transitive closure of temporal predecessors of a given
time index. Uses fuel to avoid infinite loops.
-/
def ancestorTimes (ord : TimeOrdering) (t : TimeIndex)
    (fuel : Nat := 100) : List TimeIndex :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
    let directPredecessors := ord.constraints.filterMap fun (a, b) =>
      if b == t then some a else none
    let directSuccessors := ord.constraints.filterMap fun (a, b) =>
      if a == t then some b else none
    let immediateAncestors :=
      (directPredecessors ++ directSuccessors).eraseDups
    let transitiveAncestors := immediateAncestors.flatMap fun anc =>
      anc :: ancestorTimes ord anc fuel
    transitiveAncestors.eraseDups

/--
Check if all pending eventualities at time `t_new` are either fulfilled
or duplicated at the blocking ancestor `t_anc`.
-/
def allEventualitiesFulfilledOrDuplicated
    (tracker : EventualityTracker Atom) (t_new t_anc : TimeIndex) :
    Bool :=
  let pendingAtNew := tracker.pendingAtTime t_new
  pendingAtNew.all fun e =>
    let duplicatedAtAnc := tracker.pending.any fun e' =>
      e'.formula == e.formula && e'.label.time == t_anc &&
        e'.isUntil == e.isUntil
    duplicatedAtAnc

/--
Check if a given time index is temporally blocked by any ancestor time.
-/
def isTemporallyBlocked (b : Branch Atom) (t : TimeIndex)
    (ord : TimeOrdering)
    (tracker : EventualityTracker Atom :=
      EventualityTracker.empty) : Bool :=
  let ancestors := ancestorTimes ord t
  ancestors.any fun t_anc =>
    b.isSubsetBlocked t t_anc &&
      allEventualitiesFulfilledOrDuplicated tracker t_anc t

/--
Check if ANY active time on the branch is temporally blocked.
Returns the first blocked time found, or `none` if no time is blocked.
-/
def findBlockedTime (b : Branch Atom) (ord : TimeOrdering)
    (tracker : EventualityTracker Atom :=
      EventualityTracker.empty) : Option TimeIndex :=
  b.knownTimes.find? fun t => isTemporallyBlocked b t ord tracker

/--
State tracking for blocking decisions during tableau expansion.
Records which times have been blocked and the blocking ancestor.
-/
structure BlockingState where
  /-- List of (blocked_time, blocking_ancestor) pairs. -/
  blockedTimes : List (TimeIndex × TimeIndex)
  deriving Repr

namespace BlockingState

/-- Empty blocking state. -/
def empty : BlockingState := { blockedTimes := [] }

/-- Record that a time has been blocked by an ancestor. -/
def addBlocked (state : BlockingState) (t t_anc : TimeIndex) :
    BlockingState :=
  { blockedTimes := (t, t_anc) :: state.blockedTimes }

/-- Check if a time is already recorded as blocked. -/
def isBlocked (state : BlockingState) (t : TimeIndex) : Bool :=
  state.blockedTimes.any fun (blocked, _) => blocked == t

end BlockingState

/-!
## Subformula Closure
-/

/--
Compute the subformula closure for a branch.

The subformula closure contains all subformulas of all formulas in the
branch. This bounds the size of the tableau and ensures termination.
-/
def subformulaClosure (b : Branch Atom) : List (Formula Atom) :=
  (b.flatMap (fun sf => sf.formula.subformulas)).eraseDups

/--
Signed subformula closure: all signed versions of the subformula closure.
-/
def signedSubformulaClosure (b : Branch Atom) :
    List (SignedFormula Atom) :=
  let subs := subformulaClosure b
  subs.flatMap (fun φ => [SignedFormula.pos φ, SignedFormula.neg φ])

/-!
## Complexity Measures for Termination
-/

/--
Unexpanded complexity of a signed formula.
Atomic formulas and bot have 0 unexpanded complexity.
-/
def unexpandedComplexity (sf : SignedFormula Atom) : Nat :=
  match sf.formula with
  | .atom _ => 0
  | .bot => 0
  | .imp _ _ => sf.formula.complexity
  | .box _ => sf.formula.complexity
  | .untl _ _ => sf.formula.complexity
  | .snce _ _ => sf.formula.complexity

/--
Total unexpanded complexity of a branch.
This decreases with each tableau expansion step, ensuring termination.
-/
def branchUnexpandedComplexity (b : Branch Atom) : Nat :=
  b.foldl (fun acc sf => acc + unexpandedComplexity sf) 0

end Cslib.Logic.Bimodal.Metalogic.Decidability
