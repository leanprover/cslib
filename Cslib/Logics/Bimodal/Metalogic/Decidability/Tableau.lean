/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import Cslib.Logics.Bimodal.Metalogic.Decidability.SignedFormula
import Cslib.Logics.Bimodal.ProofSystem.Axioms

/-!
# Tableau Rules for TM Bimodal Logic

This module defines the tableau expansion rules for the TM bimodal logic
decision procedure. The rules systematically decompose signed formulas
until branches close (contradiction found) or saturate (countermodel exists).

## Main Definitions

- `TableauRule`: Enumeration of all tableau expansion rules
- `RuleResult`: Result of applying a rule (linear extension or branching)
- `applyRule`: Apply a tableau rule to a signed formula
- `expandOnce`: Single-step expansion of a branch
- `AppliedSet`: HashSet tracking persistent rule outputs

## Tableau Rules

### Propositional Rules
- `andPos`: T(A AND B) -> T(A), T(B) (non-branching)
- `andNeg`: F(A AND B) -> F(A) | F(B) (branching)
- `orPos`: T(A OR B) -> T(A) | T(B) (branching)
- `orNeg`: F(A OR B) -> F(A), F(B) (non-branching)
- `impPos`: T(A -> B) -> F(A) | T(B) (branching)
- `impNeg`: F(A -> B) -> T(A), F(B) (non-branching)
- `negPos`: T(neg A) -> F(A) (non-branching)
- `negNeg`: F(neg A) -> T(A) (non-branching)

### Modal S5 Rules
- `boxPos`: T(box A) -> propagate T(A) to accessible states
- `boxNeg`: F(box A) -> create state with F(A)

### Temporal Rules
- `allFuturePos`: T(GA) -> propagate T(A) to future times
- `allFutureNeg`: F(GA) -> create future time with F(A)
- `allPastPos`: T(HA) -> propagate T(A) to past times
- `allPastNeg`: F(HA) -> create past time with F(A)

## Implementation Notes

Since TM combines S5 modal logic with linear temporal logic, we use a
simplified tableau system that exploits the special properties of S5
(all worlds are mutually accessible, so we can use a single equivalence class).

Ported from BimodalLogic with universe-polymorphic `Formula Atom` replacing
monomorphic `Formula`.

## References

* Gore, R. (1999). Tableau Methods for Modal and Temporal Logics
* Wu, M. Verified Decision Procedures for Modal Logics
-/

set_option linter.style.longLine false

namespace Cslib.Logic.Bimodal.Metalogic.Decidability

open Cslib.Logic.Bimodal

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-!
## Tableau Rule Type
-/

/--
Tableau expansion rules for TM bimodal logic.

Each rule specifies how to decompose a signed formula. Rules are either:
- **Linear** (non-branching): Add formulas to the current branch
- **Branching**: Split into multiple branches (any must close for tableau to close)
-/
inductive TableauRule : Type where
  /-- T(A AND B) -> T(A), T(B) (A AND B = neg(A -> neg B)) -/
  | andPos
  /-- F(A AND B) -> F(A) | F(B) (branching) -/
  | andNeg
  /-- T(A OR B) -> T(A) | T(B) (A OR B = neg A -> B, branching) -/
  | orPos
  /-- F(A OR B) -> F(A), F(B) -/
  | orNeg
  /-- T(A -> B) -> F(A) | T(B) (branching) -/
  | impPos
  /-- F(A -> B) -> T(A), F(B) -/
  | impNeg
  /-- T(neg A) -> F(A) (neg A = A -> bot) -/
  | negPos
  /-- F(neg A) -> T(A) -/
  | negNeg
  /-- T(box A) -> propagate T(A) to all known worlds (S5 universal, persistent) -/
  | boxPos
  /-- F(box A) -> introduce fresh witness world with F(A), auto-propagate universals -/
  | boxNeg
  /-- T(diamond A) -> introduce fresh witness world with T(A), auto-propagate universals -/
  | diamondPos
  /-- F(diamond A) -> propagate F(A) to all known worlds (S5 universal, persistent) -/
  | diamondNeg
  /-- T(box A) -> derive T(GA) and T(HA) at the same label (modal-temporal interaction, persistent).
      Sound by box_to_future (box phi -> G phi) and box_to_past (box phi -> H phi). -/
  | boxTemporal
  /-- T(GA) -> propagate T(A) to all known future times (universal, persistent) -/
  | allFuturePos
  /-- F(GA) -> F(A) at fresh future time (existential, consumable) -/
  | allFutureNeg
  /-- T(HA) -> propagate T(A) to all known past times (universal, persistent) -/
  | allPastPos
  /-- F(HA) -> F(A) at fresh past time (existential, consumable) -/
  | allPastNeg
  /-- T(FA) -> T(A) at fresh future time (existential, consumable) -/
  | someFuturePos
  /-- F(FA) -> propagate F(A) to all known future times (universal, persistent) -/
  | someFutureNeg
  /-- T(PA) -> T(A) at fresh past time (existential, consumable) -/
  | somePastPos
  /-- F(PA) -> propagate F(A) to all known past times (universal, persistent) -/
  | somePastNeg
  /-- T(U(event,guard)) -> branch: event-witness at fresh future
      time OR guard+continue (consumable) -/
  | untlPos
  /-- F(U(event,guard)) -> Reynolds co-decomposition at known
      future times (persistent) -/
  | untlNeg
  /-- T(S(event,guard)) -> branch: event-witness at fresh past
      time OR guard+continue (consumable) -/
  | sncePos
  /-- F(S(event,guard)) -> Reynolds co-decomposition at known
      past times (persistent) -/
  | snceNeg
  /-- Dense: close branch when T(U(top,bot)) appears (since
      neg U(top,bot) is a Dense axiom, asserting U(top,bot)
      leads to contradiction on dense frames).
      Only applicable when fc >= .Dense. -/
  | denseIndicatorClosure
  /-- Dense: when T(G(phi)) at (w,t) and there exists a future
      time t' > t on the branch, introduce an intermediate time
      t'' with t < t'' < t' and add T(phi) at (w,t'').
      Captures density: between any two time points there is
      another. Only when fc >= .Dense. -/
  | densityRule
  /-- Discrete: when T(F(phi)) at (w,t), add T(U(phi, neg phi))
      at (w,t). Captures "nearest future phi-point reachable by
      Until". Only when fc >= .Discrete. -/
  | priorUZ
  /-- Discrete: when T(P(phi)) at (w,t), add T(S(phi, neg phi))
      at (w,t). Captures "nearest past phi-point reachable by
      Since". Only when fc >= .Discrete. -/
  | priorSZ
  /-- Discrete: when both T(G(G(phi) -> phi)) and T(F(G(phi)))
      at same label, add T(G(phi)). Z1 backward induction axiom.
      Only when fc >= .Discrete. -/
  | z1Rule
  deriving Repr, DecidableEq, BEq, Hashable

/-!
## Rule Result Type
-/

/--
Result of applying a tableau rule to a signed formula.

- `linear`: Add formulas to the current branch (non-branching)
- `branching`: Split into multiple branches (all must close for validity)
- `persistent`: Like linear but source formula is kept on branch
- `notApplicable`: Rule doesn't apply to this signed formula
-/
inductive RuleResult (Atom : Type*) [DecidableEq Atom] [Hashable Atom] : Type _ where
  /-- Add these signed formulas to the current branch. -/
  | linear (formulas : List (SignedFormula Atom))
  /-- Split into multiple branches (each is a list of formulas to add). -/
  | branching (branches : List (List (SignedFormula Atom)))
  /-- Universal modal rule: add formulas but do NOT remove the source formula.
      Used for T(box A) and F(diamond A) which must persist for propagation to new worlds. -/
  | persistent (formulas : List (SignedFormula Atom))
  /-- Rule does not apply to this signed formula. -/
  | notApplicable

/-!
## Formula Decomposition Helpers
-/

/--
Try to decompose a formula as negation (A -> bot).
Returns `some A` if the formula is `A.imp .bot`, otherwise `none`.
-/
def asNeg? : Formula Atom → Option (Formula Atom)
  | .imp φ .bot => some φ
  | _ => none

/--
Try to decompose a formula as conjunction (neg(A -> neg B)).
Note: A AND B = (A.imp B.neg).neg = (A.imp (B.imp .bot)).imp .bot
Returns `some (A, B)` if it matches the pattern, otherwise `none`.
-/
def asAnd? : Formula Atom → Option (Formula Atom × Formula Atom)
  | .imp (.imp φ (.imp ψ .bot)) .bot => some (φ, ψ)
  | _ => none

/--
Try to decompose a formula as disjunction (neg A -> B).
Note: A OR B = A.neg.imp B = (A.imp .bot).imp B
Returns `some (A, B)` if it matches the pattern, otherwise `none`.
-/
def asOr? : Formula Atom → Option (Formula Atom × Formula Atom)
  | .imp (.imp φ .bot) ψ => some (φ, ψ)
  | _ => none

/--
Try to decompose a formula as diamond (neg box neg A).
Note: diamond A = A.neg.box.neg = ((A.imp .bot).box).imp .bot
Returns `some A` if it matches the pattern, otherwise `none`.
-/
def asDiamond? : Formula Atom → Option (Formula Atom)
  | .imp (.box (.imp φ .bot)) .bot => some φ
  | _ => none

/--
Try to decompose a formula as somePast (PA = S(A, top)).
Note: somePast A = snce A top = snce A (imp bot bot)
Returns `some A` if it matches the pattern, otherwise `none`.
-/
def asSomePast? : Formula Atom → Option (Formula Atom)
  | .somePast φ => some φ
  | _ => none

/--
Try to decompose a formula as someFuture (FA = U(A, top)).
Note: someFuture A = untl A top = untl A (imp bot bot)
Returns `some A` if it matches the pattern, otherwise `none`.
-/
def asSomeFuture? : Formula Atom → Option (Formula Atom)
  | .someFuture φ => some φ
  | _ => none

/--
Try to decompose a formula as allFuture (GA = neg F neg A = neg(U(neg A, top))).
Note: allFuture A = (someFuture A.neg).neg
Returns `some A` if it matches the pattern, otherwise `none`.
-/
def asAllFuture? : Formula Atom → Option (Formula Atom)
  | .allFuture φ => some φ
  | _ => none

/--
Try to decompose a formula as allPast (HA = neg P neg A = neg(S(neg A, top))).
Note: allPast A = (somePast A.neg).neg
Returns `some A` if it matches the pattern, otherwise `none`.
-/
def asAllPast? : Formula Atom → Option (Formula Atom)
  | .allPast φ => some φ
  | _ => none

/--
Try to decompose a formula as a genuine Until (not someFuture).
Returns `some (event, guard)` if the formula is `untl event guard` with `guard != top`.
This filters out `someFuture phi = untl phi top` which is handled by someFuturePos/someFutureNeg.
Burgess convention: first component = event, second = guard.
-/
def asUntil? : Formula Atom → Option (Formula Atom × Formula Atom)
  | .untl event guard =>
    if guard == Formula.top then none
    else some (event, guard)
  | _ => none

/--
Try to decompose a formula as a genuine Since (not somePast).
Returns `some (event, guard)` if the formula is `snce event guard` with `guard != top`.
This filters out `somePast phi = snce phi top` which is handled by somePastPos/somePastNeg.
Burgess convention: first component = event, second = guard.
-/
def asSince? : Formula Atom → Option (Formula Atom × Formula Atom)
  | .snce event guard =>
    if guard == Formula.top then none
    else some (event, guard)
  | _ => none

/-!
## Rule Application
-/

/--
Check if a specific rule is applicable to a signed formula.
-/
def isApplicable (rule : TableauRule) (sf : SignedFormula Atom)
    (fc : FrameClass := .Base) : Bool :=
  match rule, sf.sign, sf.formula with
  -- Propositional rules
  | .andPos, .pos, φ => (asNeg? φ).isNone && (asAnd? φ).isSome
  | .andNeg, .neg, φ => (asAnd? φ).isSome
  | .orPos, .pos, φ => (asOr? φ).isSome
  | .orNeg, .neg, φ => (asOr? φ).isSome
  | .impPos, .pos, .imp _ _ => true
  | .impNeg, .neg, .imp _ _ => true
  | .negPos, .pos, φ => (asNeg? φ).isSome
  | .negNeg, .neg, φ => (asNeg? φ).isSome
  -- Modal rules
  | .boxPos, .pos, .box _ => true
  | .boxNeg, .neg, .box _ => true
  | .diamondPos, .pos, φ => (asDiamond? φ).isSome
  | .diamondNeg, .neg, φ => (asDiamond? φ).isSome
  -- Modal-temporal interaction
  | .boxTemporal, .pos, .box _ => true
  -- Temporal rules (G/H universal)
  | .allFuturePos, .pos, .allFuture _ => true
  | .allFutureNeg, .neg, .allFuture _ => true
  | .allPastPos, .pos, .allPast _ => true
  | .allPastNeg, .neg, .allPast _ => true
  -- Temporal rules (F/P existential)
  | .someFuturePos, .pos, φ => (asSomeFuture? φ).isSome
  | .someFutureNeg, .neg, φ => (asSomeFuture? φ).isSome
  | .somePastPos, .pos, φ => (asSomePast? φ).isSome
  | .somePastNeg, .neg, φ => (asSomePast? φ).isSome
  -- Until/Since rules (genuine, not someFuture/somePast)
  | .untlPos, .pos, φ => (asUntil? φ).isSome
  | .untlNeg, .neg, φ => (asUntil? φ).isSome
  | .sncePos, .pos, φ => (asSince? φ).isSome
  | .snceNeg, .neg, φ => (asSince? φ).isSome
  -- Dense-specific rules (gated by fc >= .Dense)
  | .denseIndicatorClosure, .pos, .untl (.imp .bot .bot) .bot =>
      decide (FrameClass.Dense ≤ fc)
  | .densityRule, .pos, .allFuture _ =>
      decide (FrameClass.Dense ≤ fc)
  -- Discrete-specific rules (gated by fc >= .Discrete)
  | .priorUZ, .pos, φ => decide (FrameClass.Discrete ≤ fc) && (asSomeFuture? φ).isSome
  | .priorSZ, .pos, φ => decide (FrameClass.Discrete ≤ fc) && (asSomePast? φ).isSome
  | .z1Rule, .pos, .allFuture _ => decide (FrameClass.Discrete ≤ fc)
  | _, _, _ => false

/--
Helper: collect T(box A) and F(diamond A) formulas at a specific world and time,
re-labeled to a fresh time. Used by time-creation rules to propagate
box persistence (box phi -> G(box phi)) and diamond-neg persistence.
-/
private def boxDiamondPersistence (branch : Branch Atom) (w : WorldIndex) (t : TimeIndex)
    (freshTime : TimeIndex) : List (SignedFormula Atom) :=
  let boxProps := (branch.boxPosAtWorldTime w t).filterMap fun bsf =>
    let prop := { bsf with label := { bsf.label with time := freshTime } }
    if branch.contains prop then none else some prop
  let diaProps := (branch.diamondNegAtWorldTime w t).filterMap fun dsf =>
    let prop := { dsf with label := { dsf.label with time := freshTime } }
    if branch.contains prop then none else some prop
  boxProps ++ diaProps

/--
Apply a tableau rule to a signed formula.

Returns the rule result and the (possibly updated) time ordering.
The `branch` parameter provides context for propagation rules.
-/
def applyRule (rule : TableauRule) (sf : SignedFormula Atom) (branch : Branch Atom := [])
    (timeOrd : TimeOrdering := TimeOrdering.empty) :
    RuleResult Atom × TimeOrdering :=
  let l := sf.label
  match rule, sf.sign, sf.formula with
  -- T(A AND B) -> T(A), T(B)
  | .andPos, .pos, φ =>
      match asAnd? φ with
      | some (ψ, χ) => (.linear [SignedFormula.pos ψ l, SignedFormula.pos χ l], timeOrd)
      | none => (.notApplicable, timeOrd)
  -- F(A AND B) -> F(A) | F(B)
  | .andNeg, .neg, φ =>
      match asAnd? φ with
      | some (ψ, χ) => (.branching [[SignedFormula.neg ψ l], [SignedFormula.neg χ l]], timeOrd)
      | none => (.notApplicable, timeOrd)
  -- T(A OR B) -> T(A) | T(B)
  | .orPos, .pos, φ =>
      match asOr? φ with
      | some (ψ, χ) => (.branching [[SignedFormula.pos ψ l], [SignedFormula.pos χ l]], timeOrd)
      | none => (.notApplicable, timeOrd)
  -- F(A OR B) -> F(A), F(B)
  | .orNeg, .neg, φ =>
      match asOr? φ with
      | some (ψ, χ) => (.linear [SignedFormula.neg ψ l, SignedFormula.neg χ l], timeOrd)
      | none => (.notApplicable, timeOrd)
  -- T(A -> B) -> F(A) | T(B)
  | .impPos, .pos, .imp ψ χ =>
      (.branching [[SignedFormula.neg ψ l], [SignedFormula.pos χ l]], timeOrd)
  -- F(A -> B) -> T(A), F(B)
  | .impNeg, .neg, .imp ψ χ =>
      (.linear [SignedFormula.pos ψ l, SignedFormula.neg χ l], timeOrd)
  -- T(neg A) -> F(A)
  | .negPos, .pos, φ =>
      match asNeg? φ with
      | some ψ => (.linear [SignedFormula.neg ψ l], timeOrd)
      | none => (.notApplicable, timeOrd)
  -- F(neg A) -> T(A)
  | .negNeg, .neg, φ =>
      match asNeg? φ with
      | some ψ => (.linear [SignedFormula.pos ψ l], timeOrd)
      | none => (.notApplicable, timeOrd)
  -- T(box A) -> propagate T(A) to all known worlds (S5 universal, persistent)
  | .boxPos, .pos, .box ψ =>
      let worlds := branch.knownWorlds
      let newFormulas := worlds.filterMap fun w =>
        let newSf := SignedFormula.pos ψ { world := w, time := l.time }
        if branch.contains newSf then none else some newSf
      if newFormulas.isEmpty then (.notApplicable, timeOrd)
      else (.persistent newFormulas, timeOrd)
  -- F(box A) -> F(A) at fresh witness world + auto-propagate universals (S5 existential)
  | .boxNeg, .neg, .box ψ =>
      let freshWorld := branch.nextWorld
      let freshLabel : Label := { world := freshWorld, time := l.time }
      -- The witness: F(A) at the fresh world
      let witness := SignedFormula.neg ψ freshLabel
      -- Auto-propagate all T(box B) formulas to the fresh world
      let boxProps := branch.boxPosFormulas.filterMap fun bsf =>
        match bsf.formula with
        | .box inner =>
          let prop := SignedFormula.pos inner { world := freshWorld, time := bsf.label.time }
          if branch.contains prop then none else some prop
        | _ => none
      -- Auto-propagate all F(diamond B) formulas to the fresh world
      let diaProps := branch.diamondNegFormulas.filterMap fun dsf =>
        match dsf.formula with
        | .imp (.box (.imp inner .bot)) .bot =>
          let prop := SignedFormula.neg inner { world := freshWorld, time := dsf.label.time }
          if branch.contains prop then none else some prop
        | _ => none
      -- Cross-modal-temporal: propagate temporal universals at time l.time to fresh world
      let tempGProps := (branch.allFuturePosAtTime l.time).filterMap fun gsf =>
        let prop := { gsf with label := { gsf.label with world := freshWorld } }
        if branch.contains prop then none else some prop
      let tempHProps := (branch.allPastPosAtTime l.time).filterMap fun hsf =>
        let prop := { hsf with label := { hsf.label with world := freshWorld } }
        if branch.contains prop then none else some prop
      let tempFNegProps := (branch.someFutureNegAtTime l.time).filterMap fun fsf =>
        let prop := { fsf with label := { fsf.label with world := freshWorld } }
        if branch.contains prop then none else some prop
      let tempPNegProps := (branch.somePastNegAtTime l.time).filterMap fun psf =>
        let prop := { psf with label := { psf.label with world := freshWorld } }
        if branch.contains prop then none else some prop
      let tempUNegProps := (branch.untlNegAtTime l.time).filterMap fun usf =>
        let prop := { usf with label := { usf.label with world := freshWorld } }
        if branch.contains prop then none else some prop
      let tempSNegProps := (branch.snceNegAtTime l.time).filterMap fun ssf =>
        let prop := { ssf with label := { ssf.label with world := freshWorld } }
        if branch.contains prop then none else some prop
      let temporalProps := tempGProps ++ tempHProps ++ tempFNegProps ++
        tempPNegProps ++ tempUNegProps ++ tempSNegProps
      (.linear (witness :: boxProps ++ diaProps ++ temporalProps), timeOrd)
  -- T(diamond A) -> T(A) at fresh witness world + auto-propagate universals (S5 existential)
  | .diamondPos, .pos, φ =>
      match asDiamond? φ with
      | some ψ =>
        let freshWorld := branch.nextWorld
        let freshLabel : Label := { world := freshWorld, time := l.time }
        -- The witness: T(A) at the fresh world
        let witness := SignedFormula.pos ψ freshLabel
        -- Auto-propagate all T(box B) formulas to the fresh world
        let boxProps := branch.boxPosFormulas.filterMap fun bsf =>
          match bsf.formula with
          | .box inner =>
            let prop := SignedFormula.pos inner { world := freshWorld, time := bsf.label.time }
            if branch.contains prop then none else some prop
          | _ => none
        -- Auto-propagate all F(diamond B) formulas to the fresh world
        let diaProps := branch.diamondNegFormulas.filterMap fun dsf =>
          match dsf.formula with
          | .imp (.box (.imp inner .bot)) .bot =>
            let prop := SignedFormula.neg inner { world := freshWorld, time := dsf.label.time }
            if branch.contains prop then none else some prop
          | _ => none
        -- Cross-modal-temporal: propagate temporal universals at time l.time to fresh world
        let tempGProps := (branch.allFuturePosAtTime l.time).filterMap fun gsf =>
          let prop := { gsf with label := { gsf.label with world := freshWorld } }
          if branch.contains prop then none else some prop
        let tempHProps := (branch.allPastPosAtTime l.time).filterMap fun hsf =>
          let prop := { hsf with label := { hsf.label with world := freshWorld } }
          if branch.contains prop then none else some prop
        let tempFNegProps := (branch.someFutureNegAtTime l.time).filterMap fun fsf =>
          let prop := { fsf with label := { fsf.label with world := freshWorld } }
          if branch.contains prop then none else some prop
        let tempPNegProps := (branch.somePastNegAtTime l.time).filterMap fun psf =>
          let prop := { psf with label := { psf.label with world := freshWorld } }
          if branch.contains prop then none else some prop
        let tempUNegProps := (branch.untlNegAtTime l.time).filterMap fun usf =>
          let prop := { usf with label := { usf.label with world := freshWorld } }
          if branch.contains prop then none else some prop
        let tempSNegProps := (branch.snceNegAtTime l.time).filterMap fun ssf =>
          let prop := { ssf with label := { ssf.label with world := freshWorld } }
          if branch.contains prop then none else some prop
        let temporalProps := tempGProps ++ tempHProps ++ tempFNegProps ++
          tempPNegProps ++ tempUNegProps ++ tempSNegProps
        (.linear (witness :: boxProps ++ diaProps ++ temporalProps), timeOrd)
      | none => (.notApplicable, timeOrd)
  -- F(diamond A) -> propagate F(A) to all known worlds (S5 universal, persistent)
  | .diamondNeg, .neg, φ =>
      match asDiamond? φ with
      | some ψ =>
        let worlds := branch.knownWorlds
        let newFormulas := worlds.filterMap fun w =>
          let newSf := SignedFormula.neg ψ { world := w, time := l.time }
          if branch.contains newSf then none else some newSf
        if newFormulas.isEmpty then (.notApplicable, timeOrd)
        else (.persistent newFormulas, timeOrd)
      | none => (.notApplicable, timeOrd)
  -- T(box A) -> derive T(GA) and T(HA) at the same label (modal-temporal interaction)
  -- Sound by box_to_future (box phi -> G phi) and box_to_past (box phi -> H phi)
  | .boxTemporal, .pos, .box ψ =>
      let gFormula := SignedFormula.pos (Formula.allFuture ψ) l
      let hFormula := SignedFormula.pos (Formula.allPast ψ) l
      let newFormulas := [gFormula, hFormula].filter fun sf => !branch.contains sf
      if newFormulas.isEmpty then (.notApplicable, timeOrd)
      else (.persistent newFormulas, timeOrd)
  -- T(GA) @ (w,t) -> propagate T(A) to all known future times (universal, persistent)
  -- Strict inequality: G(A) at t means A holds at all t' > t
  | .allFuturePos, .pos, .allFuture ψ =>
      let futureTimes := timeOrd.futureOf l.time
      let newFormulas := futureTimes.filterMap fun t' =>
        let newSf := SignedFormula.pos ψ { world := l.world, time := t' }
        if branch.contains newSf then none else some newSf
      if newFormulas.isEmpty then (.notApplicable, timeOrd)
      else (.persistent newFormulas, timeOrd)
  -- F(GA) @ (w,t) -> F(A) at fresh future time (existential, consumable)
  -- neg G(A) at t means there exists t' > t where neg A
  | .allFutureNeg, .neg, .allFuture ψ =>
      let freshTime := branch.nextTime
      let freshLabel : Label := { world := l.world, time := freshTime }
      let newOrd := timeOrd.addFuture l.time freshTime
      -- The witness: F(A) at the fresh future time
      let witness := SignedFormula.neg ψ freshLabel
      -- Auto-propagate all T(GA) formulas from time t to freshTime
      let gProps := branch.allFuturePosFormulas.filterMap fun gsf =>
        match gsf.formula with
        | .allFuture inner =>
          -- Only propagate if freshTime is future of gsf's time
          -- Since we only added (l.time, freshTime), check gsf is at time l.time
          if gsf.label.time == l.time then
            let prop := SignedFormula.pos inner { world := gsf.label.world, time := freshTime }
            if branch.contains prop then none else some prop
          else none
        | _ => none
      -- Auto-propagate all F(FA) formulas from time t to freshTime
      let fNegProps := branch.someFutureNegFormulas.filterMap fun fsf =>
        match fsf.formula with
        | .someFuture inner =>
          if fsf.label.time == l.time then
            let prop := SignedFormula.neg inner { world := fsf.label.world, time := freshTime }
            if branch.contains prop then none else some prop
          else none
        | _ => none
      -- Cross-modal-temporal: propagate T(box A) and F(diamond A) to fresh future time
      let modalProps := boxDiamondPersistence branch l.world l.time freshTime
      (.linear (witness :: gProps ++ fNegProps ++ modalProps), newOrd)
  -- T(HA) @ (w,t) -> propagate T(A) to all known past times (universal, persistent)
  -- Strict inequality: H(A) at t means A holds at all t' < t
  | .allPastPos, .pos, .allPast ψ =>
      let pastTimes := timeOrd.pastOf l.time
      let newFormulas := pastTimes.filterMap fun t' =>
        let newSf := SignedFormula.pos ψ { world := l.world, time := t' }
        if branch.contains newSf then none else some newSf
      if newFormulas.isEmpty then (.notApplicable, timeOrd)
      else (.persistent newFormulas, timeOrd)
  -- F(HA) @ (w,t) -> F(A) at fresh past time (existential, consumable)
  -- neg H(A) at t means there exists t' < t where neg A
  | .allPastNeg, .neg, .allPast ψ =>
      let freshTime := branch.nextTime
      let freshLabel : Label := { world := l.world, time := freshTime }
      let newOrd := timeOrd.addPast l.time freshTime
      -- The witness: F(A) at the fresh past time
      let witness := SignedFormula.neg ψ freshLabel
      -- Auto-propagate all T(HA) formulas from time t to freshTime
      let hProps := branch.allPastPosFormulas.filterMap fun hsf =>
        match hsf.formula with
        | .allPast inner =>
          -- Only propagate if freshTime is past of hsf's time
          -- Since we added (freshTime, l.time), check hsf is at time l.time
          if hsf.label.time == l.time then
            let prop := SignedFormula.pos inner { world := hsf.label.world, time := freshTime }
            if branch.contains prop then none else some prop
          else none
        | _ => none
      -- Auto-propagate all F(PA) formulas from time t to freshTime
      let pNegProps := branch.somePastNegFormulas.filterMap fun psf =>
        match psf.formula with
        | .somePast inner =>
          if psf.label.time == l.time then
            let prop := SignedFormula.neg inner { world := psf.label.world, time := freshTime }
            if branch.contains prop then none else some prop
          else none
        | _ => none
      -- Cross-modal-temporal: propagate T(box A) and F(diamond A) to fresh past time
      let modalProps := boxDiamondPersistence branch l.world l.time freshTime
      (.linear (witness :: hProps ++ pNegProps ++ modalProps), newOrd)
  -- T(FA) @ (w,t) -> T(A) at fresh future time (existential, consumable)
  -- F(A) at t means there exists t' > t where A holds
  | .someFuturePos, .pos, φ =>
      match asSomeFuture? φ with
      | some ψ =>
        let freshTime := branch.nextTime
        let freshLabel : Label := { world := l.world, time := freshTime }
        let newOrd := timeOrd.addFuture l.time freshTime
        -- The witness: T(A) at the fresh future time
        let witness := SignedFormula.pos ψ freshLabel
        -- Auto-propagate all T(GA) formulas from time t to freshTime
        let gProps := branch.allFuturePosFormulas.filterMap fun gsf =>
          match gsf.formula with
          | .allFuture inner =>
            if gsf.label.time == l.time then
              let prop := SignedFormula.pos inner { world := gsf.label.world, time := freshTime }
              if branch.contains prop then none else some prop
            else none
          | _ => none
        -- Auto-propagate all F(FA) formulas from time t to freshTime
        let fNegProps := branch.someFutureNegFormulas.filterMap fun fsf =>
          match fsf.formula with
          | .someFuture inner =>
            if fsf.label.time == l.time then
              let prop := SignedFormula.neg inner { world := fsf.label.world, time := freshTime }
              if branch.contains prop then none else some prop
            else none
          | _ => none
        -- Cross-modal-temporal: propagate T(box A) and F(diamond A) to fresh future time
        let modalProps := boxDiamondPersistence branch l.world l.time freshTime
        (.linear (witness :: gProps ++ fNegProps ++ modalProps), newOrd)
      | none => (.notApplicable, timeOrd)
  -- F(FA) @ (w,t) -> propagate F(A) to all known future times (universal, persistent)
  -- F(FA) = neg(FA) means at all future times, A fails
  | .someFutureNeg, .neg, φ =>
      match asSomeFuture? φ with
      | some ψ =>
        let futureTimes := timeOrd.futureOf l.time
        let newFormulas := futureTimes.filterMap fun t' =>
          let newSf := SignedFormula.neg ψ { world := l.world, time := t' }
          if branch.contains newSf then none else some newSf
        if newFormulas.isEmpty then (.notApplicable, timeOrd)
        else (.persistent newFormulas, timeOrd)
      | none => (.notApplicable, timeOrd)
  -- T(PA) @ (w,t) -> T(A) at fresh past time (existential, consumable)
  -- P(A) at t means there exists t' < t where A holds
  | .somePastPos, .pos, φ =>
      match asSomePast? φ with
      | some ψ =>
        let freshTime := branch.nextTime
        let freshLabel : Label := { world := l.world, time := freshTime }
        let newOrd := timeOrd.addPast l.time freshTime
        -- The witness: T(A) at the fresh past time
        let witness := SignedFormula.pos ψ freshLabel
        -- Auto-propagate all T(HA) formulas from time t to freshTime
        let hProps := branch.allPastPosFormulas.filterMap fun hsf =>
          match hsf.formula with
          | .allPast inner =>
            if hsf.label.time == l.time then
              let prop := SignedFormula.pos inner { world := hsf.label.world, time := freshTime }
              if branch.contains prop then none else some prop
            else none
          | _ => none
        -- Auto-propagate all F(PA) formulas from time t to freshTime
        let pNegProps := branch.somePastNegFormulas.filterMap fun psf =>
          match psf.formula with
          | .somePast inner =>
            if psf.label.time == l.time then
              let prop := SignedFormula.neg inner { world := psf.label.world, time := freshTime }
              if branch.contains prop then none else some prop
            else none
          | _ => none
        -- Cross-modal-temporal: propagate T(box A) and F(diamond A) to fresh past time
        let modalProps := boxDiamondPersistence branch l.world l.time freshTime
        (.linear (witness :: hProps ++ pNegProps ++ modalProps), newOrd)
      | none => (.notApplicable, timeOrd)
  -- F(PA) @ (w,t) -> propagate F(A) to all known past times (universal, persistent)
  -- F(PA) = neg(PA) means at all past times, A fails
  | .somePastNeg, .neg, φ =>
      match asSomePast? φ with
      | some ψ =>
        let pastTimes := timeOrd.pastOf l.time
        let newFormulas := pastTimes.filterMap fun t' =>
          let newSf := SignedFormula.neg ψ { world := l.world, time := t' }
          if branch.contains newSf then none else some newSf
        if newFormulas.isEmpty then (.notApplicable, timeOrd)
        else (.persistent newFormulas, timeOrd)
      | none => (.notApplicable, timeOrd)
  -- T(U(event, guard)) @ (w,t) -> branch: event-witness at fresh future time OR guard+continue
  -- Consumable: removed after application. Creates fresh time t' > t.
  -- Branch 1 (event witness): T(event) @ (w, t')
  -- Branch 2 (guard + continue): T(guard) @ (w, t'), T(U(event, guard)) @ (w, t')
  | .untlPos, .pos, φ =>
      match asUntil? φ with
      | some (event, guard) =>
        let freshTime := branch.nextTime
        let freshLabel : Label := { world := l.world, time := freshTime }
        let newOrd := timeOrd.addFuture l.time freshTime
        -- Branch 1: event witness at fresh future time
        let branch1 := [SignedFormula.pos event freshLabel]
        -- Branch 2: guard holds at fresh time + Until continues from fresh time
        let branch2 := [SignedFormula.pos guard freshLabel,
                         SignedFormula.pos (.untl event guard) freshLabel]
        -- Auto-propagate all T(GA) formulas to freshTime
        let gProps := branch.allFuturePosFormulas.filterMap fun gsf =>
          match gsf.formula with
          | .allFuture inner =>
            if gsf.label.time == l.time then
              let prop := SignedFormula.pos inner { world := gsf.label.world, time := freshTime }
              if branch.contains prop then none else some prop
            else none
          | _ => none
        -- Auto-propagate all F(FA) formulas to freshTime
        let fNegProps := branch.someFutureNegFormulas.filterMap fun fsf =>
          match fsf.formula with
          | .someFuture inner =>
            if fsf.label.time == l.time then
              let prop := SignedFormula.neg inner { world := fsf.label.world, time := freshTime }
              if branch.contains prop then none else some prop
            else none
          | _ => none
        -- Auto-propagate all F(U(event', guard')) formulas to freshTime
        let untlNegProps := branch.untlNegFormulas.filterMap fun usf =>
          if usf.label.time == l.time then
            let prop := SignedFormula.neg usf.formula { world := usf.label.world, time := freshTime }
            if branch.contains prop then none else some prop
          else none
        -- Cross-modal-temporal: propagate T(box A) and F(diamond A) to fresh future time
        let modalProps := boxDiamondPersistence branch l.world l.time freshTime
        let autoProp := gProps ++ fNegProps ++ untlNegProps ++ modalProps
        (.branching [branch1 ++ autoProp, branch2 ++ autoProp], newOrd)
      | none => (.notApplicable, timeOrd)
  -- T(S(event, guard)) @ (w,t) -> branch: event-witness at fresh past time OR guard+continue
  -- Consumable: removed after application. Creates fresh time t' < t.
  -- Branch 1 (event witness): T(event) @ (w, t')
  -- Branch 2 (guard + continue): T(guard) @ (w, t'), T(S(event, guard)) @ (w, t')
  | .sncePos, .pos, φ =>
      match asSince? φ with
      | some (event, guard) =>
        let freshTime := branch.nextTime
        let freshLabel : Label := { world := l.world, time := freshTime }
        let newOrd := timeOrd.addPast l.time freshTime
        -- Branch 1: event witness at fresh past time
        let branch1 := [SignedFormula.pos event freshLabel]
        -- Branch 2: guard holds at fresh time + Since continues from fresh time
        let branch2 := [SignedFormula.pos guard freshLabel,
                         SignedFormula.pos (.snce event guard) freshLabel]
        -- Auto-propagate all T(HA) formulas to freshTime
        let hProps := branch.allPastPosFormulas.filterMap fun hsf =>
          match hsf.formula with
          | .allPast inner =>
            if hsf.label.time == l.time then
              let prop := SignedFormula.pos inner { world := hsf.label.world, time := freshTime }
              if branch.contains prop then none else some prop
            else none
          | _ => none
        -- Auto-propagate all F(PA) formulas to freshTime
        let pNegProps := branch.somePastNegFormulas.filterMap fun psf =>
          match psf.formula with
          | .somePast inner =>
            if psf.label.time == l.time then
              let prop := SignedFormula.neg inner { world := psf.label.world, time := freshTime }
              if branch.contains prop then none else some prop
            else none
          | _ => none
        -- Auto-propagate all F(S(event', guard')) formulas to freshTime
        let snceNegProps := branch.snceNegFormulas.filterMap fun ssf =>
          if ssf.label.time == l.time then
            let prop := SignedFormula.neg ssf.formula { world := ssf.label.world, time := freshTime }
            if branch.contains prop then none else some prop
          else none
        -- Cross-modal-temporal: propagate T(box A) and F(diamond A) to fresh past time
        let modalProps := boxDiamondPersistence branch l.world l.time freshTime
        let autoProp := hProps ++ pNegProps ++ snceNegProps ++ modalProps
        (.branching [branch1 ++ autoProp, branch2 ++ autoProp], newOrd)
      | none => (.notApplicable, timeOrd)
  -- F(U(event, guard)) @ (w,t) -> Reynolds co-decomposition at future times
  -- Persistent: source formula re-included in both branches.
  | .untlNeg, .neg, φ =>
      match asUntil? φ with
      | some (event, guard) =>
        let futureTimes := timeOrd.futureOf l.time
        -- Find first unprocessed future time (where decomposition hasn't been done yet)
        let unprocessed := futureTimes.filter fun t' =>
          let negEvent := SignedFormula.neg event { world := l.world, time := t' }
          let negGuard := SignedFormula.neg guard { world := l.world, time := t' }
          !branch.contains negEvent && !branch.contains negGuard
        match unprocessed with
        | [] =>
          if futureTimes.isEmpty && timeOrd.timeCount > 0 && timeOrd.timeCount < 4 then
            -- ACTIVE: no future times exist at all -- create fresh future time
            let freshTime := branch.nextTime
            let freshLabel : Label := { world := l.world, time := freshTime }
            let newOrd := timeOrd.addFuture l.time freshTime
            -- Auto-propagate T(GA) formulas from time t to freshTime
            let gProps := branch.allFuturePosFormulas.filterMap fun gsf =>
              match gsf.formula with
              | .allFuture inner =>
                if gsf.label.time == l.time then
                  let prop := SignedFormula.pos inner { world := gsf.label.world, time := freshTime }
                  if branch.contains prop then none else some prop
                else none
              | _ => none
            -- Auto-propagate F(FA) formulas from time t to freshTime
            let fNegProps := branch.someFutureNegFormulas.filterMap fun fsf =>
              match fsf.formula with
              | .someFuture inner =>
                if fsf.label.time == l.time then
                  let prop := SignedFormula.neg inner { world := fsf.label.world, time := freshTime }
                  if branch.contains prop then none else some prop
                else none
              | _ => none
            -- Auto-propagate OTHER F(U(event', guard')) formulas to freshTime
            let untlNegProps := branch.untlNegFormulas.filterMap fun usf =>
              if usf.label.time == l.time && usf != sf then
                let prop := SignedFormula.neg usf.formula { world := usf.label.world, time := freshTime }
                if branch.contains prop then none else some prop
              else none
            -- Cross-modal-temporal: propagate T(box A) and F(diamond A) to fresh future time
            let modalProps := boxDiamondPersistence branch l.world l.time freshTime
            let autoProp := gProps ++ fNegProps ++ untlNegProps ++ modalProps
            -- Reynolds co-decomposition at the fresh time
            let branch1 := [SignedFormula.neg event freshLabel, sf] ++ autoProp
            let branch2 := [SignedFormula.neg guard freshLabel,
                             SignedFormula.neg (.untl event guard) freshLabel, sf] ++ autoProp
            (.branching [branch1, branch2], newOrd)
          else
            -- All existing future times processed, or depth limit reached
            (.notApplicable, timeOrd)
        | t' :: _ =>
          let targetLabel : Label := { world := l.world, time := t' }
          -- Branch 1: event fails at t', source formula re-included for persistence
          let branch1 := [SignedFormula.neg event targetLabel, sf]
          -- Branch 2: guard fails at t' AND Until propagated to t', source re-included
          let branch2 := [SignedFormula.neg guard targetLabel,
                           SignedFormula.neg (.untl event guard) targetLabel, sf]
          (.branching [branch1, branch2], timeOrd)
      | none => (.notApplicable, timeOrd)
  -- F(S(event, guard)) @ (w,t) -> Reynolds co-decomposition at past times
  -- Persistent: source formula re-included in both branches.
  | .snceNeg, .neg, φ =>
      match asSince? φ with
      | some (event, guard) =>
        let pastTimes := timeOrd.pastOf l.time
        -- Find first unprocessed past time
        let unprocessed := pastTimes.filter fun t' =>
          let negEvent := SignedFormula.neg event { world := l.world, time := t' }
          let negGuard := SignedFormula.neg guard { world := l.world, time := t' }
          !branch.contains negEvent && !branch.contains negGuard
        match unprocessed with
        | [] =>
          if pastTimes.isEmpty && timeOrd.timeCount > 0 && timeOrd.timeCount < 4 then
            -- ACTIVE: no past times exist at all -- create fresh past time
            let freshTime := branch.nextTime
            let freshLabel : Label := { world := l.world, time := freshTime }
            let newOrd := timeOrd.addPast l.time freshTime
            -- Auto-propagate T(HA) formulas from time t to freshTime
            let hProps := branch.allPastPosFormulas.filterMap fun hsf =>
              match hsf.formula with
              | .allPast inner =>
                if hsf.label.time == l.time then
                  let prop := SignedFormula.pos inner { world := hsf.label.world, time := freshTime }
                  if branch.contains prop then none else some prop
                else none
              | _ => none
            -- Auto-propagate F(PA) formulas from time t to freshTime
            let pNegProps := branch.somePastNegFormulas.filterMap fun psf =>
              match psf.formula with
              | .somePast inner =>
                if psf.label.time == l.time then
                  let prop := SignedFormula.neg inner { world := psf.label.world, time := freshTime }
                  if branch.contains prop then none else some prop
                else none
              | _ => none
            -- Auto-propagate OTHER F(S(event', guard')) formulas to freshTime
            let snceNegProps := branch.snceNegFormulas.filterMap fun ssf =>
              if ssf.label.time == l.time && ssf != sf then
                let prop := SignedFormula.neg ssf.formula { world := ssf.label.world, time := freshTime }
                if branch.contains prop then none else some prop
              else none
            -- Cross-modal-temporal: propagate T(box A) and F(diamond A) to fresh past time
            let modalProps := boxDiamondPersistence branch l.world l.time freshTime
            let autoProp := hProps ++ pNegProps ++ snceNegProps ++ modalProps
            -- Reynolds co-decomposition at the fresh time
            let branch1 := [SignedFormula.neg event freshLabel, sf] ++ autoProp
            let branch2 := [SignedFormula.neg guard freshLabel,
                             SignedFormula.neg (.snce event guard) freshLabel, sf] ++ autoProp
            (.branching [branch1, branch2], newOrd)
          else
            -- All existing past times processed, or depth limit reached
            (.notApplicable, timeOrd)
        | t' :: _ =>
          let targetLabel : Label := { world := l.world, time := t' }
          -- Branch 1: event fails at t', source formula re-included for persistence
          let branch1 := [SignedFormula.neg event targetLabel, sf]
          -- Branch 2: guard fails at t' AND Since propagated to t', source re-included
          let branch2 := [SignedFormula.neg guard targetLabel,
                           SignedFormula.neg (.snce event guard) targetLabel, sf]
          (.branching [branch1, branch2], timeOrd)
      | none => (.notApplicable, timeOrd)
  -- Dense: T(U(top,bot)) closes the branch on dense frames
  | .denseIndicatorClosure, .pos, .untl (.imp .bot .bot) .bot =>
      -- Close branch: T(U(top, bot)) contradicts density
      (.linear [], timeOrd)
  -- Dense: T(G(phi)) at (w,t) with known future time -> introduce intermediate point
  | .densityRule, .pos, .allFuture ψ =>
      let futureTimes := timeOrd.futureOf l.time
      match futureTimes with
      | [] => (.notApplicable, timeOrd)
      | t' :: _ =>
        -- Check if we already have an intermediate time between l.time and t'
        let existingIntermediates := timeOrd.futureOf l.time |>.filter fun t'' =>
          timeOrd.futureOf t'' |>.any (· == t')
        if existingIntermediates.isEmpty then
          let freshTime := branch.nextTime
          let freshLabel : Label := { world := l.world, time := freshTime }
          -- Add t < freshTime < t' to the ordering
          let newOrd := (timeOrd.addFuture l.time freshTime).addFuture freshTime t'
          -- The intermediate point gets T(psi) from G(psi) at l.time
          let witness := SignedFormula.pos ψ freshLabel
          -- Also propagate all T(G(A)) from l.time to the intermediate
          let gProps := branch.allFuturePosFormulas.filterMap fun gsf =>
            match gsf.formula with
            | .allFuture inner =>
              if gsf.label.time == l.time && gsf.formula != .allFuture ψ then
                let prop := SignedFormula.pos inner { world := gsf.label.world, time := freshTime }
                if branch.contains prop then none else some prop
              else none
            | _ => none
          (.persistent (witness :: gProps), newOrd)
        else
          (.notApplicable, timeOrd)
  -- Discrete: T(F(phi)) -> T(U(phi, neg phi))
  | .priorUZ, .pos, φ =>
      match asSomeFuture? φ with
      | some ψ =>
        let untilFormula := Formula.untl ψ ψ.neg
        let newSf := SignedFormula.pos untilFormula l
        if branch.contains newSf then (.notApplicable, timeOrd)
        else (.persistent [newSf], timeOrd)
      | none => (.notApplicable, timeOrd)
  -- Discrete: T(P(phi)) -> T(S(phi, neg phi))
  | .priorSZ, .pos, φ =>
      match asSomePast? φ with
      | some ψ =>
        let sinceFormula := Formula.snce ψ ψ.neg
        let newSf := SignedFormula.pos sinceFormula l
        if branch.contains newSf then (.notApplicable, timeOrd)
        else (.persistent [newSf], timeOrd)
      | none => (.notApplicable, timeOrd)
  -- Discrete: Z1 backward induction
  -- When T(G(G(phi) -> phi)) and T(F(G(phi))) both at same label, add T(G(phi))
  | .z1Rule, .pos, .allFuture φ_inner =>
      -- Check if sf matches T(G(G(phi) -> phi)) pattern
      match φ_inner with
      | .imp (.imp (.untl (.imp inner .bot) (.imp .bot .bot)) .bot) rhs =>
        -- This is G(G(inner) -> rhs) -- verify rhs = inner
        if inner == rhs then
          -- Look for T(F(G(inner))) on the branch at the same label
          let gInner := Formula.allFuture inner
          let fgFormula := Formula.someFuture gInner
          let fgSf := SignedFormula.pos fgFormula l
          if branch.contains fgSf then
            let newSf := SignedFormula.pos gInner l
            if branch.contains newSf then (.notApplicable, timeOrd)
            else (.persistent [newSf], timeOrd)
          else (.notApplicable, timeOrd)
        else (.notApplicable, timeOrd)
      | _ => (.notApplicable, timeOrd)
  | _, _, _ => (.notApplicable, timeOrd)

/--
`RuleResult.branching` is never equal to `RuleResult.notApplicable`.
-/
@[simp] theorem RuleResult.branching_ne_notApplicable
    (bs : List (List (SignedFormula Atom))) :
    RuleResult.branching bs ≠ (RuleResult.notApplicable : RuleResult Atom) := by
  exact nofun

/--
`RuleResult.linear` is never equal to `RuleResult.notApplicable`.
-/
@[simp] theorem RuleResult.linear_ne_notApplicable
    (fs : List (SignedFormula Atom)) :
    RuleResult.linear fs ≠ (RuleResult.notApplicable : RuleResult Atom) := by
  exact nofun

/--
`RuleResult.persistent` is never equal to `RuleResult.notApplicable`.
-/
@[simp] theorem RuleResult.persistent_ne_notApplicable
    (fs : List (SignedFormula Atom)) :
    RuleResult.persistent fs ≠ (RuleResult.notApplicable : RuleResult Atom) := by
  exact nofun

/-!
## Applied-Set Tracking

Persistent rules (boxPos, diamondNeg, allFuturePos, allPastPos, boxTemporal,
someFutureNeg, somePastNeg, untlNeg, snceNeg) keep their source formula on the
branch and propagate consequences. If a consumable rule later removes a propagated
formula, the persistent rule sees it as "new" and re-adds it, creating an infinite
loop. The `AppliedSet` tracks signed formulas that have already been produced by
persistent rules. When a persistent rule's output formulas are ALL already in the
applied set, the rule is treated as not applicable.
-/

/-- Set of signed formulas already produced by persistent rule applications.
    Used to prevent infinite cycling between persistent and consumable rules. -/
abbrev AppliedSet (Atom : Type*) [DecidableEq Atom] [Hashable Atom] :=
  Std.HashSet (SignedFormula Atom)

/-!
## Branch Expansion
-/

/--
All base tableau rules in priority order (frame-class independent).
Propositional rules are tried first, then modal, then temporal.
-/
def allRules : List TableauRule := [
  .negPos, .negNeg,      -- Negation (simplest)
  .impNeg,               -- F(A -> B) non-branching
  .andPos, .orNeg,       -- Non-branching compound
  .boxPos, .boxNeg,      -- Modal
  .diamondPos, .diamondNeg,
  .boxTemporal,                    -- Modal-temporal interaction (before temporal rules)
  .allFuturePos, .allFutureNeg,  -- Temporal G/H
  .allPastPos, .allPastNeg,
  .someFuturePos, .someFutureNeg,  -- Temporal F/P
  .somePastPos, .somePastNeg,
  .untlPos, .untlNeg,             -- Until (genuine, not someFuture)
  .sncePos, .snceNeg,             -- Since (genuine, not somePast)
  .impPos,               -- Branching implication
  .andNeg, .orPos        -- Branching compound
]

/--
Dense-specific rules, included only when fc >= .Dense.
-/
def denseRules : List TableauRule := [
  .denseIndicatorClosure,
  .densityRule
]

/--
Discrete-specific rules, included only when fc >= .Discrete.
-/
def discreteRules : List TableauRule := [
  .priorUZ, .priorSZ,
  .z1Rule
]

/--
All tableau rules for a given frame class, in priority order.
Base rules are always included; Dense/Discrete rules are appended
when the frame class supports them.
-/
def allRulesForFC (fc : FrameClass := .Base) : List TableauRule :=
  let base := allRules
  let dense := if decide (FrameClass.Dense ≤ fc) then denseRules else []
  let discrete := if decide (FrameClass.Discrete ≤ fc) then discreteRules else []
  base ++ dense ++ discrete

/--
Find a rule that applies to a signed formula.
Returns the first applicable rule, its result, and the updated TimeOrdering.
-/
def findApplicableRule (sf : SignedFormula Atom) (branch : Branch Atom := [])
    (timeOrd : TimeOrdering := TimeOrdering.empty)
    (fc : FrameClass := .Base) :
    Option (TableauRule × RuleResult Atom × TimeOrdering) :=
  (allRulesForFC fc).findSome? fun rule =>
    if isApplicable rule sf fc then
      let (result, newOrd) := applyRule rule sf branch timeOrd
      match result with
      | .notApplicable => none
      | _ => some (rule, result, newOrd)
    else none

/--
Check if a signed formula is fully expanded (no rules apply).
Atoms, bot with appropriate signs, and already-reduced formulas are expanded.
-/
def isExpanded (sf : SignedFormula Atom) (branch : Branch Atom := [])
    (timeOrd : TimeOrdering := TimeOrdering.empty)
    (fc : FrameClass := .Base) : Bool :=
  (findApplicableRule sf branch timeOrd fc).isNone

/--
Find an unexpanded formula in a branch.
Returns the first formula that can still be expanded.
-/
def findUnexpanded (b : Branch Atom) (timeOrd : TimeOrdering := TimeOrdering.empty)
    (fc : FrameClass := .Base) : Option (SignedFormula Atom) :=
  b.find? (fun sf => ¬isExpanded sf b timeOrd fc)

/--
Result of a single expansion step on a branch.
-/
inductive ExpansionResult (Atom : Type*) [DecidableEq Atom] [Hashable Atom] : Type _ where
  /-- Branch is fully saturated (no more expansions possible). -/
  | saturated
  /-- Single branch extension (non-branching rule applied). -/
  | extended (newBranch : Branch Atom)
  /-- Branch splits into multiple branches (branching rule applied). -/
  | split (branches : List (Branch Atom))

/--
Perform a single expansion step on a branch.

Finds the first unexpanded formula and applies the appropriate rule.
Returns the result of the expansion together with the (possibly updated) TimeOrdering.
-/
def expandOnce (b : Branch Atom) (timeOrd : TimeOrdering := TimeOrdering.empty)
    (fc : FrameClass := .Base) : ExpansionResult Atom × TimeOrdering :=
  match findUnexpanded b timeOrd fc with
  | none => (.saturated, timeOrd)
  | some sf =>
      match findApplicableRule sf b timeOrd fc with
      | none => (.saturated, timeOrd)  -- Shouldn't happen if findUnexpanded returned something
      | some (_, result, newOrd) =>
          match result with
          | .linear formulas =>
              -- Remove the expanded formula and add new ones
              let remaining := b.filter (· != sf)
              (.extended (formulas ++ remaining), newOrd)
          | .branching branches =>
              -- Remove the expanded formula from each branch and add new formulas
              let remaining := b.filter (· != sf)
              (.split (branches.map fun newFormulas => newFormulas ++ remaining), newOrd)
          | .persistent formulas =>
              -- Add new formulas but keep the source formula (universal modal rule)
              (.extended (formulas ++ b), newOrd)
          | .notApplicable => (.saturated, newOrd)  -- Shouldn't happen

/--
Find a rule applicable to a signed formula, filtering persistent rules whose
output has already been fully produced (tracked in the applied set).
-/
def findApplicableRuleWithApplied (sf : SignedFormula Atom) (branch : Branch Atom := [])
    (timeOrd : TimeOrdering := TimeOrdering.empty)
    (fc : FrameClass := .Base)
    (applied : AppliedSet Atom := {}) :
    Option (TableauRule × RuleResult Atom × TimeOrdering × List (SignedFormula Atom)) :=
  (allRulesForFC fc).findSome? fun rule =>
    if isApplicable rule sf fc then
      let (result, newOrd) := applyRule rule sf branch timeOrd
      match result with
      | .notApplicable => none
      | .persistent formulas =>
          -- Filter out formulas already in the applied set
          let newFormulas := formulas.filter fun f => !applied.contains f
          if newFormulas.isEmpty then
            none  -- All outputs already produced; skip this rule
          else
            some (rule, .persistent newFormulas, newOrd, newFormulas)
      | _ => some (rule, result, newOrd, [])
    else none

/-- Check if a signed formula is fully expanded, considering the applied set. -/
def isExpandedWithApplied (sf : SignedFormula Atom) (branch : Branch Atom := [])
    (timeOrd : TimeOrdering := TimeOrdering.empty)
    (fc : FrameClass := .Base)
    (applied : AppliedSet Atom := {}) : Bool :=
  (findApplicableRuleWithApplied sf branch timeOrd fc applied).isNone

/-- Find an unexpanded formula in a branch, considering the applied set. -/
def findUnexpandedWithApplied (b : Branch Atom) (timeOrd : TimeOrdering := TimeOrdering.empty)
    (fc : FrameClass := .Base)
    (applied : AppliedSet Atom := {}) : Option (SignedFormula Atom) :=
  b.find? (fun sf => ¬isExpandedWithApplied sf b timeOrd fc applied)

/--
Perform a single expansion step on a branch, using the applied set to prevent
persistent rule loops. Returns `(result, newTimeOrdering, formulasToAddToAppliedSet)`.
-/
def expandOnceWithApplied (b : Branch Atom) (timeOrd : TimeOrdering := TimeOrdering.empty)
    (fc : FrameClass := .Base) (applied : AppliedSet Atom := {})
    : ExpansionResult Atom × TimeOrdering × List (SignedFormula Atom) :=
  match findUnexpandedWithApplied b timeOrd fc applied with
  | none => (.saturated, timeOrd, [])
  | some sf =>
      match findApplicableRuleWithApplied sf b timeOrd fc applied with
      | none => (.saturated, timeOrd, [])
      | some (_, result, newOrd, newApplied) =>
          match result with
          | .linear formulas =>
              let remaining := b.filter (· != sf)
              (.extended (formulas ++ remaining), newOrd, [])
          | .branching branches =>
              let remaining := b.filter (· != sf)
              (.split (branches.map fun newFormulas => newFormulas ++ remaining), newOrd, [])
          | .persistent formulas =>
              (.extended (formulas ++ b), newOrd, newApplied)
          | .notApplicable => (.saturated, newOrd, [])

/--
Count of unexpanded formulas in a branch (termination measure).
-/
def countUnexpanded (b : Branch Atom) (timeOrd : TimeOrdering := TimeOrdering.empty)
    (fc : FrameClass := .Base) : Nat :=
  b.filter (fun sf => ¬isExpanded sf b timeOrd fc) |>.length

/--
Total unexpanded complexity (alternative termination measure).
-/
def totalUnexpandedComplexity (b : Branch Atom) (timeOrd : TimeOrdering := TimeOrdering.empty)
    (fc : FrameClass := .Base) : Nat :=
  b.filter (fun sf => ¬isExpanded sf b timeOrd fc)
  |>.foldl (fun acc sf => acc + sf.complexity) 0

end Cslib.Logic.Bimodal.Metalogic.Decidability
