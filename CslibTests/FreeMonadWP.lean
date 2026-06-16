/-
Copyright (c) 2025 Tanner Duve (Logical Intelligence). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

import Cslib.Foundations.Control.Monad.Free.Effects
import Std.Tactic.Do

/-!
Examples for WP in `Cslib.Foundations.Control.Monad.Free.WP`: instance resolution,
a `Triple` on a `FreeState` program discharged by `mvcgen`, and a custom `CounterF` effect with
its own logical handler.
-/

set_option mvcgen.warning false

namespace CslibTests.FreeMonadWP

open Cslib Cslib.FreeM Std.Do

example : Std.Do.WP (FreeState Nat) (.arg Nat .pure) := inferInstance
example : WPMonad (FreeState Nat) (.arg Nat .pure) := inferInstance
example : Std.Do.WP (FreeReader Nat) (.arg Nat .pure) := inferInstance
example : FreeM.WP (StateF Nat) (.arg Nat .pure) := inferInstance

/-- Increment the natural-number state by 1. -/
def incr : FreeState Nat Unit := do
  let n ← MonadStateOf.get
  MonadStateOf.set (n + 1)

example : wp incr = wp (FreeState.toStateM incr) :=
  StateF.wp_freeState_eq_wp_toStateM incr

/-- Starting in state `n`, `incr` ends in state `n + 1`. `mvcgen` picks up the `@[spec]` lemmas
for `MonadStateOf.get`/`set` on `FreeState` and discharges the resulting arithmetic VC. -/
example (n : Nat) :
    ⦃fun s => ⌜s = n⌝⦄ (incr : FreeState Nat Unit) ⦃⇓ _ s' => ⌜s' = n + 1⌝⦄ := by
  mvcgen
  intro s heq
  subst heq
  rfl

/-- A counter effect with two operations. -/
inductive CounterF : Type → Type where
  /-- Increment the counter by one. -/
  | tick : CounterF Unit
  /-- Read the counter's value. -/
  | read : CounterF Nat

/-- Counter programs built from `CounterF`. -/
abbrev FreeCounter := FreeM CounterF

namespace CounterF

/-- Effect handler for `CounterF` into `StateM Nat`, used to seed both the executable
semantics and the logical handler. -/
def interp : ∀ ι : Type, CounterF ι → StateM Nat ι
  | _, .tick => modify (· + 1)
  | _, .read => MonadStateOf.get

instance : FreeM.WP CounterF (.arg Nat .pure) where
  handler := fun {ι} op => wp (CounterF.interp ι op)

/-- Interpret counter programs as `StateM Nat` programs. -/
abbrev toStateM {α : Type} (comp : FreeCounter α) : StateM Nat α :=
  comp.liftM (fun {ι} => CounterF.interp ι)

/-- Adequacy theorem specialized to `CounterF`. -/
theorem wp_FreeCounter_eq_wp_toStateM {α : Type} (comp : FreeCounter α) :
    wp comp = wp (CounterF.toStateM comp) :=
  liftM_wp_eq_wp_liftM (m := StateM Nat) CounterF.interp comp

end CounterF

/-- Smart constructor: tick the counter as a `FreeCounter` action. -/
abbrev tick : FreeCounter Unit := lift CounterF.tick

/-- Smart constructor: read the counter as a `FreeCounter` action. -/
abbrev readCounter : FreeCounter Nat := lift CounterF.read

/-- Tick three times, then read out the counter. -/
def threeTicks : FreeCounter Nat := do
  tick; tick; tick
  readCounter

/--
Triple about the counter program: starting at `0`, the final value is `3` and the final state
is `3`. Proven by the same bridge-then-`mvcgen` pattern as `incr`.
-/
example :
    ⦃fun s => ⌜s = 0⌝⦄ threeTicks ⦃⇓ v s => ⌜v = 3 ∧ s = 3⌝⦄ := by
  mvcgen
  intro s seq0
  subst seq0
  exact ⟨rfl, rfl⟩

/-- A failure effect with one operation `fail` of empty answer type. -/
inductive FailF : Type → Type where
  /-- Abort the computation. -/
  | fail : FailF PEmpty.{1}

/-- Logical handler for `FailF`: `fail` has precondition `⌜False⌝`, so it is only provable in
unreachable branches. -/
def FailF.handler {ps : PostShape} : {ι : Type} → FailF ι → PredTrans ps ι :=
  fun
    | .fail => PredTrans.const spred(⌜False⌝)

/-- A combined state + failure signature, sequencing `StateF Nat` with `FailF`. -/
abbrev StateFail := fun α => StateF Nat α ⊕ FailF α

/-- Handler for the combined signature: the sum of the component handlers — the paper's
`H₁ ⊕ H₂` composition. -/
instance : FreeM.WP StateFail (.arg Nat .pure) where
  handler := fun op => Sum.elim FreeM.WP.handler FailF.handler op

/-- Smart constructor for state-read in the combined signature. -/
abbrev sfGet : FreeM StateFail Nat := lift (Sum.inl StateF.get)

/-- Smart constructor for state-write in the combined signature. -/
abbrev sfSet (n : Nat) : FreeM StateFail PUnit := lift (Sum.inl (StateF.set n))

/-- Smart constructor for failure in the combined signature, eliminated to any return type via
`PEmpty.elim`. -/
abbrev sfFail {α : Type} : FreeM StateFail α :=
  lift (Sum.inr FailF.fail) >>= PEmpty.elim

/-- Hoare spec for the sum-lifted state-read. -/
@[spec]
theorem Spec.sfGet {Q : PostCond Nat (.arg Nat .pure)} :
    Triple sfGet (spred(fun s => Q.1 s s)) Q := by
  mvcgen

/-- Hoare spec for the sum-lifted state-write. -/
@[spec]
theorem Spec.sfSet (n : Nat) {Q : PostCond PUnit (.arg Nat .pure)} :
    Triple (sfSet n) (spred(fun _ => Q.1 ⟨⟩ n)) Q := by
  mvcgen

/-- Hoare spec for sum-lifted failure: requires `False` to verify. -/
@[spec]
theorem Spec.sfFail {α : Type} {Q : PostCond α (.arg Nat .pure)} :
    Triple (sfFail : FreeM StateFail α) (spred(⌜False⌝)) Q := by
  mvcgen

/-- A non-branching program in the combined signature: read the state, then write
`state + 1`. Shows that the sum handler composes the StateF and FailF specs cleanly. -/
def getAndBump : FreeM StateFail Unit := do
  let n ← sfGet
  sfSet (n + 1)

/-- `getAndBump` advances the state by 1, proven through the sum handler. -/
example (n : Nat) :
    ⦃fun s => ⌜s = n⌝⦄ (getAndBump : FreeM StateFail Unit)
      ⦃⇓ _ s => ⌜s = n + 1⌝⦄ := by
  mvcgen
  intro s a
  subst a
  rfl

/-- Increment the state if it's strictly below `limit`, otherwise fail. Branches on the state's
value and uses `sfFail` in the else branch. -/
def bumpUnder (limit : Nat) : FreeM StateFail Unit := do
  let n ← sfGet
  if n < limit then sfSet (n + 1) else sfFail

/-- Starting in a state below `limit`, `bumpUnder` increments without failing — the failure
branch is unreachable because the precondition rules it out. -/
example (limit n : Nat) (hlt : n < limit) :
    ⦃fun s => ⌜s = n⌝⦄ (bumpUnder limit : FreeM StateFail Unit)
      ⦃⇓ _ s => ⌜s = n + 1⌝⦄ := by
  unfold bumpUnder
  mvcgen <;> aesop

/-- Demonic non-determinism: a single operation `choice α` that abstractly returns an arbitrary
`a : α`. Verification must consider all possible values of `a`. -/
inductive DemonicF : Type → Type 1 where
  /-- Choose an element of `α`. -/
  | choice (α : Type) : DemonicF α

/-- Logical handler for `DemonicF`: the predicate transformer for `choice α` is universal
quantification over `α`. Conjunctivity of `∀` (i.e. `∀ a, P a ∧ Q a ⊣⊢ (∀ a, P a) ∧ (∀ a, Q a)`)
is what makes this admissible in `PredTrans`. -/
def DemonicF.handler {ps : PostShape} : {ι : Type} → DemonicF ι → PredTrans ps ι
  | _, .choice _ =>
    { trans := fun Q => SPred.forall (fun a => Q.1 a)
      conjunctiveRaw := by
        intro Q₁ Q₂
        apply SPred.bientails.iff.mpr
        refine ⟨?_, ?_⟩
        · apply SPred.and_intro
          · apply SPred.forall_intro
            intro a
            exact (SPred.forall_elim a).trans SPred.and_elim_l
          · apply SPred.forall_intro
            intro a
            exact (SPred.forall_elim a).trans SPred.and_elim_r
        · apply SPred.forall_intro
          intro a
          apply SPred.and_intro
          · exact SPred.and_elim_l.trans (SPred.forall_elim a)
          · exact SPred.and_elim_r.trans (SPred.forall_elim a) }

instance : FreeM.WP DemonicF .pure where
  handler := DemonicF.handler

/-- Smart constructor for demonic choice over `α`. -/
abbrev demonic (α : Type) : FreeM DemonicF α := lift (DemonicF.choice α)

/-- Triple for `demonic α`: the precondition must imply the postcondition for *every* `a : α`. -/
@[spec]
theorem Spec.demonic {α : Type} {Q : PostCond α .pure} :
    Triple (demonic α) (SPred.forall (fun a : α => Q.1 a)) Q :=
  Triple.iff.mpr SPred.entails.rfl

/-- A demonic Bool: the precondition must hold for both `true` and `false`. -/
example {Q : PostCond Bool .pure} :
    Triple (demonic Bool) (SPred.and (Q.1 true) (Q.1 false)) Q :=
    fun ⟨ht, hf⟩ b =>
    match b with
    | true => ht
    | false => hf

end CslibTests.FreeMonadWP
