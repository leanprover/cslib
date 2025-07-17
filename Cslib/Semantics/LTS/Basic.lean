/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Mathlib.Tactic.Lemma
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Rel
import Mathlib.Logic.Function.Defs
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Stream.Defs

/-!
# Labelled Transition System

A Labelled Transition System (LTS) models the observable behaviour of the possible states of a
system. They are particularly popular in the fields of concurrency theory, logic, and programming
languages.

## Main definitions

- `LTS` is a structure for labelled transition systems, consisting of a labelled transition
relation `Tr` between states. We follow the style and conventions in [Sangiorgi2011].

- `LTS.MTr` extends the transition relation of any LTS to a multi-step transition relation,
formalising the inference system and admissible rules for such relations in [Montesi2023].

- Definitions for all the common classes of LTSs: image-finite, finitely branching, finite-state,
finite, and deterministic.

## Main statements

- A series of results on `LTS.MTr` that allow for obtaining and composing multi-step transitions in
different ways.

- `LTS.deterministic_imageFinite`: every deterministic LTS is also image-finite.

- `LTS.finiteState_imageFinite`: every finite-state LTS is also image-finite.

- `LTS.finiteState_finitelyBranching`: every finite-state LTS is also finitely-branching, if the
type of labels is finite.

## References

* [F. Montesi, *Introduction to Choreographies*] [Montesi2023]
* [D. Sangiorgi, *Introduction to Bisimulation and Coinduction*] [Sangiorgi2011]
-/

universe u v

/--
A Labelled Transition System (LTS) consists of a type of states (`State`), a type of transition
labels (`Label`), and a labelled transition relation (`Tr`).
-/
structure LTS (State : Type u) (Label : Type v) where
  /-- The transition relation. -/
  Tr : State → Label → State → Prop

section Relation

/-- Given an `lts` and a transition label `μ`, returns the relation that relates all states `s1`
and `s2` such that `lts.Tr s1 μ s2`.

This can be useful, for example, to see a reduction relation as an LTS. -/
def LTS.toRel (lts : LTS State Label) (μ : Label) : Rel State State :=
  fun s1 s2 => lts.Tr s1 μ s2

/-- Any homogeneous relation can be seen as an LTS where all transitions have the same label. -/
def Rel.toLTS [DecidableEq Label] (r : Rel State State) (μ : Label) : LTS State Label where
  Tr := fun s1 μ' s2 => if μ' = μ then r s1 s2 else False

end Relation

section MultiStep

/-! ## Multi-step transitions -/

variable {State : Type u} {Label : Type v} (lts : LTS State Label)

/--
Definition of a multi-step transition.

(Implementation note: compared to [Montesi2023], we choose stepL instead of stepR as fundamental
rule. This makes working with lists of labels more convenient, because we follow the same
construction. It is also similar to what is done in the `SimpleGraph` library in mathlib.)
-/
inductive LTS.MTr (lts : LTS State Label) : State → List Label → State → Prop where
  | refl {s : State} : lts.MTr s [] s
  | stepL {s1 : State} {μ : Label} {s2 : State} {μs : List Label} {s3 : State} :
    lts.Tr s1 μ s2 → lts.MTr s2 μs s3 →
    lts.MTr s1 (μ :: μs) s3

/-- Any transition is also a multi-step transition. -/
theorem LTS.MTr.single {s1 : State} {μ : Label} {s2 : State} :
  lts.Tr s1 μ s2 → lts.MTr s1 [μ] s2 := by
  intro h
  apply LTS.MTr.stepL
  · exact h
  · apply LTS.MTr.refl

/-- Any multi-step transition can be extended by adding a transition. -/
theorem LTS.MTr.stepR {s1 : State} {μs : List Label} {s2 : State} {μ : Label} {s3 : State} :
  lts.MTr s1 μs s2 → lts.Tr s2 μ s3 → lts.MTr s1 (μs ++ [μ]) s3 := by
  intro h1 h2
  induction h1
  case refl s1' =>
    simp
    apply LTS.MTr.single lts h2
  case stepL s1' μ' s2' μs' s3' h1' h3 ih =>
    apply LTS.MTr.stepL
    · exact h1'
    · apply ih h2

/-- Multi-step transitions can be composed. -/
theorem LTS.MTr.comp {s1 : State} {μs1 : List Label} {s2 : State} {μs2 : List Label} {s3 : State} :
  lts.MTr s1 μs1 s2 → lts.MTr s2 μs2 s3 →
  lts.MTr s1 (μs1 ++ μs2) s3 := by
  intro h1 h2
  induction h1
  case refl =>
    simp
    assumption
  case stepL s1 μ s' μs1' s'' h1' h3 ih  =>
    apply LTS.MTr.stepL
    · exact h1'
    · apply ih h2

/-- Any 1-sized multi-step transition implies a transition with the same states and label. -/
theorem LTS.MTr.single_invert (s1 : State) (μ : Label) (s2 : State) :
  lts.MTr s1 [μ] s2 → lts.Tr s1 μ s2 := by
  intro h
  cases h
  case stepL s1' htr hmtr =>
    cases hmtr
    exact htr

/-- In any zero-steps multi-step transition, the origin and the derivative are the same. -/
theorem LTS.MTr.nil_eq (h : lts.MTr s1 [] s2) : s1 = s2 := by
  cases h
  rfl

/-- A state `s1` can reach a state `s2` if there exists a multi-step transition from
`s1` to `s2`. -/
def LTS.CanReach (s1 s2 : State) : Prop :=
  ∃ μs, lts.MTr s1 μs s2

/-- Any state can reach itself. -/
theorem LTS.CanReach.refl (s : State) : lts.CanReach s s := by
  exists []
  apply LTS.MTr.refl

/-- The LTS generated by a state `s` is the LTS given by all the states reachable from `s`. -/
def LTS.generatedBy (s : State) : LTS {s' : State // lts.CanReach s s'} Label where
  Tr := fun s1 μ s2 => lts.CanReach s s1 ∧ lts.CanReach s s2 ∧ lts.Tr s1 μ s2

end MultiStep

section Termination
/-! ## Definitions about termination -/

variable {State} {Label} (lts : LTS State Label) {Terminated : State → Prop}

/-- A state 'may terminate' if it can reach a terminated state. The definition of `Terminated`
is a parameter. -/
def LTS.MayTerminate (s : State) : Prop := ∃ s', Terminated s' ∧ lts.CanReach s s'

/-- A state 'is stuck' if it is not terminated and cannot go forward. The definition of `Terminated`
is a parameter. -/
def LTS.Stuck (s : State) : Prop :=
  ¬Terminated s ∧ ¬∃ μ s', lts.Tr s μ s'

end Termination

section Union
/-! ## Definitions for the unions of LTSs

Note: there is a nontrivial balance between ergonomics and generality here. These definitions might
change in the future. -/

variable {State : Type u} {Label : Type v}

/-- The union of two LTSs that have common supertypes for states and labels. -/
def LTS.unionSubtype
{S1 : State → Prop} {L1 : Label → Prop} {S2 : State → Prop} {L2 : Label → Prop}
[DecidablePred S1] [DecidablePred L1] [DecidablePred S2] [DecidablePred L2]
(lts1 : LTS (@Subtype State S1) (@Subtype Label L1))
(lts2 : LTS (@Subtype State S2) (@Subtype Label L2)) :
  LTS State Label where
  Tr := fun s μ s' =>
    if h : S1 s ∧ L1 μ ∧ S1 s' then
      lts1.Tr ⟨s, h.1⟩ ⟨μ, h.2.1⟩ ⟨s', h.2.2⟩
    else if h : S2 s ∧ L2 μ ∧ S2 s' then
      lts2.Tr ⟨s, h.1⟩ ⟨μ, h.2.1⟩ ⟨s', h.2.2⟩
    else
      False

/-- TODO: move this to `Sum`? -/
def Sum.isLeftP {α} {β} (x : α ⊕ β) : Prop := Sum.isLeft x = true

/-- TODO: move this to `Sum`? -/
def Sum.isRightP {α} {β} (x : α ⊕ β) : Prop := Sum.isRight x = true

/-- Lifting of an `LTS State Label` to `LTS (State ⊕ State') Label`. -/
def LTS.inl {State'} (lts : LTS State Label) :
  LTS (@Subtype (State ⊕ State') Sum.isLeftP) (@Subtype Label (Function.const Label True)) where
  Tr := fun s μ s' =>
    let ⟨s, _⟩ := s
    let ⟨s', _⟩ := s'
    match s, μ, s' with
    | Sum.inl s1, μ, Sum.inl s2 => lts.Tr s1 μ s2
    | _, _, _ => False

/-- Lifting of an `LTS State Label` to `LTS (State' ⊕ State) Label`. -/
def LTS.inr {State'} (lts : LTS State Label) :
  LTS (@Subtype (State' ⊕ State) Sum.isRightP) (@Subtype Label (Function.const Label True)) where
  Tr := fun s μ s' =>
    let ⟨s, _⟩ := s
    let ⟨s', _⟩ := s'
    match s, μ, s' with
    | Sum.inr s1, μ, Sum.inr s2 => lts.Tr s1 μ s2
    | _, _, _ => False

/-- Union of two LTSs with the same `Label` type. The result combines the original respective state
types `State1` and `State2` into `(State1 ⊕ State2)`. -/
def LTS.unionSum {State1} {State2} (lts1 : LTS State1 Label) (lts2 : LTS State2 Label) :
  LTS (State1 ⊕ State2) Label :=
  @LTS.unionSubtype
    (State1 ⊕ State2) Label
    Sum.isLeftP
    (Function.const Label True)
    Sum.isRightP
    (Function.const Label True)
    (by
      simp [DecidablePred]
      intro s
      cases h : s
      · apply Decidable.isTrue
        trivial
      · simp [Sum.isLeftP]
        apply Decidable.isFalse
        trivial)
    (by
      intro μ
      simp [Function.const]
      apply Decidable.isTrue
      trivial)
    (by
      simp [DecidablePred]
      intro s
      cases h : s
      · simp [Sum.isRightP]
        apply Decidable.isFalse
        trivial
      · apply Decidable.isTrue
        trivial)
    (by
      intro μ
      simp [Function.const]
      apply Decidable.isTrue
      trivial)
    lts1.inl
    lts2.inr

end Union

section Classes
/-!
### Classes of LTSs
-/

variable {State : Type u} {Label : Type v} (lts : LTS State Label)

/-- An lts is deterministic if a state cannot reach different states with the same transition
label. -/
def LTS.Deterministic : Prop :=
  ∀ (s1 : State) (μ : Label) (s2 s3 : State),
    lts.Tr s1 μ s2 → lts.Tr s1 μ s3 → s2 = s3

/-- The `μ`-image of a state `s` is the set of all `μ`-derivatives of `s`. -/
def LTS.Image (s : State) (μ : Label) : Set State := { s' : State | lts.Tr s μ s' }

/-- An lts is image-finite if all images of its states are finite. -/
def LTS.ImageFinite : Prop :=
  ∀ s μ, Finite (lts.Image s μ)

/-- In a deterministic LTS, if a state has a `μ`-derivative, then it can have no other
`μ`-derivative. -/
theorem LTS.deterministic_not_lto (hDet : lts.Deterministic) :
  ∀ s μ s' s'', s' ≠ s'' → lts.Tr s μ s' → ¬lts.Tr s μ s'' := by
  intro s μ s' s'' hneq hltos'
  by_contra hltos''
  have hDet' := hDet s μ s' s'' hltos' hltos''
  simp only [← hDet'] at hneq
  contradiction

/-- In a deterministic LTS, any image is either a singleton or the empty set. -/
theorem LTS.deterministic_image_char (hDet : lts.Deterministic) :
  ∀ s μ, (∃ s', lts.Image s μ = { s' }) ∨ (lts.Image s μ = ∅) := by
  intro s μ
  by_cases hs' : ∃ s', lts.Tr s μ s'
  case pos =>
    obtain ⟨s', hs'⟩ := hs'
    left
    apply Exists.intro s'
    simp [Image]
    simp [setOf, singleton, Set.singleton]
    funext s''
    by_cases heq : s' = s''
    case pos =>
      simp [heq]
      simp [heq] at hs'
      exact hs'
    case neg =>
      have hDet' := LTS.deterministic_not_lto lts hDet s μ s' s'' heq hs'
      simp [hDet']
      exact Ne.symm heq
  case neg =>
    right
    simp [Image]
    simp [setOf]
    simp [EmptyCollection.emptyCollection]
    funext s''
    by_contra hf
    simp at hf
    simp at hs'
    specialize hs' s''
    contradiction

/-- Every deterministic LTS is also image-finite. -/
theorem LTS.deterministic_imageFinite :
  lts.Deterministic → lts.ImageFinite := by
  simp only [ImageFinite]
  intro h s μ
  have hDet := LTS.deterministic_image_char lts h s μ
  cases hDet
  case inl hDet =>
    obtain ⟨s', hDet'⟩ := hDet
    simp [hDet']
    apply Set.finite_singleton
  case inr hDet =>
    simp [hDet]
    apply Set.finite_empty

/-- A state has an outgoing label `μ` if it has a `μ`-derivative. -/
def LTS.HasOutLabel (s : State) (μ : Label) : Prop :=
  ∃ s', lts.Tr s μ s'

/-- The set of outgoing labels of a state. -/
def LTS.OutgoingLabels (s : State) := { μ | lts.HasOutLabel s μ }

/-- An LTS is finitely branching if it is image-finite and all states have finite sets of
outgoing labels. -/
def LTS.FinitelyBranching : Prop :=
  lts.ImageFinite ∧ ∀ s, Finite (lts.OutgoingLabels s)

/-- An LTS is finite-state if it has a finite `State` type. -/
@[nolint unusedArguments]
def LTS.FiniteState (_ : LTS State Label) : Prop := Finite State

/-- Every finite-state LTS is also image-finite. -/
theorem LTS.finiteState_imageFinite (hFinite : lts.FiniteState) :
  lts.ImageFinite := by
  simp [ImageFinite, Image]
  simp [FiniteState] at hFinite
  intro s μ
  apply @Subtype.finite State hFinite

/-- Every LTS with finite types for states and labels is also finitely branching. -/
theorem LTS.finiteState_finitelyBranching
  (hFiniteLabel : Finite Label) (hFiniteState : lts.FiniteState) :
  lts.FinitelyBranching := by
  simp [FinitelyBranching, OutgoingLabels, HasOutLabel]
  simp [FiniteState] at hFiniteState
  constructor
  case left =>
    apply LTS.finiteState_imageFinite lts hFiniteState
  case right =>
    intro s
    apply @Subtype.finite Label hFiniteLabel

/-- An LTS is acyclic if there are no infinite multi-step transitions. -/
def LTS.Acyclic : Prop :=
  ∃ n, ∀ s1 μs s2, lts.MTr s1 μs s2 → μs.length < n

/-- An LTS is finite if it is finite-state and acyclic. -/
def LTS.Finite : Prop :=
  lts.FiniteState ∧ lts.Acyclic

end Classes

/-! ## Weak transitions (single- and multi-step) -/

section Weak

/-- A type of transition labels that includes a special 'internal' transition `τ`. -/
class HasTau (Label : Type v) where
  τ : Label

/-- Saturated transition relation. -/
inductive LTS.STr [HasTau Label] (lts : LTS State Label) : State → Label → State → Prop where
| refl : lts.STr s HasTau.τ s
| tr : lts.STr s1 HasTau.τ s2 → lts.Tr s2 μ s3 → lts.STr s3 HasTau.τ s4 → lts.STr s1 μ s4

/-- The `LTS` obtained by saturating the transition relation in `lts`. -/
def LTS.saturate [HasTau Label] (lts : LTS State Label) : LTS State Label where
  Tr := LTS.STr lts

/-- Any transition is also a saturated transition. -/
theorem LTS.STr.single [HasTau Label] (lts : LTS State Label) : lts.Tr s μ s' → lts.STr s μ s' := by
  intro h
  apply LTS.STr.tr LTS.STr.refl h LTS.STr.refl

/-- As `LTS.str`, but counts the number of `τ`-transitions. This is convenient as induction metric. -/
inductive LTS.strN [HasTau Label] (lts : LTS State Label) : ℕ → State → Label → State → Prop where
| refl : lts.strN 0 s HasTau.τ s
| tr : lts.strN n s1 HasTau.τ s2 → lts.Tr s2 μ s3 → lts.strN m s3 HasTau.τ s4 → lts.strN (n + m + 1) s1 μ s4

/-- `LTS.str` and `LTS.strN` are equivalent. -/
theorem LTS.str_strN [HasTau Label] (lts : LTS State Label) : lts.STr s1 μ s2 ↔ ∃ n, lts.strN n s1 μ s2 := by
  apply Iff.intro <;> intro h
  case mp =>
    induction h
    case refl =>
      exists 0
      exact LTS.strN.refl
    case tr s1 sb μ sb' s2 hstr1 htr hstr2 ih1 ih2 =>
      obtain ⟨n1, ih1⟩ := ih1
      obtain ⟨n2, ih2⟩ := ih2
      exists (n1 + n2 + 1)
      apply LTS.strN.tr ih1 htr ih2
  case mpr =>
    obtain ⟨n, h⟩ := h
    induction h
    case refl =>
      constructor
    case tr n s1 sb μ sb' m s2 hstr1 htr hstr2 ih1 ih2 =>
      apply LTS.STr.tr ih1 htr ih2

/-- Saturated transitions labelled by τ can be composed (weighted version). -/
theorem LTS.strN.trans_τ
  [HasTau Label] (lts : LTS State Label)
  (h1 : lts.strN n s1 HasTau.τ s2) (h2 : lts.strN m s2 HasTau.τ s3) :
  lts.strN (n + m) s1 HasTau.τ s3 := by
  cases h1
  case refl =>
    simp
    exact h2
  case tr n1 sb sb' n2 hstr1 htr hstr2 =>
    have ih := LTS.strN.trans_τ lts hstr2 h2
    have conc := LTS.strN.tr hstr1 htr ih
    have n_eq : n1 + (n2 + m) + 1 = n1 + n2 + 1 + m := by omega
    rw [← n_eq]
    exact conc

/-- Saturated transitions labelled by τ can be composed. -/
theorem LTS.STr.trans_τ
  [HasTau Label] (lts : LTS State Label)
  (h1 : lts.STr s1 HasTau.τ s2) (h2 : lts.STr s2 HasTau.τ s3) :
  lts.STr s1 HasTau.τ s3 := by
  obtain ⟨n, h1N⟩ := (LTS.str_strN lts).1 h1
  obtain ⟨m, h2N⟩ := (LTS.str_strN lts).1 h2
  have concN := LTS.strN.trans_τ lts h1N h2N
  apply (LTS.str_strN lts).2 ⟨n + m, concN⟩

/-- Saturated transitions can be appended with τ-transitions (weighted version). -/
theorem LTS.strN.append
  [HasTau Label] (lts : LTS State Label)
  (h1 : lts.strN n1 s1 μ s2)
  (h2 : lts.strN n2 s2 HasTau.τ s3) :
  lts.strN (n1 + n2) s1 μ s3 := by
  cases h1
  case refl =>
    simp
    exact h2
  case tr n11 sb sb' n12 hstr1 htr hstr2 =>
    have hsuffix := LTS.strN.trans_τ lts hstr2 h2
    have n_eq : n11 + (n12 + n2) + 1 = (n11 + n12 + 1 + n2) := by omega
    rw [← n_eq]
    apply LTS.strN.tr hstr1 htr hsuffix

/-- Saturated transitions can be composed (weighted version). -/
theorem LTS.strN.comp
  [HasTau Label] (lts : LTS State Label)
  (h1 : lts.strN n1 s1 HasTau.τ s2)
  (h2 : lts.strN n2 s2 μ s3)
  (h3 : lts.strN n3 s3 HasTau.τ s4) :
  lts.strN (n1 + n2 + n3) s1 μ s4 := by
  cases h2
  case refl =>
    apply LTS.strN.trans_τ lts h1 h3
  case tr n21 sb sb' n22 hstr1 htr hstr2 =>
    have hprefix_τ := LTS.strN.trans_τ lts h1 hstr1
    have hprefix := LTS.strN.tr hprefix_τ htr hstr2
    have conc := LTS.strN.append lts hprefix h3
    have n_eq : (n1 + n21 + n22 + 1 + n3) = (n1 + (n21 + n22 + 1) + n3) := by omega
    rw [← n_eq]
    apply conc

/-- Saturated transitions can be composed. -/
theorem LTS.STr.comp
  [HasTau Label] (lts : LTS State Label)
  (h1 : lts.STr s1 HasTau.τ s2)
  (h2 : lts.STr s2 μ s3)
  (h3 : lts.STr s3 HasTau.τ s4) :
  lts.STr s1 μ s4 := by
  obtain ⟨n1, h1N⟩ := (LTS.str_strN lts).1 h1
  obtain ⟨n2, h2N⟩ := (LTS.str_strN lts).1 h2
  obtain ⟨n3, h3N⟩ := (LTS.str_strN lts).1 h3
  have concN := LTS.strN.comp lts h1N h2N h3N
  apply (LTS.str_strN lts).2 ⟨n1 + n2 + n3, concN⟩

end Weak

/-! ## Divergence -/

section Divergence

/-- A divergent execution is a stream of states where each state is the anti-τ-derivative of the
next. -/
def LTS.DivergentExecution [HasTau Label] (lts : LTS State Label)
  (stream : Stream' State) : Prop :=
  ∀ n, lts.Tr (stream n) HasTau.τ (stream n.succ)

/-- A state is divergent if there is a divergent execution from it. -/
def LTS.Divergent [HasTau Label] (lts : LTS State Label) (s : State) : Prop :=
  ∃ stream : Stream' State, stream 0 = s ∧ lts.DivergentExecution stream

/-- If a stream is a divergent execution, then any 'suffix' is also a divergent execution. -/
theorem LTS.divergent_drop [HasTau Label] (lts : LTS State Label) (stream : Stream' State) (h : lts.DivergentExecution stream) (n : ℕ) : lts.DivergentExecution (stream.drop n) := by
  simp only [LTS.DivergentExecution]
  intro m
  simp only [Stream'.drop, Stream'.get]
  simp [LTS.DivergentExecution] at h
  specialize h (n + m)
  have n_eq : m.succ + n = n + m + 1 := by omega
  have n_comm : n + m = m + n := by apply Nat.add_comm
  rw [n_eq, ← n_comm]
  apply h

/-- An LTS is divergence-free if it has no divergent state. -/
def LTS.DivergenceFree [HasTau Label] (lts : LTS State Label) : Prop :=
  ¬∃ s, lts.Divergent s

end Divergence

open Lean Elab Meta Command Term

/-- A command to create an `LTS` from a labelled transition `α → β → α → Prop`, robust to use of `variable `-/
elab "create_lts" lt:ident name:ident : command => do
  liftTermElabM do
    let lt ← realizeGlobalConstNoOverloadWithInfo lt
    let ci ← getConstInfo lt
    forallTelescope ci.type fun args ty => do
      let throwNotLT := throwError m!"type{indentExpr ci.type}\nis not a labelled transition"
      unless args.size ≥ 2 do
        throwNotLT
      unless ← isDefEq (← inferType args[args.size - 3]!) (← inferType args[args.size - 1]!) do
        throwNotLT
      unless (← whnf ty).isProp do
        throwError m!"expecting Prop, not{indentExpr ty}"
      let params := ci.levelParams.map .param
      let lt := mkAppN (.const lt params) args[0...args.size-3]
      let bundle ← mkAppM ``LTS.mk #[lt]
      let value ← mkLambdaFVars args[0...args.size-3] bundle
      let type ← inferType value
      addAndCompile <| .defnDecl {
        name := name.getId
        levelParams := ci.levelParams
        type
        value
        safety := .safe
        hints := .abbrev
      }
      addTermInfo' name (.const name.getId params) (isBinder := true)
      addDeclarationRangesFromSyntax name.getId name

/-- 
  This command adds notations for an `LTS.Tr`. This should not usually be called directly, but from
  the `lts` attribute. 

  As an example `lts_reduction_notation foo "β"` will add the notations "[⬝]⭢β" and "[⬝]↠β"

  Note that the string used will afterwards be registered as a notation. This means that if you have
  also used this as a constructor name, you will need quotes to access corresponding cases, e.g. «β»
  in the above example.
-/
syntax "lts_reduction_notation" ident (Lean.Parser.Command.notationItem)? : command
macro_rules
  | `(lts_reduction_notation $lts $sym) => 
    `(
      notation:39 t "["μ"]⭢"$sym t' => (LTS.Tr $lts) t μ t'
      notation:39 t "["μ"]↠"$sym t' => (LTS.MTr $lts) t μ t'
     )
  | `(lts_reduction_notation $lts) => 
    `(
      notation:39 t "["μ"]⭢" t' => (LTS.Tr $lts) t μ t'
      notation:39 t "["μ"]↠" t' => (LTS.MTr $lts) t μ t'
     )

/-- This attribute calls the `lts_reduction_notation` command for the annotated declaration. -/
syntax (name := lts_attr) "lts" ident (Lean.Parser.Command.notationItem)? : attr

initialize Lean.registerBuiltinAttribute {
  name := `lts_attr
  descr := "Register notation for an LTS"
  add := fun decl stx _ => MetaM.run' do
    match stx with
    | `(attr | lts $lts $sym) =>
        liftCommandElabM <| Command.elabCommand (← `(create_lts $(mkIdent decl) $lts))
        liftCommandElabM <| Command.elabCommand (← `(lts_reduction_notation $lts $sym))
    | `(attr | lts $lts) =>
        liftCommandElabM <| Command.elabCommand (← `(create_lts $(mkIdent decl) $lts))
        liftCommandElabM <| Command.elabCommand (← `(lts_reduction_notation $lts))
    | _ => throwError "invalid syntax for 'lts' attribute"
}
