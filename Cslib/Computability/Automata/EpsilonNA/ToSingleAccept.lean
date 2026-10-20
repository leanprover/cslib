/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Computability.Automata.EpsilonNA.Basic
public import Cslib.Foundations.Semantics.LTS.Simulation

/-! # Translation of εNA into εNA with a single start or accept state

Defines the transformation `toSingleAccept` for `εNA.FinAcc` and proves correctness
results in terms of language equivalence and correspondences between the two transition systems.

The transformation `toSingleStart` similarly yields a single start state, without incoming
transitions, and `toSingleStartAccept` combines the two.
-/

@[expose] public section

namespace Cslib.Automata.εNA.FinAcc

variable {State Symbol : Type*}

/-- Any `εNA.FinAcc` can be converted into an `εNA.FinAcc` with a single accept state `none`.
The original states are wrapped in `some`, and all original accept states have ε-transitions to
`none`. -/
@[local grind]
def toSingleAccept (a : εNA.FinAcc State Symbol) : εNA.FinAcc (Option State) Symbol where
  start := some '' a.start
  accept := {none}
  Tr
    | some s, x, some s' => a.Tr s x s'
    | some s, none, none => s ∈ a.accept
    | _, _, _ => False

@[scoped grind =]
theorem toSingleAccept_accept_def {a : εNA.FinAcc State Symbol} :
    a.toSingleAccept.accept = {none} := rfl

open Acceptor in
@[scoped grind .]
theorem toSingleAccept_accepts_mTr_iff {a : εNA.FinAcc State Symbol} :
    Accepts a.toSingleAccept xs ↔
    ∃ s ∈ a.toSingleAccept.start, a.toSingleAccept.SMTr s (xs.map Option.some) none := by
  grind [Accepts]

open scoped LTS LTS.MTr LTS.STr LTS.SMTr

@[scoped grind →]
theorem toSingleAccept_tr_antiDerivative_isSome {a : εNA.FinAcc State Symbol}
    (h : a.toSingleAccept.Tr os x os') : os.isSome := by
  cases os with grind

theorem toSingleAccept_tr_tr {a : εNA.FinAcc State Symbol} :
    a.toSingleAccept.Tr (some s) x (some s') ↔ a.Tr s x s' := Iff.rfl

scoped grind_pattern toSingleAccept_tr_tr => a.toSingleAccept.Tr (some s) x (some s')

@[scoped grind →]
theorem toSingleAccept_tr_none_accept {a : εNA.FinAcc State Symbol}
    (h : a.toSingleAccept.Tr os x none) : ∃ s, os = some s ∧ s ∈ a.accept := by
  grind

@[scoped grind ⇒]
theorem toSingleAccept_not_tr_none {a : εNA.FinAcc State Symbol} :
    ¬a.toSingleAccept.Tr none x os := by
  grind

@[scoped grind →]
theorem toSingleAccept_mTr_antiDerivative_isSome {a : εNA.FinAcc State Symbol}
    (h : a.toSingleAccept.MTr os x (some s')) : os.isSome := by
  generalize hos' : some s' = os' at h
  induction h <;> grind

@[scoped grind =]
theorem toSingleAccept_mTr_mTr {a : εNA.FinAcc State Symbol} :
    a.toSingleAccept.MTr (some s) xs (some s') ↔ a.MTr s xs s' := by
  induction xs generalizing s
  case nil => grind
  case cons x xs ih =>
    apply Iff.intro <;> intro h
    case mp =>
      cases h with
      | @stepL s _ s'' _ _ htr hmtr =>
        obtain ⟨smid, rfl⟩ : ∃ smid, s'' = Option.some smid :=
          s''.isSome_iff_exists.mp (toSingleAccept_mTr_antiDerivative_isSome hmtr)
        exact (ih.mp hmtr).stepL (toSingleAccept_tr_tr.mp htr)
    case mpr =>
      cases h
      case stepL sb htr hmtr =>
        apply LTS.MTr.stepL (s2 := some sb) <;> grind

@[scoped grind →]
theorem toSingleAccept_τSTr_antiDerivative_none {a : εNA.FinAcc State Symbol}
    (h : a.toSingleAccept.τSTr none os) : os = none := by
  generalize hnone : none = os' at h
  induction h using Relation.ReflTransGen.head_induction_on
  case refl => rfl
  case head _ _ h₁ h₂ ih => grind [toSingleAccept_tr_antiDerivative_isSome h₁]

@[scoped grind →]
theorem toSingleAccept_τSTr_antiDerivative_isSome {a : εNA.FinAcc State Symbol}
    (h : a.toSingleAccept.τSTr os (some s')) : os.isSome := by
  induction h using Relation.ReflTransGen.head_induction_on
  case refl => exact Option.isSome_some
  case head _ _ h₁ h₂ ih => exact toSingleAccept_tr_antiDerivative_isSome h₁

@[scoped grind =]
theorem toSingleAccept_τSTr_τSTr {a : εNA.FinAcc State Symbol}
    : a.toSingleAccept.τSTr (some s) (some s') ↔ a.τSTr s s' := by
  apply Iff.intro
  · generalize hos' : some s' = os'
    intro h
    induction h generalizing s' with
    | refl =>
      cases hos'
      exact LTS.τSTr.refl
    | tail hτstr htr ih =>
      subst hos'
      obtain ⟨_, rfl⟩ := Option.isSome_iff_exists.mp <| toSingleAccept_tr_antiDerivative_isSome htr
      exact .tail (ih rfl) htr
  · intro h
    cases h with
    | refl => exact LTS.τSTr.refl
    | tail hτstr htr => exact .tail (.lift some (by rfl) _ _ hτstr) htr

@[scoped grind →]
theorem toSingleAccept_τSTr_none_accept {a : εNA.FinAcc State Symbol}
    (h : a.toSingleAccept.τSTr (some s) none) : ∃ s' ∈ a.accept, a.τSTr s s' := by
  generalize hos' : none = os' at h
  induction h
  case refl => simp at hos'
  case tail osb os' h₁ h₂ ih =>
    subst hos'
    have ⟨sb, hosb, hsb⟩ := toSingleAccept_tr_none_accept h₂
    subst hosb
    exact ⟨sb, hsb, toSingleAccept_τSTr_τSTr.mp h₁⟩

@[scoped grind →]
theorem toSingleAccept_sTr_antiDerivative_isSome {a : εNA.FinAcc State Symbol}
    (h : a.toSingleAccept.STr os x (some s')) : os.isSome := by
  generalize hos' : some s' = os'
  cases h <;> grind

@[scoped grind =]
theorem toSingleAccept_sTr_sTr {a : εNA.FinAcc State Symbol}
    : a.toSingleAccept.STr (some s) x (some s') ↔ a.STr s x s' := by
  generalize hos' : some s' = os'
  apply Iff.intro <;> intro h
  case mp =>
    induction h
    case refl => grind only [Option.some_inj, LTS.STr.refl]
    case tr osb₁ x osb₂ os' h₁ h₂ h₃ =>
      have ⟨sb₂, hosb₂⟩ : ∃ sb₂, osb₂ = some sb₂ := by grind
      have ⟨sb₁, hosb₁⟩ : ∃ sb₁, osb₁ = some sb₁ := by grind
      grind [LTS.STr.tr (s2 := sb₁) (s3 := sb₂)]
  case mpr =>
    induction h
    case refl => grind only [LTS.STr.refl]
    case tr sb₁ x sb₂ s' h₁ h₂ h₃ =>
      apply LTS.STr.tr (s2 := some sb₁) (s3 := some sb₂)
        (toSingleAccept_τSTr_τSTr.mpr h₁)
        (toSingleAccept_tr_tr.mpr h₂)
        (hos' ▸ toSingleAccept_τSTr_τSTr.mpr h₃)

@[scoped grind →]
theorem toSingleAccept_sTr_none_accept {a : εNA.FinAcc State Symbol}
    (h : a.toSingleAccept.STr (some s) x none) : ∃ s' ∈ a.accept, a.STr s x s' := by
  cases h
  case tr osb₁ osb₂ h₁ h₂ h₃ =>
    obtain ⟨sb₁, rfl⟩ := Option.isSome_iff_exists.mp
      (toSingleAccept_tr_antiDerivative_isSome h₂)
    cases osb₂ with
    | none =>
      have hx : x = none := by grind
      subst x
      exact ⟨sb₁, h₂, (LTS.sTr_τSTr_iff a.toLTS).mpr (toSingleAccept_τSTr_τSTr.mp h₁)⟩
    | some sb₂ =>
      obtain ⟨s', hs', hsb₂⟩ := toSingleAccept_τSTr_none_accept h₃
      exact ⟨s', hs', LTS.STr.tr (toSingleAccept_τSTr_τSTr.mp h₁)
        (toSingleAccept_tr_tr.mp h₂) hsb₂⟩

@[scoped grind →]
theorem toSingleAccept_sTr_none_none {a : εNA.FinAcc State Symbol}
    (h : a.toSingleAccept.STr none x os) : x = none ∧ os = none := by
  cases h
  case refl => trivial
  case tr osb₁ osb₂ h₁ h₂ h₃ => grind

@[scoped grind →]
theorem toSingleAccept_sMTr_antiDerivative_isSome {a : εNA.FinAcc State Symbol}
    (h : a.toSingleAccept.SMTr os xs (some s')) : os.isSome := by
  generalize hos' : some s' = os' at h
  induction h <;> grind [= Option.isSome_iff_exists]

@[scoped grind =]
theorem toSingleAccept_sMTr_sMTr {a : εNA.FinAcc State Symbol}
    : a.toSingleAccept.SMTr (some s) x (some s') ↔ a.SMTr s x s' := by
  generalize hos : some s = os, hos' : some s' = os'
  apply Iff.intro <;> intro h
  case mp =>
    induction h generalizing s
    case τ => grind [LTS.SMTr.τ]
    case stepL os x osb xs os' h₁ h₂ ih =>
      have ⟨sb, hosb⟩ : ∃ sb, osb = some sb := by grind [Option.isSome_iff_exists]
      grind [LTS.SMTr.stepL (s2 := sb)]
  case mpr =>
    induction h generalizing os
    case τ => grind [LTS.SMTr.τ]
    case stepL s x sb xs s' h₁ h₂ ih => grind [LTS.SMTr.stepL (s2 := some sb)]

@[scoped grind →]
theorem toSingleAccept_sMTr_none_accept {a : εNA.FinAcc State Symbol}
    (h : a.toSingleAccept.SMTr (some s) (List.map some xs) none) :
    ∃ s' ∈ a.accept, a.SMTr s (List.map some xs) s' := by
  induction xs generalizing s
  case nil =>
    rcases h with ⟨h⟩
    have ⟨s', hs', h'⟩ := toSingleAccept_sTr_none_accept h
    exact ⟨s', hs', LTS.SMTr.τ h'⟩
  case cons x xs ih =>
    cases h
    case stepL osb hstr hsmtr =>
      cases hosb : osb
      case none =>
        subst hosb
        have ⟨s', hs', hstr'⟩ := toSingleAccept_sTr_none_accept hstr
        refine ⟨s', hs', LTS.SMTr.stepL hstr' ?_⟩
        have hxs : xs = [] := by cases xs with grind [cases LTS.SMTr]
        grind
      case some sb =>
        subst hosb
        have ⟨s', hs', ih'⟩ := ih hsmtr
        exact ⟨s', hs', LTS.SMTr.stepL (toSingleAccept_sTr_sTr.mp hstr) ih'⟩

open Acceptor in
/-- `toSingleAccept` preserves the language of the input automaton. -/
@[scoped grind =]
theorem toSingleAccept_language_eq {a : εNA.FinAcc State Symbol} :
    language a.toSingleAccept = language a := by
  ext xs
  apply Iff.intro <;> intro h
  case mp =>
    rcases h with ⟨os, hos, os', hos', hsmtr⟩
    rcases hos with ⟨s, hs₁, hs₂⟩
    exists s
    grind
  case mpr =>
    rcases h with ⟨s, hs, s', hs', hsmtr⟩
    refine ⟨s, by grind, none, by grind, ?_⟩
    rw [show xs.map some = xs.map some ++ [] by simp]
    exact LTS.SMTr.comp (toSingleAccept_sMTr_sMTr.mpr hsmtr) <| LTS.SMTr.τ (LTS.STr.single hs')

/-- Any `εNA.FinAcc` can be converted into an `εNA.FinAcc` with a single start state `none`.
The original states are wrapped in `some`, and `none` has ε-transitions to all original start
states. -/
def toSingleStart (a : εNA.FinAcc State Symbol) : εNA.FinAcc (Option State) Symbol where
  start := {none}
  accept := some '' a.accept
  Tr
    | some s, x, some s' => a.Tr s x s'
    | none, none, some s => s ∈ a.start
    | _, _, _ => False

theorem toSingleStart_tr_tr {a : εNA.FinAcc State Symbol} {s s' : State} {x : Option Symbol} :
    a.toSingleStart.Tr (some s) x (some s') ↔ a.Tr s x s' := Iff.rfl

theorem toSingleStart_tr_start {a : εNA.FinAcc State Symbol} {s : State} (hs : s ∈ a.start) :
    a.toSingleStart.Tr none none (some s) := hs

/-- No transition of `toSingleStart` leads to its start state. -/
theorem toSingleStart_not_tr_none {a : εNA.FinAcc State Symbol} {os : Option State}
    {x : Option Symbol} : ¬a.toSingleStart.Tr os x none := by
  cases os <;> cases x <;> simp [toSingleStart]

/-- The transitions from the start state of `toSingleStart` are `ε`-transitions to the original
start states. -/
theorem toSingleStart_tr_none {a : εNA.FinAcc State Symbol} {os : Option State}
    {x : Option Symbol} (h : a.toSingleStart.Tr none x os) :
    x = none ∧ ∃ s, os = some s ∧ s ∈ a.start := by
  cases x <;> cases os <;> simp_all [toSingleStart]

/-- Multistep transitions of `toSingleStart` between original states are those of the original
automaton. -/
theorem toSingleStart_mTr_mTr {a : εNA.FinAcc State Symbol} {s s' : State}
    {xs : List (Option Symbol)} : a.toSingleStart.MTr (some s) xs (some s') ↔ a.MTr s xs s' := by
  constructor
  · intro h
    induction xs generalizing s with
    | nil =>
      cases h
      exact .refl
    | cons x xs ih =>
      obtain ⟨os, htr, h'⟩ := LTS.MTr.cons_iff.mp h
      cases os with
      | none => exact absurd htr toSingleStart_not_tr_none
      | some s'' => exact .stepL (toSingleStart_tr_tr.mp htr) (ih h')
  · intro h
    exact h.map some fun _ _ _ => toSingleStart_tr_tr.mpr

open Acceptor in
/-- `toSingleStart` preserves the language of the input automaton. -/
@[scoped grind =]
theorem toSingleStart_language_eq {a : εNA.FinAcc State Symbol} :
    language a.toSingleStart = language a := by
  ext xs
  rw [mem_language_iff, mem_language_iff]
  constructor
  · rintro ⟨_, hs', _, ht', μs, rfl, h⟩
    obtain rfl := Set.mem_singleton_iff.mp hs'
    obtain ⟨t, ht, rfl⟩ := (Set.mem_image _ _ _).mp ht'
    cases μs with
    | nil => cases h
    | cons μ μs =>
      obtain ⟨os, htr, h'⟩ := LTS.MTr.cons_iff.mp h
      obtain ⟨rfl, s, rfl, hs⟩ := toSingleStart_tr_none htr
      exact ⟨s, hs, t, ht, μs, rfl, toSingleStart_mTr_mTr.mp h'⟩
  · rintro ⟨s, hs, t, ht, μs, rfl, h⟩
    refine ⟨none, Set.mem_singleton _, some t, Set.mem_image_of_mem _ ht, none :: μs, rfl, ?_⟩
    exact .stepL (toSingleStart_tr_start hs) (toSingleStart_mTr_mTr.mpr h)

/-- Any `εNA.FinAcc` can be converted into an `εNA.FinAcc` with a single start state `none`,
without incoming transitions, and a single accept state `some none`, without outgoing
transitions. -/
def toSingleStartAccept (a : εNA.FinAcc State Symbol) :
    εNA.FinAcc (Option (Option State)) Symbol :=
  a.toSingleAccept.toSingleStart

theorem toSingleStartAccept_start {a : εNA.FinAcc State Symbol} :
    a.toSingleStartAccept.start = {none} := rfl

theorem toSingleStartAccept_accept {a : εNA.FinAcc State Symbol} :
    a.toSingleStartAccept.accept = {some none} := by
  simp [toSingleStartAccept, toSingleStart, toSingleAccept_accept_def]

open Acceptor in
/-- `toSingleStartAccept` preserves the language of the input automaton. -/
@[scoped grind =]
theorem toSingleStartAccept_language_eq {a : εNA.FinAcc State Symbol} :
    language a.toSingleStartAccept = language a := by
  rw [toSingleStartAccept, toSingleStart_language_eq, toSingleAccept_language_eq]

end Cslib.Automata.εNA.FinAcc
