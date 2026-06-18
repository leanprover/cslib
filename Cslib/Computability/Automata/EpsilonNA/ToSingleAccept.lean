/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Computability.Automata.EpsilonNA.Basic

/-! # Translation of εNA into εNA with a single accept state

Defines the transformation `toSingleAccept` for `εNA.FinAcc` and proves correctness
results in terms of language equivalence and correspondences between the two transition systems.

Note for future work: we could formulate a stronger transformation, whereby also the set of accept
states becomes a singleton.
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
  cases os with
  | none => simp only [toSingleAccept] at h
  | some _ => simp

theorem toSingleAccept_tr_tr {a : εNA.FinAcc State Symbol} :
    a.toSingleAccept.Tr (some s) x (some s') ↔ a.Tr s x s' := by
  simp [toSingleAccept]

scoped grind_pattern toSingleAccept_tr_tr => a.toSingleAccept.Tr (some s) x (some s')

@[scoped grind →]
theorem toSingleAccept_tr_none_accept {a : εNA.FinAcc State Symbol}
    (h : a.toSingleAccept.Tr os x none) : ∃ s, os = some s ∧ s ∈ a.accept := by
  grind

@[scoped grind ⇒]
theorem toSingleAccept_not_tr_none {a : εNA.FinAcc State Symbol} :
    ¬a.toSingleAccept.Tr none x os := by
  grind only [toSingleAccept]

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
      | stepL => grind
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
  case head _ _ h₁ h₂ ih =>
    grind only [toSingleAccept_tr_antiDerivative_isSome h₁, = Option.isSome_none]

@[scoped grind →]
theorem toSingleAccept_τSTr_antiDerivative_isSome {a : εNA.FinAcc State Symbol}
    (h : a.toSingleAccept.τSTr os (some s')) : os.isSome := by
  induction h using Relation.ReflTransGen.head_induction_on
  case refl => grind only [= Option.isSome_some]
  case head _ _ h₁ h₂ ih =>
    exact toSingleAccept_tr_antiDerivative_isSome h₁

@[scoped grind =]
theorem toSingleAccept_τSTr_τSTr {a : εNA.FinAcc State Symbol}
    : a.toSingleAccept.τSTr (some s) (some s') ↔ a.τSTr s s' := by
  generalize hos' : some s' = os'
  apply Iff.intro <;> intro h
  case mp =>
    induction h generalizing s'
    case refl =>
      cases hos'
      constructor
    case tail osb os' hτstr htr ih =>
      have hosb := toSingleAccept_tr_antiDerivative_isSome (os := osb) (os' := os') htr
      apply Option.isSome_iff_exists.mp at hosb
      rcases hosb with ⟨sb, hosb⟩
      apply Relation.ReflTransGen.trans (b := sb) (ih hosb.symm)
      apply Relation.ReflTransGen.single
      rw [hosb, ← hos'] at htr
      apply htr
  case mpr =>
    induction h generalizing os'
    case refl =>
      cases hos'
      constructor
    case tail sb s' hτstr htr ih =>
      specialize ih (os' := some sb) rfl
      apply Relation.ReflTransGen.trans (b := some sb) ih
      apply Relation.ReflTransGen.single
      rw [← hos']
      apply toSingleAccept_tr_tr.mpr htr

@[scoped grind →]
theorem toSingleAccept_τSTr_none_accept {a : εNA.FinAcc State Symbol}
    (h : a.toSingleAccept.τSTr (some s) none) : ∃ s' ∈ a.accept, a.τSTr s s' := by
  generalize hos' : none = os' at h
  induction h
  case refl => simp at hos'
  case tail osb os' h₁ h₂ ih =>
    rw [← hos'] at h₂
    have hosb : ∃ sb, osb = some sb ∧ sb ∈ a.accept := by
      apply toSingleAccept_tr_none_accept h₂
    rcases hosb with ⟨sb, hosb, hsb⟩
    exists sb; apply And.intro hsb
    rw [hosb] at h₁
    apply toSingleAccept_τSTr_τSTr.mp h₁

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
      grind [LTS.STr.tr (s2 := some sb₁) (s3 := some sb₂)]

@[scoped grind →]
theorem toSingleAccept_sTr_none_accept {a : εNA.FinAcc State Symbol}
    (h : a.toSingleAccept.STr (some s) x none) : ∃ s' ∈ a.accept, a.STr s x s' := by
  cases h
  case tr osb₁ osb₂ h₁ h₂ h₃ =>
    have ⟨sb₁, hosb₁⟩ : ∃ sb₁, osb₁ = some sb₁ := by grind
    rw [hosb₁] at h₂
    cases hosb₂ : osb₂
    case none =>
      rw [hosb₂] at h₂
      have h₂' := toSingleAccept_tr_none_accept h₂
      rcases h₂' with ⟨s', hs', hs'a⟩
      exists s'; apply And.intro hs'a
      rw [hs'] at h₂
      have hx : x = none := by grind
      rw [hx]
      rw [hosb₁, hs'] at h₁
      cases h₁
      case refl =>
        apply LTS.STr.refl
      case tail osb htrb htr =>
        have ⟨sb, hosb⟩ : ∃ sb, osb = some sb := by
          grind only [toSingleAccept_tr_antiDerivative_isSome htr, Option.isSome_iff_exists]
        rw [hosb] at htr
        apply toSingleAccept_tr_tr.mp at htr
        rw [hosb] at htrb
        apply toSingleAccept_τSTr_τSTr.mp at htrb
        apply LTS.STr.tr htrb htr LTS.τSTr.refl
    case some sb₂ =>
      rw [hosb₁] at h₁
      rw [hosb₂] at h₂ h₃
      have ⟨s', hs', hsb₂⟩ := toSingleAccept_τSTr_none_accept h₃
      exists s'; apply And.intro hs'
      apply LTS.STr.tr
        (toSingleAccept_τSTr_τSTr.mp h₁)
        (toSingleAccept_tr_tr.mp h₂)
        hsb₂

@[scoped grind →]
theorem toSingleAccept_sTr_none_none {a : εNA.FinAcc State Symbol}
    (h : a.toSingleAccept.STr none x os) : x = none ∧ os = none := by
  cases h
  case refl => trivial
  case tr osb₁ osb₂ h₁ h₂ h₃ =>
    have hosb₁ : osb₁ = none := by grind
    rw [hosb₁] at h₂
    grind

@[scoped grind →]
theorem toSingleAccept_sMTr_antiDerivative_isSome {a : εNA.FinAcc State Symbol}
    (h : a.toSingleAccept.SMTr os xs (some s')) : os.isSome := by
  generalize hos' : some s' = os' at h
  induction h <;> grind only [= Option.isSome_iff_exists,
    → toSingleAccept_sTr_antiDerivative_isSome]

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
    case stepL s x sb xs s' h₁ h₂ ih =>
      grind [LTS.SMTr.stepL (s2 := some sb)]

@[scoped grind →]
theorem toSingleAccept_sMTr_none_accept {a : εNA.FinAcc State Symbol}
    (h : a.toSingleAccept.SMTr (some s) (List.map some xs) none) :
    ∃ s' ∈ a.accept, a.SMTr s (List.map some xs) s' := by
  induction xs generalizing s
  case nil =>
    rcases h with ⟨h⟩
    have ⟨s', hs', h'⟩ := toSingleAccept_sTr_none_accept h
    exists s'; apply And.intro hs'
    apply LTS.SMTr.τ h'
  case cons x xs ih =>
    cases h
    case stepL osb hstr hsmtr =>
      cases hosb : osb
      case none =>
        rw [hosb] at hstr hsmtr
        have ⟨s', hs', hstr'⟩ := toSingleAccept_sTr_none_accept hstr
        exists s'; apply And.intro hs'
        have hxs : xs = [] := by
          cases xs
          case nil => rfl
          case cons x' xs =>
            cases hsmtr
            grind
        apply LTS.SMTr.stepL hstr' (by grind)
      case some sb =>
        rw [hosb] at hstr hsmtr
        have ⟨s', hs', ih'⟩ := ih hsmtr
        exists s'; apply And.intro hs'
        apply LTS.SMTr.stepL (toSingleAccept_sTr_sTr.mp hstr) ih'

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
    exists s
    apply And.intro (by grind)
    exists none
    apply And.intro (by grind)
    have h' : a.toSingleAccept.SMTr (some s) (List.map some xs) (some s') := by grind
    have hcomp := LTS.SMTr.comp (lts := a.toSingleAccept.toLTS) (s₁ := some s) (s₂ := some s')
      (s₃ := none) (μs₁ := List.map some xs) (μs₂ := []) h'
    simp only [List.append_nil] at hcomp
    apply hcomp
    constructor
    apply LTS.STr.single
    grind [toSingleAccept]

end Cslib.Automata.εNA.FinAcc
