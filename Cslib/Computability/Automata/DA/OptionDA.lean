/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Computability.Automata.DA.Basic
public import Cslib.Computability.Automata.EpsilonNA.Basic
public import Cslib.Computability.Automata.EpsilonNA.ToNA
public import Cslib.Computability.Automata.NA.ToDA

/-! # OptionDA: DA with a single halting accept state

An `OptionDA` is a deterministic automaton with a unique accepting and halting state, codified as
`none : Option State`. Any `DA.FinAcc` can be converted into an `OptionDA` by (i) adding an
ε-transition from every accepting state to the `none` halting state, and then (ii) by transforming
the resulting `εNA` into an `OptionDA`.
-/

@[expose] public section

namespace Cslib.Automata

/-- A deterministic automaton with a single accepting, halting state, modelled as the `none` value
of `Option Symbol`. -/
structure OptionDA (State Symbol : Type*) where
  /-- The transition function of the automaton. -/
  tr : State → Symbol → Option State
  /-- The initial state of the automaton. -/
  start : State

variable {State Symbol : Type*}

namespace OptionDA

/-- Multistep transition function. -/
def mtr (a : OptionDA State Symbol) : State → List Symbol → Option State
  | s, [] => s
  | s, x :: xs => a.tr s x >>= (a.mtr · xs)

/-- An `OptionDA` accepts a string if its multistep transition function maps the start state and
the string to an accept state.

This is the standard string recognition performed by DFAs in the literature. -/
@[simp, scoped grind =]
instance : Acceptor (OptionDA State Symbol) Symbol where
  Accepts (a : OptionDA State Symbol) (xs : List Symbol) := a.mtr a.start xs = .none

end OptionDA

/-- Converts a `DA.FinAcc` into an `εNA` with an additional `none` state that acts as the unique
accepting and halting state. Every accepting state of the original automaton gains an ε-transition
to `none`, and all other transitions are lifted by `some`. -/
@[scoped grind =]
def DA.FinAcc.toOptionεNA (a : DA.FinAcc State Symbol) : εNA.FinAcc (Option State) Symbol where
  start := {some a.start}
  accept := {none}
  Tr
    -- Lift of original transitions
    | some s, some x, some s' => s' = a.tr s x
    -- Additional ε-transitions to the halting state.
    | some s, none, none => s ∈ a.accept
    | _, _, _ => False

/-- The `none` state in `DA.toOptionεNA` is the only accept state. -/
@[simp]
lemma DA.FinAcc.toOptionεNA_none_accept (a : DA.FinAcc State Symbol) :
    a.toOptionεNA.accept = {none} := rfl

/-- The `none` state in `DA.toOptionεNA` has no outgoing transitions. -/
@[scoped grind .]
lemma DA.FinAcc.toOptionεNA_none_tr (a : DA.FinAcc State Symbol)
    (μ : Option Symbol) (s : Option State) : ¬a.toOptionεNA.Tr none μ s := by grind

/-- The `none` state in `DA.toOptionεNA` has no outgoing transitions. -/
@[scoped grind .]
lemma DA.FinAcc.toOptionεNA_tr_none_iff {a : DA.FinAcc State Symbol}
    (h : a.toOptionεNA.Tr s μ s') : μ = none ↔ s' = none := by cases hμ : μ <;> grind

/-- The `none` state in `DA.toOptionεNA` has no outgoing transitions. -/
@[scoped grind .]
lemma DA.FinAcc.toOptionεNA_ε_τSTr_none {a : DA.FinAcc State Symbol}
    (h : a.toOptionεNA.τSTr s s') : s' = s ∨ s' = none := by
  cases h with
    | refl => simp
    | tail s₁ h =>
      apply toOptionεNA_tr_none_iff at h
      simp only [HasTau.τ, true_iff] at h
      simp [h]

/-- The `none` state in `DA.toOptionεNA` has no outgoing transitions. -/
@[scoped grind .]
lemma DA.FinAcc.toOptionεNA_none_sTr_none {a : DA.FinAcc State Symbol}
    (h : a.toOptionεNA.STr s none s') : s' = s ∨ s' = none := by cases h <;> grind

@[scoped grind =]
lemma DA.FinAcc.toOptionεNA_mem_accept_tr_iff {a : DA.FinAcc State Symbol} :
    s ∈ a.accept ↔ a.toOptionεNA.Tr s none none := by grind only [toOptionεNA]

lemma pippo {a : DA.FinAcc State Symbol} :
    a.toOptionεNA.STr (some s) (some μ) = a.toOptionεNA.Tr (some s) (some μ) := by
  sorry
  -- grind

open scoped LTS LTS.STr LTS.SMTr FLTS εNA εNA.FinAcc

@[scoped grind =]
lemma DA.FinAcc.toOptionεNA_mem_accept_sTr_iff {a : DA.FinAcc State Symbol} :
    s ∈ a.accept ↔ a.toOptionεNA.STr s none none := by
  apply Iff.intro <;> intro h
  case mp =>
    grind only [toOptionεNA_mem_accept_tr_iff, LTS.STr.single]
  case mpr =>
    cases h
    case tr osb osb' h₁ h₂ h₃ =>
      rw [show osb' = none by grind only [toOptionεNA]] at h₂
      induction h₁
      case refl => grind only [= toOptionεNA_mem_accept_tr_iff]
      case tail os os' h₁₁ h₁₂ ih =>
        have h_tr_os: a.toOptionεNA.Tr os none none := by
          have : a.toOptionεNA.τSTr os os' := by
            simp only [LTS.τSTr]
            grind
          simp only [toOptionεNA]
          grind
        exact ih h_tr_os

/-- The ε-closure of the start state in `DA.toOptionεNA` consists of the start state and `none`. -/
@[scoped grind =]
lemma DA.FinAcc.toOptionεNA_start_εClosure {a : DA.FinAcc State Symbol} (h : a.start ∈ a.accept) :
    a.toOptionεNA.εClosure a.toOptionεNA.start = {some a.start, none} := by
  rw [show a.toOptionεNA.start = {some a.start} by rfl]
  simp only [εNA.εClosure, LTS.τClosure, LTS.setImage, Set.mem_singleton_iff, LTS.image,
    LTS.saturate, HasTau.τ, Set.iUnion_iUnion_eq_left]
  ext s
  apply Iff.intro <;> intro h'
  · grind
  · cases h' with
      | inl h' =>
        rw [h']
        apply LTS.STr.refl
      | inr h' =>
        rw [h']
        have htr : a.toOptionεNA.Tr (some a.start) none none := by grind only [toOptionεNA]
        exact LTS.STr.single htr

/-- Correspondence of transitions under `toOptionεNA`. -/
@[scoped grind =]
theorem DA.FinAcc.toOptionεNA_tr_tr_iff {a : DA.FinAcc State Symbol}
    : a.toOptionεNA.Tr (some s) (some μ) (some s') ↔ a.tr s μ = s' := by grind only [toOptionεNA]

/-- Correspondence of transitions under `toOptionεNA`. -/
@[scoped grind =]
theorem DA.FinAcc.toOptionεNA_sTr_tr_iff {a : DA.FinAcc State Symbol} :
    a.toOptionεNA.STr (some s) (some μ) (some s') ↔
    a.toOptionεNA.Tr (some s) (some μ) (some s') := by
  apply Iff.intro <;> intro h
  case mp =>
    cases h
    grind [toOptionεNA]
  case mpr =>
    apply LTS.STr.single h

/-- Correspondence of multistep transitions under `toOptionεNA`. -/
@[scoped grind =]
theorem DA.FinAcc.toOptionεNA_mTr_mTr_iff {a : DA.FinAcc State Symbol}
    : a.toOptionεNA.MTr (some s) (μs.map Option.some) (some s') ↔ a.mtr s μs = s' := by
  induction μs generalizing s
  case nil => grind
  case cons x xs ih =>
    apply Iff.intro <;> intro h
    case mp =>
      cases h
      case stepL sb htr hmtr =>
        have h_tr_sb : a.tr s x = sb := by
          simp only [toOptionεNA] at htr
          grind only
        grind only [FLTS.mtr, List.foldl_cons]
    case mpr =>
      apply LTS.MTr.stepL (s2 := some (a.tr s x)) (by grind) (by grind)

/-- Correspondence of saturated and normal multistep transitions under `toOptionεNA`. -/
@[scoped grind =]
theorem DA.FinAcc.toOptionεNA_sMTr_mTr_iff {a : DA.FinAcc State Symbol} {μs : List Symbol}
    (h : μs ≠ []) : a.toOptionεNA.SMTr (some s) (μs.map Option.some) (some s') ↔
    a.toOptionεNA.MTr (some s) (μs.map Option.some) (some s') := by
  induction μs generalizing s with
  | nil => contradiction
  | cons μ μs ih =>
    simp only [List.map_cons]
    apply Iff.intro <;> intro h'
    case mp =>
      cases h'
      case stepL os hstr hsmtr =>
        have hos : ∃ sb, os = some sb := by
          sorry
        rcases hos with ⟨sb, hos⟩

        cases μs
        case nil => grind
        case cons μ' μs =>

        simp [toOptionεNA]

    case mpr =>
      exact LTS.SMTr.fromMTr h'

/-- Correspondence of multistep transitions under `toOptionεNA`. -/
@[scoped grind =]
theorem DA.FinAcc.toOptionεNA_sMTr_mTr_iff {a : DA.FinAcc State Symbol}
    : a.toOptionεNA.SMTr (some s) (μs.map Option.some) (some s') ↔ a.mtr s μs = s' := by
  induction μs generalizing s
  case nil =>
    simp [toOptionεNA]
    grind
  case cons x xs ih =>
    apply Iff.intro <;> intro h
    case mp =>
      cases h
      case stepL sb htr hmtr =>

        -- have h_tr_sb : a.tr s x = sb := by
        --   simp only [toOptionεNA] at htr
        --   grind only
        grind only [FLTS.mtr, List.foldl_cons]
    case mpr =>
      apply LTS.MTr.stepL (s2 := some (a.tr s x)) (by grind) (by grind)

open Acceptor in
/-- `DA.toOptionεNA` preserves the automaton's language. -/
@[scoped grind =]
theorem DA.FinAcc.toOptionεNA_language_eq {a : DA.FinAcc State Symbol} :
    language a.toOptionεNA = language a := by
  ext xs
  simp only [Acceptor.mem_language, Accepts]
  apply Iff.intro <;> intro h
  case mp =>
    rcases h with ⟨s, hs, s', hs', h⟩
    cases hs' -- s' is none
    revert hs
    cases xs
    case nil =>
      intro hs; cases hs
      cases h
      case refl.τ h =>
        grind [toOptionεNA_mem_accept_sTr_iff.mpr h]
    case cons x xs =>
      intro hs; cases hs
      cases h
      case stepL os h_sTr h_sMTr =>


    simp only [toOptionεNA_none_accept, Set.mem_singleton_iff] at hs'
    simp [hs'] at h

    sorry
  case mpr =>
    induction xs
    case nil =>
      simp only [FLTS.mtr_nil_eq] at h
      exists a.start
      apply And.intro (by grind)
      exists none
      apply And.intro (by simp)
      apply LTS.SMTr.τ
      apply LTS.STr.tr (s2 := some a.start) (s3 := none) <;> grind
    case cons x xs ih =>
      exists a.start
      apply And.intro (by grind)
      exists none
      apply And.intro (by simp)
      simp only [FLTS.mtr, List.foldl_cons] at h
      simp only [List.map_cons]
      rw [← FLTS.mtr] at h

      -- rw [← List.foldl_cons] at h
      grind
    --   exists a.start
    --   apply And.intro
    --   case left => grind
    --   case right =>
    --     have h' : a.start ∈ a.accept := by grind [FLTS.mtr]
    --     exists none
    --     constructor
    --     · grind
    --     · simp
    --       have : (s : State) → s ∈ a.accept → a.toOptionεNA.saturate.Tr (some s) none none := by
    --         intro s hs
    --         sorry
    --       -- simp [LTS.saturate]
    --       -- apply LTS.MTr.stepL

    --       simp [LTS.saturate]


    --       simp [toOptionεNA]


    --     grind
    --     sorry
    -- case cons x xs =>
    --   sorry

namespace NA.FinAcc

def ofOptionFinAcc (a : NA.FinAcc (Option State) Symbol) : NA.FinAcc State Symbol where
  start := { s | some s ∈ a.start }
  Tr s x s' := a.Tr (some s) x (some s')
  accept := { s | ∃ x, a.Tr (some s) x none }

noncomputable def toOptionDA (a : NA.FinAcc State Symbol) : OptionDA (Set State) Symbol :=
  let da := a.toDAFinAcc
  { start := da.start
    tr S x :=
      let S' := da.tr S x
      open Classical in if S' ∈ da.accept then none else some S' }

end NA.FinAcc

noncomputable def DA.FinAcc.toOptionDA (a : DA.FinAcc State Symbol) :
    OptionDA (Set State) Symbol :=
  a.toOptionεNA.toNAFinAcc.ofOptionFinAcc.toOptionDA

open Acceptor in
-- open scoped NA.FinAcc in
theorem DA.FinAcc.toOptionDA_language_eq {a : DA.FinAcc State Symbol} :
    language a.toOptionDA = language a := by
  simp [toOptionDA]
  sorry

end Cslib.Automata
