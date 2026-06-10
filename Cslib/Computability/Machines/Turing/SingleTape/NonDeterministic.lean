/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Data.Relation
public import Cslib.Computability.Automata.NA.Basic
public import Cslib.Computability.Automata.EpsilonNA.Basic
public import Cslib.Computability.Automata.EpsilonNA.ToNA
public import Cslib.Computability.Automata.EpsilonNA.ToSingleAccept
public import Cslib.Foundations.Data.BiTape
public import Cslib.Foundations.Semantics.LTS.Map
public import Cslib.Computability.Machines.Turing.SingleTape.Defs

/-! # Single-Tape Nondeterministic Turing Machines (NTMs)

Nondeterministic Turing Machines (NTMs), defined as nondeterministic automata (`NA`) that act on a
bidirectional tape (`BiTape`).
-/

@[expose] public section

namespace Cslib.Computability.Turing.SingleTape

open Automata

/-- A (single-tape) Nondeterministic Turing Machine (NTM) is a nondeterministic automaton equipped
with a set of accepting halting states. -/
structure SingleTapeNTM (State Symbol : Type*)
    extends NA State (TrLabel Symbol) where
  /-- The set of accepting states. -/
  accept : Set State
  /-- Proof that all accepting states are halting states. -/
  accept_halting (hmem : s ∈ accept) : ¬∃ μ s', Tr s μ s'

variable {State Symbol : Type*}

namespace SingleTapeNTM

/-- An NTM yields a small-step operational semantics on configurations, which codifies an execution
step. -/
@[scoped grind =]
def Red (m : SingleTapeNTM State Symbol)
    (c c' : Cfg State Symbol) : Prop :=
  ∃ μ, m.Tr c.state μ c'.state ∧ -- The controller can perform the move
    μ.read = c.tape.head ∧ -- The tape has the expected symbol to be read
    c'.tape = (c.tape.write μ.write).optionMove μ.move -- Write effect on the tape

@[scoped grind =]
theorem red_tr {m : SingleTapeNTM State Symbol} :
    m.Red c c' ↔
    ∃ μ, m.Tr c.state μ c'.state ∧
      μ.read = c.tape.head ∧
      c'.tape = (c.tape.write μ.write).optionMove μ.move := by
  grind only [Red]

/-- Multistep execution of an NTM, defined as the reflexive and transitive closure of one-step
execution.
-/
@[scoped grind =]
def MRed (m : SingleTapeNTM State Symbol) :=
  Relation.ReflTransGen m.Red

/-- An NTM is an acceptor of finite lists of symbols. -/
@[simp, scoped grind =]
instance : Acceptor (SingleTapeNTM State Symbol) Symbol where
  Accepts (m : SingleTapeNTM State Symbol) (xs : List Symbol) :=
    ∃ s ∈ m.start, ∃ c', c'.state ∈ m.accept ∧ m.MRed (Cfg.mk₁ s xs) c'

section Regular

open scoped Cslib.Automata.εNA.FinAcc

/-- Checks that a `TrLabel` is of the form expected by the NTM encoding of a single-accept
`εNA.FinAcc`. -/
@[scoped grind =]
def fromεNAFinAcc.mapSymbol (x : Symbol) : TrLabel Symbol := ⟨some x, none, Turing.Dir.right⟩

open fromεNAFinAcc

@[scoped grind .]
theorem fromεNAFinAcc.mapSymbol_injective {Symbol} :
    Function.Injective (mapSymbol (Symbol := Symbol)) := by
  grind only [Function.Injective, mapSymbol]

/-- Checks that a `List TrLabel` is of the form expected by the NTM encoding of a single-accept
`εNA.FinAcc`. -/
@[scoped grind =]
def fromεNAFinAcc.mapSymbolList (xs : List Symbol) := xs.map mapSymbol

@[scoped grind =]
theorem fromεNAFinAcc.mapSymbolList_nil : mapSymbolList ([] : List Symbol) = [] := by
  simp [mapSymbolList]

@[scoped grind =]
theorem fromεNAFinAcc.mapSymbolList_cons :
    mapSymbolList (x :: xs) = mapSymbol x :: mapSymbolList xs := by
  grind only [mapSymbolList, = List.map_cons]

@[scoped grind .]
theorem fromεNAFinAcc.mapSymbolList_injective {Symbol} :
    Function.Injective (mapSymbolList (Symbol := Symbol)) := by
  apply List.map_injective_iff.mpr (mapSymbol_injective (Symbol := Symbol))

open Acceptor εNA.FinAcc NA.FinAcc
open scoped LTS LTS.MTr

/-- Transforms an `εNA.FinAcc` into a single-tape NTM. -/
def fromεNAFinAcc (a : εNA.FinAcc State Symbol) : SingleTapeNTM (Option State ⊕ Unit) Symbol :=
  let aSA := a.toSingleAccept.toNAFinAcc
  {
    start := {.inr ()}
      -- Sum.inl '' aSA.start
    accept := {.inl none}
    Tr
      | .inl s, μ, .inl s' => ∃ x, μ = mapSymbol x ∧ aSA.Tr s x s'
      | .inr (), ⟨none, none, none⟩, .inl none => none ∈ aSA.accept
      | .inr (), ⟨none, none, none⟩, .inl s => s ∈ aSA.start
      | _, _, _ => False
    -- Tr s μ s' := ∃ x, μ = mapSymbol x ∧ aSA.Tr s x s'
    accept_halting := by
      intro s hs h
      have hsnone : s = .inl none := by grind
      rcases h with ⟨μ, s', h⟩
      split at h
      case h_1 =>
        rcases h with ⟨x, hμ, h⟩
        cases h
        case tr =>
          grind only [→ toSingleAccept_τSTr_antiDerivative_none, ← toSingleAccept_not_tr_none]
      case h_2 | h_3 | h_4 => grind only
  }

@[scoped grind →]
theorem fromεNAFinAcc_tr_not_inr {a : εNA.FinAcc State Symbol}
    (h : (fromεNAFinAcc a).Tr us μ us') : ∃ s', us' = .inl s' := by
  grind only [fromεNAFinAcc]

@[scoped grind =]
theorem fromεNAFinAcc_tr_iff {a : εNA.FinAcc State Symbol} :
    (fromεNAFinAcc a).Tr (.inl s) μ (.inl s') ↔
    ∃ x, μ = mapSymbol x ∧ a.toSingleAccept.toNAFinAcc.Tr s x s' := by
  apply Iff.intro <;> intro h
  case mp =>
    grind only [→ LTS.MTr.single, fromεNAFinAcc]
  case mpr =>
    grind only [fromεNAFinAcc]

@[scoped grind =]
theorem fromεNAFinAcc_mTr_iff {a : εNA.FinAcc State Symbol} :
    (fromεNAFinAcc a).MTr (.inl s) μs (.inl s') ↔
    ∃ xs, μs = mapSymbolList xs ∧ a.toSingleAccept.toNAFinAcc.MTr s xs s' := by
  induction μs generalizing s
  case nil => grind [=_ mapSymbolList_nil]
  case cons μ μs ih =>
    apply Iff.intro <;> intro h
    case mp =>
      cases h
      case stepL ousb htr hmtr =>
        have ⟨sb, housb⟩ : ∃ sb, ousb = .inl sb := by grind
        specialize ih (s := sb)
        have ⟨xs, hμs⟩ : ∃ xs, μs = mapSymbolList xs := by grind only
        have ⟨x, hμ⟩ : ∃ x, μ = mapSymbol x := by grind only [= fromεNAFinAcc_tr_iff]
        exists x :: xs
        rw [housb] at htr hmtr
        apply And.intro (by grind only [mapSymbolList_cons])
        have ⟨x', hx', htr'⟩ := fromεNAFinAcc_tr_iff.mp htr
        rw [show x' = x by grind only [mapSymbol_injective]] at htr'
        apply LTS.MTr.stepL htr'
        have ⟨xs', hxs', hmtr'⟩ := ih.mp hmtr
        grind only [mapSymbolList_injective]
    case mpr =>
      rcases h with ⟨μs', hl, h⟩
      cases h
      case refl =>
        grind only [= mapSymbolList_nil]
      case stepL x osb xs htr hmtr =>
        have hμ : μ = mapSymbol x := by grind only [= mapSymbolList_cons]
        have htr' := fromεNAFinAcc_tr_iff.mpr ⟨x, hμ, htr⟩
        apply LTS.MTr.stepL htr' (by grind only [= mapSymbolList_cons])

@[scoped grind =]
theorem fromεNAFinAcc_accepts_nil_iff {a : εNA.FinAcc State Symbol} :
    Accepts (fromεNAFinAcc a) [] ↔
    (fromεNAFinAcc a).Tr (.inr ()) ⟨none, none, none⟩ (.inl none) := by
  apply Iff.intro <;> intro h
  case mp =>
    rcases h with ⟨asdf, asdf ,wer ,g ⟩



@[scoped grind =]
theorem fromεNAFinAcc_accepts_iff_mTr {a : εNA.FinAcc State Symbol} {xs : List Symbol}
    (hxs : xs ≠ []) :
    Accepts (fromεNAFinAcc a) xs ↔
    ∃ s ∈ a.toSingleAccept.toNAFinAcc.start, ∃ μs : List (TrLabel Symbol),
      μs = mapSymbolList xs ∧ (fromεNAFinAcc a).MTr (.inl s) μs (.inl none) := by
  apply Iff.intro <;> intro h
  case mp =>
    rcases h with ⟨s, hs, c, hc, hmred⟩
    induction xs
    case nil =>
      grind
      cases hmred using Relation.ReflTransGen.head_induction_on
      case refl =>
        grind
      case head cb h₁ h₂ h₃ =>
        rcases h₂ with ⟨μ, htr, hμ, hcb⟩
        rcases htr with ⟨x, hμx, htr⟩
        rw [hμx] at hμ
        contradiction
    case cons x xs ih =>

      cases hmred using Relation.ReflTransGen.head_induction_on
      case refl =>
        cases hc
        have := fromεNAFinAcc.accept_halting
        grind [SingleTapeNTM.accept_halting]
      case head cb h₁ h₂ h₃ =>
        rcases h₂ with ⟨μ, htr, hμ, hcb⟩
        rcases htr with ⟨x, hμx, htr⟩
        rw [hμx] at hμ
        contradiction
      sorry

-- @[scoped grind .]
-- theorem fromεNAFinAcc_accepts_iff_mTr {a : εNA.FinAcc State Symbol} {xs : List Symbol} :
--     Accepts (fromεNAFinAcc a) xs ↔
--     ∃ s ∈ (fromεNAFinAcc a).start, ∃ μs : List (TrLabel Symbol),
--       IsEncLabelList μs ∧ (μs.map TrLabel.read).filter Option.isSome = xs.map Option.some ∧
--       (fromεNAFinAcc a).MTr s μs none := by
--   apply Iff.intro <;> intro h
--   case mp =>
--     induction xs
--     case nil =>
--       match h with
--       | .intro s ⟨hs, c, hc, h⟩ =>
--         exists s
--         apply And.intro hs
--         exists []
--         apply And.intro (by trivial)
--         apply And.intro (by grind)

--         sorry

--       contradiction
--     case cons x xs ih =>

--       rcases h with ⟨s, hs, c', hc', h⟩
--       exists s; apply And.intro hs

--       cases h
--     case refl =>
--       exists s; apply And.intro hs
--       simp [Cfg.mk₁] at hc'

--       simp
--       sorry
--     sorry
--   sorry
--   simp [fromεNAFinAcc]

-- lemma fromεNAFinAcc_toSingleAccept_language_eq {a : εNA.FinAcc State Symbol} :
--     language (fromεNAFinAcc a) = language a.toSingleAccept := by
--   ext xs
--   simp only [Acceptor.mem_language]
--   -- rw [fromεNAFinAcc_accepts_iff_mTr]
--   apply Iff.intro <;> intro h
--   case mp =>
--     rcases h with ⟨s, hs, c', hc', hmred⟩

--     induction hmred
--     case refl =>
--       exists s; apply And.intro (by grind only [fromεNAFinAcc])
--       simp only [Cfg.mk₁] at hc'
--       exists s; apply And.intro hc'


--       sorry
--   sorry

end Regular

end SingleTapeNTM

end Cslib.Computability.Turing.SingleTape
