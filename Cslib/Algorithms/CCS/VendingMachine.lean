/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Languages.CCS.Semantics
public import Cslib.Foundations.Semantics.LTS.Bisimulation
public import Cslib.Foundations.Semantics.LTS.TraceEq
public import Cslib.Logics.HML.Basic
public import Mathlib.Tactic.FinCases

/-! # Milner's Vending Machine

This file formalises Milner's vending machine example for CCS.

We formalise two versions:
- A machine with a deterministic LTS: `coin.(tea.VM + coffee.VM)`.
- A machine with a nondeterministic LTS: `coin.tea.VM + coin.coffee.VM`.

We then prove the classical example that the two are not bisimilar, although they are trace
equivalent.
We also show the distinction with HML: only the deterministic machine offers the choice of drink
after a coin is inserted.
-/

@[expose] public section

namespace Cslib.Algorithms.CCS.VendingMachine

open Cslib.CCS Process Act
open scoped LTS

/-! Action names. -/

/-- Insert a coin. -/
abbrev Coin := name "coin"

/-- Tea request. -/
abbrev Tea := name "tea"

/-- Coffee request. -/
abbrev Coffee := name "coffee"

/-- Constants. -/
inductive Constant
  | vm

/-- The vending machine process. -/
@[local grind =]
def vm : Process String Constant := `(CCS| const .vm)

/-! ## Deterministic vending machine -/

/-- Constant definitions: vm = coin.(tea.VM + coffee.VM) -/
@[local grind =]
def vendingDefs : Constant → Option (Process String Constant)
  | .vm => some <| `(CCS| Coin. ((Tea. const .vm) + (Coffee. const .vm)))

/-- The LTS of CCS for the deterministic vending machine. -/
abbrev ltsD := CCS.lts (defs := vendingDefs)

/-- VM can perform a coin action. -/
example : ltsD.Tr vm Coin `(CCS| (Tea. (const .vm)) + (Coffee. (const .vm))) :=
  Tr.const rfl Tr.pre

/-! ## Nondeterministic vending machine -/

/-- vm = coin.tea.VM + coin.coffee.VM -/
def vendingDefsND : Constant → Option (Process String Constant)
  | .vm => some <| `(CCS| (Coin. Tea. const .vm) + (Coin. Coffee. const .vm))

/-- The LTS of CCS for the nondeterministic vending machine. -/
abbrev ltsND := CCS.lts (defs := vendingDefsND)

open LTS LTS.IsBisimulation LTS.Bisimilarity

/-- The deterministic and nondeterministic vending machines are not bisimilar. -/
theorem vm_ltsD_ltsND_not_bisim : ¬(vm ~[ltsD, ltsND] vm) := by
  rintro ⟨r, hr, hbisim⟩
  let p₁ := `(CCS| (Tea. const Constant.vm) + (Coffee. const Constant.vm))
  let q₁ := `(CCS| Tea. const Constant.vm)
  have ltsD_vm_deterministic : ltsD.DeterministicStateLabel vm Coin := by
    grind
  have h : r p₁ q₁ :=
    match_deterministic
      hbisim hr
      ltsD_vm_deterministic
      (.const rfl .pre)
      (.const rfl (.choiceL .pre))
  have hp₁q₁ : p₁ ~[ltsD, ltsND] q₁ := by grind
  have hp₁coffee : ltsD.Tr p₁ Coffee (.const .vm) := .choiceR .pre
  grind [hp₁q₁.follow_fst]

/-! ## Trace equivalence of the two vending machines -/

/-- Every trace of the deterministic machine is a trace of the nondeterministic machine.

The statement is generalised to the states reached after a coin has been inserted, so that it can
be proved by induction on the trace: the nondeterministic machine has then already committed to a
drink, hence the disjunction. -/
private theorem traces_ltsD_subset_traces_ltsND (μs : List (Act String)) :
    (μs ∈ ltsD.traces vm → μs ∈ ltsND.traces vm) ∧
    (μs ∈ ltsD.traces `(CCS| (Tea. const .vm) + (Coffee. const .vm)) →
      μs ∈ ltsND.traces `(CCS| Tea. const .vm) ∨ μs ∈ ltsND.traces `(CCS| Coffee. const .vm)) := by
  induction μs with
  | nil => exact ⟨fun _ => ⟨_, .refl⟩, fun _ => .inl ⟨_, .refl⟩⟩
  | cons μ μs ih =>
    simp only [mem_traces_cons_iff]
    constructor
    · rintro ⟨s, htr, hs⟩
      cases htr with | «const» hdef htr =>
      cases hdef
      cases htr
      rcases ih.2 hs with h | h
      · exact ⟨_, .const rfl (.choiceL .pre), h⟩
      · exact ⟨_, .const rfl (.choiceR .pre), h⟩
    · rintro ⟨s, htr, hs⟩
      cases htr with
      | choiceL htr => cases htr; exact .inl ⟨_, .pre, ih.1 hs⟩
      | choiceR htr => cases htr; exact .inr ⟨_, .pre, ih.1 hs⟩

/-- Every trace of the nondeterministic machine is a trace of the deterministic machine.

As for `traces_ltsD_subset_traces_ltsND`, the statement is generalised to the states reached after a
coin has been inserted. -/
private theorem traces_ltsND_subset_traces_ltsD (μs : List (Act String)) :
    (μs ∈ ltsND.traces vm → μs ∈ ltsD.traces vm) ∧
    (μs ∈ ltsND.traces `(CCS| Tea. const .vm) →
      μs ∈ ltsD.traces `(CCS| (Tea. const .vm) + (Coffee. const .vm))) ∧
    (μs ∈ ltsND.traces `(CCS| Coffee. const .vm) →
      μs ∈ ltsD.traces `(CCS| (Tea. const .vm) + (Coffee. const .vm))) := by
  induction μs with
  | nil => exact ⟨fun _ => ⟨_, .refl⟩, fun _ => ⟨_, .refl⟩, fun _ => ⟨_, .refl⟩⟩
  | cons μ μs ih =>
    simp only [mem_traces_cons_iff]
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨s, htr, hs⟩
      cases htr with | «const» hdef htr =>
      cases hdef
      cases htr with
      | choiceL htr => cases htr; exact ⟨_, .const rfl .pre, ih.2.1 hs⟩
      | choiceR htr => cases htr; exact ⟨_, .const rfl .pre, ih.2.2 hs⟩
    · rintro ⟨s, htr, hs⟩
      cases htr
      exact ⟨_, .choiceL .pre, ih.1 hs⟩
    · rintro ⟨s, htr, hs⟩
      cases htr
      exact ⟨_, .choiceR .pre, ih.1 hs⟩

/-- The deterministic and nondeterministic vending machines are trace equivalent. -/
theorem vm_ltsD_ltsND_traceEq : vm ~tr[ltsD, ltsND] vm :=
  Set.ext fun μs =>
    ⟨(traces_ltsD_subset_traces_ltsND μs).1, (traces_ltsND_subset_traces_ltsD μs).1⟩

/-! ## HML properties of the two vending machines -/

open Logic Modal HML Model Proposition Satisfies
open scoped InferenceSystem

/-- HML model for the deterministic machine with no atomic propositions. -/
@[local grind =]
def modelD : HML.Model (Process String Constant) (Act String) Empty := ⟨ltsD, fun _ p => nomatch p⟩

/-- HML model for the nondeterministic machine with no atomic propositions. -/
@[local grind =]
def modelND : HML.Model (Process String Constant) (Act String) Empty :=
  ⟨ltsND, fun _ p => nomatch p⟩

/-- After inserting a coin, it is possible to choose between tea and coffee. -/
@[local grind =]
def choiceAfterCoin : HML.Proposition (Act String) Empty := d[Coin](d⟨Tea⟩⊤ ∧ d⟨Coffee⟩⊤)

theorem vm_modelD_choiceAfterCoin : ⇓HML[modelD,vm ⊨ choiceAfterCoin] := by
  have htea : ltsD.Tr `(CCS| (Tea. const .vm) + (Coffee. const .vm)) Tea vm := .choiceL .pre
  have hcoffee : ltsD.Tr `(CCS| (Tea. const .vm) + (Coffee. const .vm)) Coffee vm := .choiceR .pre
  grind [hml_dynBox_iff_forall, hml_dynDiamond_iff_exists]

theorem vm_modelND_not_choiceAfterCoin : ¬⇓HML[modelND,vm ⊨ choiceAfterCoin] := by
  have hcoin : ltsND.Tr vm Coin `(CCS| Tea. const .vm) := .const rfl (.choiceL .pre)
  grind [hml_dynBox_iff_forall, hml_dynDiamond_iff_exists]

end Cslib.Algorithms.CCS.VendingMachine
