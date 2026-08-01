/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Languages.CCS.Semantics
public import Cslib.Foundations.Semantics.LTS.Bisimulation
public import Cslib.Foundations.Semantics.LTS.TraceEq
public import Mathlib.Tactic.FinCases

/-! # Milner's Vending Machine

This file formalises Milner's vending machine example for CCS.

We formalise two versions:
- A machine with a deterministic LTS: `coin.(tea.VM + coffee.VM)`.
- A machine with a nondeterministic LTS: `coin.tea.VM + coin.coffee.VM`.

We then prove the classical example that the two are not bisimilar.

Future work on proving that the two vending machines are trace equivalent would be
welcome.
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
def vm : Process String Constant := const .vm

/-! ## Deterministic vending machine -/

/-- Constant definitions: vm = coin.(tea.VM + coffee.VM) -/
@[local grind =]
def vendingDefs : Constant → Option (Process String Constant)
  | .vm => some <| pre Coin (choice (pre Tea (const .vm)) (pre Coffee (const .vm)))

/-- The LTS of CCS for the deterministic vending machine. -/
abbrev ltsD := CCS.lts (defs := vendingDefs)

/-- VM can perform a coin action. -/
example : ltsD.Tr vm Coin (choice (pre Tea (const .vm)) (pre Coffee (const .vm))) :=
  Tr.const rfl Tr.pre

/-! ## Nondeterministic vending machine -/

/-- vm = coin.tea.VM + coin.coffee.VM -/
def vendingDefsND : Constant → Option (Process String Constant)
  | .vm => some <| (choice (pre Coin (pre Tea (const .vm))) (pre Coin (pre Coffee (const .vm))))

/-- The LTS of CCS for the nondeterministic vending machine. -/
abbrev ltsND := CCS.lts (defs := vendingDefsND)

open LTS LTS.IsBisimulation LTS.Bisimilarity

/-- The deterministic and nondeterministic vending machines are not bisimilar. -/
theorem vm_ltsD_ltsND_not_bisim : ¬(vm ~[ltsD, ltsND] vm) := by
  rintro ⟨r, hr, hbisim⟩
  let p₁ := (choice (pre Tea (const Constant.vm)) (pre Coffee (const Constant.vm)))
  let q₁ := (pre Tea (const Constant.vm))
  have ltsD_vm_deterministic : ltsD.DeterministicStateLabel vm Coin := by
    intro _ _ htr₁ htr₂
    grind [const_tr htr₁, const_tr htr₂]
  have h : r p₁ q₁ :=
    match_deterministic
      hbisim hr
      ltsD_vm_deterministic
      (.const rfl .pre)
      (.const rfl (.choiceL .pre))
  have hp₁q₁ : p₁ ~[ltsD, ltsND] q₁ := by grind
  have hp₁coffee : ltsD.Tr p₁ Coffee (const Constant.vm) := .choiceR .pre
  grind [hp₁q₁.follow_fst]

end Cslib.Algorithms.CCS.VendingMachine
