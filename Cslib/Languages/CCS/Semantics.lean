/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Semantics.LTS.HasTau
public meta import Cslib.Foundations.Semantics.LTS.Notation
public import Cslib.Languages.CCS.Basic

/-! # Semantics of CCS

## Main definitions
- `CCS.Tr`: transition relation for CCS.
- `CCS.lts`: the `LTS` of CCS.

-/

@[expose] public section

namespace Cslib.CCS

variable
  {Name : Type u}
  {Constant : Type v}
  {defs : Constant → Option (Process Name Constant)}

open Process

/-- The transition relation for CCS. This is a direct formalisation of the one found in
[Sangiorgi2011]. -/
@[lts lts]
inductive Tr : Process Name Constant → Act Name → Process Name Constant → Prop where
  | pre : Tr (pre μ p) μ p
  | parL : Tr p μ p' → Tr (par p q) μ (par p' q)
  | parR : Tr q μ q' → Tr (par p q) μ (par p q')
  | com :
    μ.Co μ' → Tr p μ p' → Tr q μ' q' → Tr (par p q) Act.τ (par p' q')
  | choiceL : Tr p μ p' → Tr (choice p q) μ p'
  | choiceR : Tr q μ q' → Tr (choice p q) μ q'
  | res : μ ≠ Act.name a → μ ≠ Act.coname a → Tr p μ p' → Tr (res a p) μ (res a p')
  | const : defs k = some p → Tr p μ p' → Tr (const k) μ p'

instance : HasTau (Act Name) where
  τ := Act.τ

/-- A process is (successfully) terminated if it is a composition of `nil`s. -/
inductive Terminated : Process Name Constant → Prop where
  | nil : Terminated Process.nil
  | par : Terminated p → Terminated q → Terminated (par p q)
  | choice : Terminated p → Terminated q → Terminated (choice p q)
  | res : Terminated p → Terminated (res a p)

open LTS

/-- A terminated process has no outgoing transitions. -/
@[scoped grind ⇒]
theorem not_tr_of_terminated (h : Terminated p) : ¬(lts (defs := defs)).Tr p μ p' := by
  intro htr
  induction htr <;> grind [Terminated]

/-- Inversion lemma for prefix transitions. -/
@[scoped grind →]
theorem pre_tr (h : (lts (defs := defs)).Tr (pre μ p) μ' p') : μ = μ' ∧ p = p' := by
  cases h
  simp

/-- Inversion lemma for constant transitions. -/
@[scoped grind →]
theorem const_tr (h : (lts (defs := defs)).Tr (const k) μ p') :
    ∃ p, defs k = some p ∧ (lts (defs := defs)).Tr p μ p' := by
  cases h
  case const p hdef htr =>
    exists p

/-- Prefixes are deterministic. -/
@[scoped grind .]
theorem pre_deterministicState : DeterministicState (lts (defs := defs)) (pre μ p) := by
  grind

/-- Constants are deterministic if their definition is deterministic. -/
@[scoped grind .]
theorem const_deterministicStateLabel (hdef : defs k = some p)
    (h : DeterministicStateLabel (lts (defs := defs)) p μ) :
    DeterministicStateLabel (lts (defs := defs)) (const k) μ := by
  intro p₁ p₂ h₁ h₂
  cases h₁
  cases h₂
  case const.const q₁ hdef₁ htr₁ q₂ hdef₂ htr₂ =>
    have hq₁ : q₁ = p := by grind only
    have hq₂ : q₂ = p := by grind only
    rw [hq₁] at htr₁
    rw [hq₂] at htr₂
    apply h p₁ p₂ htr₁ htr₂

/-- Restriction is deterministic if its subterm is deterministic. -/
@[scoped grind .]
theorem res_deterministicStateLabel
    (h : DeterministicStateLabel (lts (defs := defs)) p μ) :
    DeterministicStateLabel (lts (defs := defs)) (res μ' p) μ := by
  intro p₁ p₂ h₁ h₂
  cases h₁
  cases h₂
  case res.res q₁ h₁ h₂ htr₁ q₂ h₃ h₄ htr₂ =>
    have hq₁q₂ : q₁ = q₂ := by
      apply h _ _ htr₁ htr₂
    rw [hq₁q₂]

end Cslib.CCS
