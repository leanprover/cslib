/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Logics.LinearLogic.CLL.Basic
import Mathlib.Data.Multiset.Defs
import Mathlib.Data.Multiset.AddSub

namespace Cslib

universe u

variable {Atom : Type u}

namespace CLL

/-- A sequent in CLL, as a multiset. -/
abbrev MSequent (Atom) := Multiset (Proposition Atom)

/-- Checks that all propositions in `Γ` are question marks. -/
-- TODO: This and Sequent.AllQuest can probably be unified, we just need Mem.
-- TODO: This should become a Bool.
def MSequent.AllQuest (Γ : MSequent Atom) :=
  ∀ a ∈ Γ, ∃ b, a = Proposition.quest b

open Proposition in
/-- CLL sequent calculus based on `Multiset`. -/
inductive MProof : MSequent Atom → Prop where
  | ax : MProof {a, a⫠}
  | cut : MProof (a ::ₘ Γ) → MProof (a⫠ ::ₘ Δ) → MProof (Γ + Δ)
  | one : MProof {1}
  | bot : MProof Γ → MProof (⊥ ::ₘ Γ)
  | parr : MProof (a ::ₘ b ::ₘ Γ) → MProof ((a ⅋ b) ::ₘ Γ)
  | tensor : MProof (a ::ₘ Γ) → MProof (b ::ₘ Δ) → MProof ((a ⊗ b) ::ₘ (Γ + Δ))
  | oplus₁ : MProof (a ::ₘ Γ) → MProof ((a ⊕ b) ::ₘ Γ)
  | oplus₂ : MProof (b ::ₘ Γ) → MProof ((a ⊕ b) ::ₘ Γ)
  | with : MProof (a ::ₘ Γ) → MProof (b ::ₘ Γ) → MProof ((a & b) ::ₘ Γ)
  | top : MProof (⊤ ::ₘ Γ)
  | quest : MProof (a ::ₘ Γ) → MProof (ʔa ::ₘ Γ)
  | weaken : MProof Γ → MProof (ʔa ::ₘ Γ)
  | contract : MProof (ʔa ::ₘ ʔa ::ₘ Γ) → MProof (ʔa ::ₘ Γ)
  | bang {Γ : MSequent Atom} {a} : Γ.AllQuest → MProof (a ::ₘ Γ) → MProof ((!a) ::ₘ Γ)

attribute [local grind _=_] Multiset.coe_eq_coe
attribute [local grind _=_] Multiset.cons_coe
attribute [local grind] MProof

/- TODO: This is probably a general property of Multiset (for general predicates). -/
@[grind →]
lemma MSequent.allQuest_from_sequent (h : Sequent.AllQuest Γ) :
  MSequent.AllQuest (Multiset.ofList Γ) := by
  intro b hin
  specialize h b
  specialize h (Multiset.mem_coe.1 hin)
  exact h

/- `MProof` is complete for `Proof`. -/
def MProof.fromProof {Γ : Sequent Atom} (p : ⇓Γ) : MProof (Multiset.ofList Γ) := by
  induction p
  case ax =>
    constructor
  case cut a Γ Δ p q ihp ihq =>
    rw [← Multiset.cons_coe] at ihp ihq
    have icut := MProof.cut ihp ihq
    exact icut
  case exchange Γ Δ hperm p ihp =>
    grind
  case one =>
    constructor
  case bot Γ p ihp =>
    exact MProof.bot ihp
  case parr a b Γ p ihp =>
    grind
  case tensor a Γ b Δ p q ihp ihq =>
    rw [← Multiset.cons_coe] at ihp
    rw [← Multiset.cons_coe] at ihq
    apply MProof.tensor ihp ihq
  all_goals grind

end CLL

end Cslib
