/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Logics.LinearLogic.CLL.Basic

/-! # η-expansion for Classical Linear Logic (CLL) -/

namespace Cslib.CLL

universe u

variable {Atom : Type u}

attribute [local grind _=_] Multiset.coe_eq_coe
attribute [local grind _=_] Multiset.cons_coe
attribute [local grind _=_] Multiset.singleton_add
attribute [local grind =] Multiset.add_comm
attribute [local grind =] Multiset.add_assoc
attribute [local grind =] Multiset.insert_eq_cons

/-- The η-expansion of a proposition `a` is a `Proof` of `{a, a⫠}` that applies the axiom
only to atomic propositions. -/
def Proposition.expand (a : Proposition Atom) : ⇓{a, a⫠} :=
  match a with
  | atom x
    | atomDual x
    | 1
    | ⊥
    | ⊤ => Proof.ax
  | 0 =>
    Proof.top (Γ := {0})
    |> .rwConclusion (by simp only [Proposition.dual]; rfl : ⊤ ::ₘ {0} = 0⫠ ::ₘ {0})
    |> .rwConclusion (by grind : 0⫠ ::ₘ {0} = {0, 0⫠})
  | tensor a b =>
    Proof.parr (
      Proof.tensor a.expand b.expand
      |> .rwConclusion (by grind :
        ((a ⊗ b) ::ₘ ({a⫠} + {b⫠})) = (a⫠ ::ₘ b⫠ ::ₘ {a.tensor b}))
    ) |> .rwConclusion (by grind :
      ((a⫠ ⅋ b⫠) ::ₘ {a ⊗ b}) = {a ⊗ b, (a ⊗ b)⫠})
  | parr a b =>
    Proof.tensor (a := a⫠) (b := b⫠)
      (a.expand.rwConclusion (by grind : {a, a⫠} = {a⫠, a}))
      (b.expand.rwConclusion (by grind : {b, b⫠} = {b⫠, b}))
    |> .rwConclusion (by grind : (a⫠ ⊗ b⫠) ::ₘ ({a} + {b}) = a ::ₘ b ::ₘ {(a⫠.tensor b⫠)})
    |> Proof.parr
  | oplus a b =>
    Proof.with
      (a.expand.oplus₁ (b := b) |> .rwConclusion (by grind : (a ⊕ b) ::ₘ {a⫠} = a⫠ ::ₘ {a ⊕ b}))
      (b.expand.oplus₂ (a := a) |> .rwConclusion (by grind : (a ⊕ b) ::ₘ {b⫠} = b⫠ ::ₘ {a ⊕ b}))
    |> .rwConclusion (by grind : (a⫠ & b⫠) ::ₘ {a ⊕ b} = {(a ⊕ b), (a⫠ & b⫠)})
  | .with a b =>
    Proof.with
      (a⫠.expand.oplus₁ (b := b⫠) |> .rwConclusion (by grind [Proposition.dual_involution] :
        (a⫠ ⊕ b⫠) ::ₘ {a⫠⫠} = a ::ₘ {a⫠ ⊕ b⫠}))
      (b⫠.expand.oplus₂ (a := a⫠) |> .rwConclusion (by grind [Proposition.dual_involution] :
        (a⫠ ⊕ b⫠) ::ₘ {b⫠⫠} = b ::ₘ {a⫠ ⊕ b⫠}))
  | ʔa =>
    Proof.bang
      (Γ := {ʔa})
      rfl
      (a.expand.quest.rwConclusion (by grind : ʔa ::ₘ {a⫠} = a⫠ ::ₘ {ʔa}))
    |> Proof.rwConclusion (by grind : ((a⫠).bang ::ₘ {ʔa}) = {ʔa, (ʔa)⫠})
  | bang a =>
    Proof.bang
      (Γ := {ʔ(a⫠)})
      rfl
      (a⫠.expand.quest.rwConclusion (by grind : ʔa⫠ ::ₘ {a⫠⫠} = a⫠⫠ ::ₘ {ʔa⫠}))
    |> Proof.rwConclusion (by grind : ((a⫠⫠).bang ::ₘ {ʔa⫠}) = {ʔa⫠, (ʔa⫠)⫠})
    |> Proof.rwConclusion (by grind : {ʔa⫠, (ʔa⫠)⫠} = {ʔa⫠, !(a⫠⫠)})
    |> Proof.rwConclusion (by rw [Proposition.dual_involution] : {ʔa⫠, !(a⫠⫠)} = {ʔa⫠, !a})
    |> Proof.rwConclusion (by grind : {ʔa⫠, !a} = {!a, ʔa⫠})
termination_by sizeOf a
decreasing_by
  all_goals simp <;> grind


end Cslib.CLL
