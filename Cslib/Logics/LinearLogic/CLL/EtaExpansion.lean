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
    Proof.top (Γ := {0}).rwConclusion (by grind)
  | tensor a b =>
    Proof.tensor a.expand b.expand
    |> .rwConclusion (by grind)
    |> Proof.parr
    |> .rwConclusion (by grind :
      ((a⫠ ⅋ b⫠) ::ₘ {a ⊗ b}) = {a ⊗ b, (a ⊗ b)⫠})
  | parr a b =>
    Proof.tensor (a := a⫠) (b := b⫠)
      (a.expand.rwConclusion (by grind : {a, a⫠} = {a⫠, a}))
      (b.expand.rwConclusion (by grind : {b, b⫠} = {b⫠, b}))
    |> .rwConclusion (by grind)
    |> Proof.parr
  | oplus a b =>
    Proof.with
      (a.expand.oplus₁ (b := b) |> .rwConclusion (by grind))
      (b.expand.oplus₂ (a := a) |> .rwConclusion (by grind))
    |> .rwConclusion (by grind : (a⫠ & b⫠) ::ₘ {a ⊕ b} = {(a ⊕ b), (a⫠ & b⫠)})
  | .with a b =>
    Proof.with
      (a⫠.expand.oplus₁ (b := b⫠) |> .rwConclusion (by grind))
      (b⫠.expand.oplus₂ (a := a⫠) |> .rwConclusion (by grind))
  | ʔa =>
    Proof.bang
      (Γ := {ʔa})
      rfl
      (a.expand.quest.rwConclusion (by grind : ʔa ::ₘ {a⫠} = a⫠ ::ₘ {ʔa}))
    |> Proof.rwConclusion (by grind)
  | bang a =>
    Proof.bang
      (Γ := {ʔ(a⫠)})
      rfl
      (a⫠.expand.quest.rwConclusion (by grind : ʔa⫠ ::ₘ {a⫠⫠} = a⫠⫠ ::ₘ {ʔa⫠}))
    |> Proof.rwConclusion (by grind)
termination_by a
decreasing_by
  all_goals simp <;> grind


end Cslib.CLL
