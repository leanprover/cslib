/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Logics.LinearLogic.CLL.Basic

@[expose] public section

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
@[scoped grind =]
def Proposition.expand (a : Proposition Atom) : ⇓{a, a⫠} :=
  match a with
  | atom x
    | atomDual x => Proof.ax
  | 1 =>
    Proof.one |> Proof.bot
    |> .rwConclusion (by rw [show ⊥ = 1⫠ by rfl])
    |> .rwConclusion (by grind : 1⫠ ::ₘ {1} = {1, 1⫠})
  | ⊥ =>
    Proof.one |> Proof.bot
  | ⊤ => Proof.top
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

/-- A `Proof` has only atomic axioms if all its instances of the axiom treat atomic propositions. -/
@[scoped grind =]
def Proof.onlyAtomicAxioms (p : ⇓Γ) : Bool :=
  match p with
  | @ax _ a => (a matches Proposition.atom _) || (a matches Proposition.atomDual _)
  | cut p q => p.onlyAtomicAxioms && q.onlyAtomicAxioms
  | one => true
  | bot p => p.onlyAtomicAxioms
  | parr p => p.onlyAtomicAxioms
  | tensor p q => p.onlyAtomicAxioms && p.onlyAtomicAxioms
  | oplus₁ p => p.onlyAtomicAxioms
  | oplus₂ p => p.onlyAtomicAxioms
  | .with p q => p.onlyAtomicAxioms && q.onlyAtomicAxioms
  | top => true
  | quest p => p.onlyAtomicAxioms
  | weaken p => p.onlyAtomicAxioms
  | contract p => p.onlyAtomicAxioms
  | bang _ p => p.onlyAtomicAxioms

/-- `Proof.onlyAtomicAxioms` is preserved by `Proof.rwConclusion`. -/
theorem Proof.onlyAtomicAxioms_rwConclusion {heq : Γ = Δ} {p : ⇓Γ} (h : p.onlyAtomicAxioms) :
  (p.rwConclusion heq).onlyAtomicAxioms := by grind

open Proposition Proof in
@[local grind →]
private lemma Proof.expand_onlyAtomicAxioms_dual {a : Proposition Atom} :
    a.expand.onlyAtomicAxioms → a⫠.expand.onlyAtomicAxioms := by
  induction a <;> grind

open Proposition Proof in
/-- η-expansion is correct: the proof returned by η-expansion contains only atomic axioms. -/
theorem Proof.expand_onlyAtomicAxioms (a : Proposition Atom) : a.expand.onlyAtomicAxioms := by
  induction a <;> grind [onlyAtomicAxioms_rwConclusion]

end Cslib.CLL
