/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Logics.LinearLogic.CLL.Basic
public import Cslib.Foundations.Logic.InferenceSystem

@[expose] public section

/-! # Multiplicative Classical Linear Logic (MLL)

Multiplicative classical linear logic, defined as a fragment of classical linear logic by means of
`Subtype`.

This file serves as the reference example of how to define a fragment of an inference system
through tagging of `InferenceSystem` and `Subtype`, following the next recipe. It is a work in
progress: the recipe will evolve together with how the Lean and CSLib ecosystems can
deal with this general problem.

1. Define predicates for restricting relevant types to the fragment, here `IsMLL` for propositions
(`CLL.Proposition`) and proofs (`CLL.Proof`). This part lives under the namespace of the original
system (here `Cslib.Logic.CLL`).
2. Define the types in the fragment -- here `MLL.Proposition` and `MLL.Proof` -- as abbreviations of
subtypes. This part lives under the namespace of the fragment (here `Cslib.Logic.MLL`).

We also call the first part the 'unbundled part' and the second the 'bundled part'.

This recipe has the advantage that any value (propositions, proofs, etc.) in the fragment is
coerciable into the original system for free through `Subtype`.

The main disadvantage is that the fragment does not have its own inductives, so case analysis
requires carrying around the restricting predicate(s) as parameters to discharge irrelevant cases
from the original system.
This can be elegantly managed by unbundling the predicate right away, so that `match` (or similar)
can automatically eliminate irrelevant cases.
For example, the following definition checks that an MLL proof is cut-free:

```
/-- An MLL proof is cut-free if it does not contain any applications of rule cut. -/
def Proof.cutFree {Γ : Sequent Atom} (p : MLL⇓Γ) : Bool :=
  go p.val p.property
where go {Γ : CLL.Sequent Atom} (p : ⇓Γ) (hp : p.IsMLL) : Bool :=
  match p, hp with
  | .ax, _ => true
  | .bot p, hp | .parr p, hp => go p hp
  | .one, _ => true
  | .cut _ _, _ => false
  | .tensor p q, hp => go p hp.left && go q hp.right
```
-/

namespace Cslib.Logic.CLL

/-- A proposition is in the multiplicative fragment of CLL. -/
@[simp]
def Proposition.IsMLL : Proposition Atom → Prop
  | atom _ | atomDual _ | one | bot => True
  | tensor a b | parr a b => a.IsMLL ∧ b.IsMLL
  | _ => False

/-- Recursor for MLL propositions. -/
@[induction_eliminator, cases_eliminator, elab_as_elim]
def Proposition.IsMLL.rec
    {motive : {a : Proposition Atom} → (h : a.IsMLL) → Sort u}
    (atom : ∀ x : Atom, motive (a := .atom x) (by simp))
    (atomDual : ∀ x : Atom, motive (a := .atomDual x) (by simp))
    (one : motive (a := .one) (by simp))
    (bot : motive (a := .bot) (by simp))
    (tensor : ∀ (a b : Proposition Atom) {ha : a.IsMLL} {hb : b.IsMLL},
      motive ha → motive hb → motive (a :=.tensor a b) (by simp [ha,hb]))
    (parr : ∀ (a b : Proposition Atom) {ha : a.IsMLL} {hb : b.IsMLL},
      motive ha → motive hb → motive (a := .parr a b) (by simp [ha,hb]))
    {a : Proposition Atom} (h : a.IsMLL) : motive (a := a) h :=
  match a, h with
  | .atom x, _ => atom x
  | .atomDual x, _ => atomDual x
  | .one, _ => one
  | .bot, _ => bot
  | .tensor a b, ⟨ha, hb⟩ =>
    tensor a b (ha := ha) (hb := hb)
      (Proposition.IsMLL.rec atom atomDual one bot tensor parr ha)
      (Proposition.IsMLL.rec atom atomDual one bot tensor parr hb)
  | .parr a b, ⟨ha, hb⟩ =>
      parr a b
        (Proposition.IsMLL.rec atom atomDual one bot tensor parr ha)
        (Proposition.IsMLL.rec atom atomDual one bot tensor parr hb)
  | .zero, h | .top, h | .oplus _ _, h | .with _ _, h
    | .bang _, h | .quest _, h => nomatch h

/-- Duality in MLL stays in MLL. -/
@[scoped grind →]
theorem Proposition.isMLL_dual {a : Proposition Atom} (ha : a.IsMLL) : a⫠.IsMLL := by
  induction ha <;> grind [dual, IsMLL]

/-- A multiplicative propositional context. -/
@[simp]
def Proposition.Context.IsMLL : Context Atom → Prop
  | hole => True
  | tensorL a b | tensorR a b | parrL a b | parrR a b => a.IsMLL ∧ b.IsMLL
  | _ => False

/-- Filling a multiplicative propositional context with a multiplicative proposition stays in MLL.
-/
theorem Proposition.Context.isMLL_fill {c : CLL.Proposition.Context Atom} {a : CLL.Proposition Atom}
    (hc : c.IsMLL) : (c.fill a).IsMLL ↔ a.IsMLL := by
  induction c with
  | hole => grind [fill]
  | tensorL | tensorR | parrL | parrR => grind [fill, IsMLL, Proposition.IsMLL]
  | _ => grind [IsMLL]

/-- A multiplicative sequent. -/
@[scoped grind =, simp]
def Sequent.IsMLL (Γ : Sequent Atom) := ∀ a ∈ Γ, a.IsMLL

open scoped Logic.InferenceSystem

/-- A proof is in MLL. -/
@[simp]
def Proof.IsMLL {Γ : Sequent Atom} : ⇓Γ → Prop
  | ax (a := a) | bot a | parr a => a.IsMLL
  | cut p q | tensor p q => p.IsMLL ∧ q.IsMLL
  | one => True
  | _ => False

/-- Recursor for MLL derivations. -/
@[induction_eliminator, cases_eliminator, elab_as_elim]
def Proof.IsMLL.rec
    {motive : {Γ : Sequent Atom} → {p : Proof Γ} → (h : p.IsMLL) → Sort u}
    (ax : ∀ {a : Proposition Atom} {ha : a.IsMLL}, @motive {a, a⫠} .ax (by simp [ha]))
    (one : @motive {Proposition.one} .one (by simp))
    (bot : ∀ {Γ : Sequent Atom} (p : Proof Γ) {hp : p.IsMLL},
      @motive Γ p hp → @motive (.bot ::ₘ Γ) (.bot p) (by simp [hp]))
    (tensor : ∀ {a b : Proposition Atom} {Γ Δ : Sequent Atom}
      (p : Proof (a ::ₘ Γ)) (q : Proof (b ::ₘ Δ)) {hp : p.IsMLL} {hq : q.IsMLL},
      @motive (a ::ₘ Γ) p hp → @motive (b ::ₘ Δ) q hq →
      @motive ((a ⊗ b) ::ₘ (Γ + Δ)) (.tensor p q) (by simp [hp, hq]))
    (parr : ∀ {a b : Proposition Atom} {Γ : Sequent Atom}
      (p : Proof (a ::ₘ b ::ₘ Γ)) {hp : p.IsMLL},
      @motive (a ::ₘ b ::ₘ Γ) p hp → @motive ((a ⅋ b) ::ₘ Γ) (.parr p) (by simp [hp]))
    (cut : ∀ {a : Proposition Atom} {Γ Δ : Sequent Atom}
      (p : Proof (a ::ₘ Γ)) (q : Proof (a⫠ ::ₘ Δ)) {hp : p.IsMLL} {hq : q.IsMLL},
      @motive (a ::ₘ Γ) p hp → @motive (a⫠ ::ₘ Δ) q hq →
      @motive (Γ + Δ) (.cut p q) (by simp [hp, hq]))
    {Γ : Sequent Atom} {p : Proof Γ} (h : p.IsMLL) : @motive Γ p h :=
  match p, h with
  | .ax (a := a), hp => @ax a (by simp only [IsMLL] at hp; exact hp)
  | .one, _ => one
  | .bot p (Γ := Γ), hp => @bot Γ p hp (IsMLL.rec ax one bot tensor parr cut (p := p) hp)
  | .tensor (a := a) (b := b) (Γ := Γ) (Δ := Δ) p q, h =>
    @tensor a b Γ Δ p q h.left h.right
      (IsMLL.rec ax one bot tensor parr cut h.left)
      (IsMLL.rec ax one bot tensor parr cut h.right)
  | .parr (a := a) (b := b) (Γ := Γ) p, hp =>
    @parr a b Γ p hp
      (IsMLL.rec ax one bot tensor parr cut (p := p) hp)
  | .cut (a := a) (Γ := Γ) (Δ := Δ) p q, h =>
    @cut a Γ Δ p q h.left h.right
      (IsMLL.rec ax one bot tensor parr cut h.left)
      (IsMLL.rec ax one bot tensor parr cut h.right)

open scoped Sequent Proposition in
/-- A proof in the MLL fragment can only prove MLL sequents. -/
theorem Proof.isMLL_sequent {Γ : Sequent Atom} {p : ⇓Γ} (h : p.IsMLL) : Γ.IsMLL := by
  -- This should be simpler, grind seems to have some trouble.
  induction h
  case ax =>
    grind [Proof.IsMLL, Multiset.insert_eq_cons, Multiset.mem_singleton]
  case one =>
    simp [Sequent.IsMLL, Proposition.IsMLL]
  case parr | tensor | cut => grind [Proposition.IsMLL, Proof.IsMLL]
  case bot Γ p ih =>
    simp
    grind [Proof.IsMLL]

/-- If a CLL derivation is cut-free and concludes an MLL sequent, then it is an MLL derivation. -/
theorem Proof.isMLL_cutFree {Γ : Sequent Atom} (p : ⇓Γ) (hΓ : Γ.IsMLL)
    (hp : p.cutFree) : p.IsMLL := by
  induction p
  case ax a =>
    simp only [Sequent.IsMLL, Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton,
      forall_eq_or_imp, forall_eq] at hΓ
    simp [hΓ]
  case one => simp
  case bot _ _ ih =>
    simp only [Sequent.IsMLL, Multiset.mem_cons, forall_eq_or_imp, Proposition.IsMLL,
      true_and] at hΓ
    specialize ih hΓ hp
    grind only [IsMLL]
  case parr a b Γ p ih =>
    simp only [Sequent.IsMLL, Multiset.mem_cons, forall_eq_or_imp, Proposition.IsMLL] at hΓ
    specialize ih (by grind [Sequent.IsMLL]) hp
    grind only [IsMLL]
  case tensor a b Γ Δ p q ihp ihq =>
    simp only [Sequent.IsMLL, Multiset.mem_cons, forall_eq_or_imp, Proposition.IsMLL] at hΓ
    specialize ihp (by grind [Sequent.IsMLL])
    specialize ihq (by grind [Sequent.IsMLL])
    grind only [cutFree, IsMLL]
  case oplus₁ | oplus₂ | «with» | top | quest | contract | weaken | bang => simp at hΓ
  case cut => simp [cutFree] at hp

/-- MLL derivations. -/
abbrev MLL.Proof (Γ : CLL.Sequent Atom) := {p : ⇓Γ // p.IsMLL}

/-- Tag for the MLL inference system. -/
inductive MLL

/-- MLL inference system. -/
instance : InferenceSystem MLL (Sequent Atom) := ⟨MLL.Proof⟩

namespace MLL

open InferenceSystem

@[match_pattern]
def Proof.ax {a : Proposition Atom} (h : a.IsMLL) : Proof {a, a⫠} :=
  ⟨CLL.Proof.ax, by simp [h, Proof.IsMLL]⟩

@[match_pattern]
def Proof.one : Proof (Atom := Atom) {Proposition.one} :=
  ⟨CLL.Proof.one, by simp [Proof.IsMLL]⟩

@[match_pattern]
def Proof.bot {Γ : Sequent Atom} (p : Proof Γ) : Proof (⊥ ::ₘ Γ) :=
  ⟨CLL.Proof.bot p, by simp [Proof.IsMLL, p.property]⟩

@[match_pattern]
def Proof.parr {Γ : Sequent Atom} {a b : Proposition Atom} (p : Proof (a ::ₘ b ::ₘ Γ)) :
    Proof ((a ⅋ b) ::ₘ Γ) :=
  ⟨CLL.Proof.parr p, by simp [Proof.IsMLL, p.property]⟩

@[match_pattern]
def Proof.tensor {Γ Δ : Sequent Atom} {a b : Proposition Atom}
    (p : Proof (a ::ₘ Γ)) (q : Proof (b ::ₘ Δ)) :
    Proof ((a ⊗ b) ::ₘ (Γ + Δ)) :=
  ⟨CLL.Proof.tensor p q, by simp [Proof.IsMLL, p.property, q.property]⟩

/-- MLL proofs derive only MLL sequents. -/
theorem Proof.isMLL_sequent {Γ : Sequent Atom} (p : MLL⇓Γ) : Γ.IsMLL :=
  CLL.Proof.isMLL_sequent p.property

end MLL

def Proof.cutFreeToMLL {Γ : Sequent Atom} (p : ⇓Γ) (hΓ : Γ.IsMLL) (hp : p.cutFree) : MLL⇓Γ :=
  ⟨p, CLL.Proof.isMLL_cutFree p hΓ hp⟩

instance {Γ : Sequent Atom} : Coe (MLL⇓Γ) (⇓Γ) where
  coe p := p.val

def MLL.Proof.cutFree {Γ : Sequent Atom} (p : MLL⇓Γ) : Bool :=
  match p with
  | ax h | one => true
  | bot p => p.cutFree
  | parr p => p.cutFree
  | tensor p q => p.cutFree && q.cutFree
  | cut => false

end Cslib.Logic.CLL
