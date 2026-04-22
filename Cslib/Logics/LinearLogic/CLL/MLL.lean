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

This file also serves as the reference example of how to define a fragment of an inference system
through `Subtype`, following the next recipe.

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
/-- A proof is cut-free if it does not contain any applications of rule cut. -/
def Proof.cutFree {Γ : Sequent Atom} (p : ⇓Γ) : Bool :=
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
/-- An MLL proof can only prove MLL sequents. -/
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

end Cslib.Logic.CLL

namespace Cslib.Logic.MLL

/-- MLL propositions. -/
abbrev Proposition (Atom : Type u) := {a : CLL.Proposition Atom // a.IsMLL}

/-- Propositional duality in MLL. -/
abbrev Proposition.dual (a : Proposition Atom) : Proposition Atom where
  val := a.val.dual
  property := CLL.Proposition.isMLL_dual a.property

@[inherit_doc] scoped postfix:max "⫠" => Proposition.dual

/-- Atom in MLL. -/
@[match_pattern]
def Proposition.atom (x : Atom) : Proposition Atom := ⟨.atom x, by simp⟩

/-- Atom dual in MLL. -/
@[match_pattern]
def Proposition.atomDual (x : Atom) : Proposition Atom := ⟨.atomDual x, by simp⟩

/-- `1` in MLL. -/
@[match_pattern]
def Proposition.one : Proposition Atom := ⟨.one, by simp⟩

/-- `⊥` in MLL. -/
@[match_pattern]
def Proposition.bot : Proposition Atom := ⟨.bot, by simp⟩

/-- `a ⊗ b` in MLL. -/
@[match_pattern]
def Proposition.tensor (a b : Proposition Atom) : Proposition Atom :=
  ⟨CLL.Proposition.tensor a b, by simp [a.2, b.2]⟩

/-- `a ⅋ b` in MLL. -/
@[match_pattern]
def Proposition.parr (a b : Proposition Atom) : Proposition Atom :=
  ⟨CLL.Proposition.parr a b, by simp [a.2, b.2]⟩

/-- Recursor for bundled MLL propositions. -/
@[induction_eliminator, cases_eliminator, elab_as_elim]
abbrev Proposition.rec (a : Proposition Atom) :=
  @CLL.Proposition.IsMLL.rec (a := a.val) (h := a.property)

/-- MLL propositional contexts. -/
abbrev Proposition.Context (Atom : Type u) := {c : CLL.Proposition.Context Atom // c.IsMLL}

/-- Filling of an MLL propositional context. -/
def Proposition.Context.fill (c : Proposition.Context Atom) (a : Proposition Atom) :
    Proposition Atom where
  val := CLL.Proposition.Context.fill c a
  property := (CLL.Proposition.Context.isMLL_fill c.property).mpr a.property

/-- MLL sequents.

Implementation note: it is important that this is defined as a `Multiset` rather than a `Subtype`
of `CLL.Sequent` (i.e., `{Γ : CLL.Sequent Atom // Γ.IsMLL}`). Otherwise, we would not get access to
set notation for MLL sequents.
-/
abbrev Sequent (Atom : Type u) := Multiset (Proposition Atom)

-- {Γ : CLL.Sequent Atom // Γ.IsMLL}
-- Multiset (Proposition Atom)

/-- Upcast of an MLL sequent into a CLL sequent. -/
instance instCoeSequent : Coe (Sequent Atom) (CLL.Sequent Atom) where
  coe Γ := Γ.map Subtype.val

/-- Downcast of a CLL sequent into an MLL sequent. -/
def _root_.Cslib.Logic.CLL.Sequent.toMLL {Γ : CLL.Sequent Atom} (h : Γ.IsMLL) : Sequent Atom :=
  Γ.attach.map (fun (a : {a : CLL.Proposition Atom // a ∈ Γ}) => ⟨a.val, h a a.property⟩)

def _root_.Cslib.Logic.CLL.Sequent.toMLL_eq {Γ : CLL.Sequent Atom} (h : Γ.IsMLL) :
    (Γ.toMLL h : CLL.Sequent Atom) = Γ := by simp [CLL.Sequent.toMLL]

/-- MLL derivations. -/
abbrev Proof {Atom : Type u} (Γ : Sequent Atom) := {p : CLL.Proof (Atom := Atom) Γ // p.IsMLL}

-- /-- Downcast of a CLL proof into an MLL proof. -/
-- def _root_.Cslib.Logic.CLL.Proof.toMLL {p : CLL.Proof Γ} (h : p.IsMLL) :
--     MLL.Proof (Γ.toMLL (CLL.Proof.isMLL_sequent h)) :=
--   ⟨CLL.Sequent.toMLL_eq (CLL.Proof.isMLL_sequent h) ▸ p, h⟩

-- /-- Recursor for bundled MLL derivations. -/
-- @[induction_eliminator, cases_eliminator, elab_as_elim]
-- abbrev Proof.rec
--     {motive : {Γ : Sequent Atom} → (p : Proof Γ) → Sort u}
--     {Γ : Sequent Atom}
--     (p : Proof Γ) :=
--   @CLL.Proof.IsMLL.rec
--     (motive := fun {Γ} {p : CLL.Proof Γ} h => motive
--       ⟨p, h⟩)
--     (p := p.val) (h := p.property)


theorem bot_cons : Multiset.map Subtype.val (Proposition.bot ::ₘ Γ) = ⊥ ::ₘ Multiset.map Subtype.val Γ  := by
  simp [Proposition.bot]
  rfl

-- def _root_.Cslib.Logic.CLL.Proof.toMLL (p : CLL.Proof Γ) (hp : p.IsMLL) : Proof (Γ.toMLL (CLL.Proof.isMLL_sequent hp)) :=
--   match p, hp with
--   -- | .ax (a := a), _ => .ax
--   | .one, _ => ⟨.one, by simp⟩
--   | .bot p, hp =>
--     let p' := p.toMLL hp

--     ⟨CLL.Proof.bot (p.toMLL hp), by grind only [CLL.Proof.IsMLL]⟩
--     let r := p.toMLL hp

--     let p' := (Cslib.Logic.CLL.Sequent.toMLL_eq (Cslib.Logic.CLL.Proof.isMLL_sequent hp)) ▸ p.toMLL hp
--     ⟨.bot (toMLL_eq ▸ p.toMLL hp), by simp⟩

def Proof.one {Atom} : Proof (Atom := Atom) {Proposition.one} := ⟨.one, by simp⟩



def Proof.bot {Γ : Sequent Atom} (p : Proof Γ) : Proof (Proposition.bot ::ₘ Γ) :=
  ⟨bot_cons ▸ CLL.Proof.bot p.val, by grind only [CLL.Proof.IsMLL]⟩

-- def Proof.tensor {Γ : Sequent Atom} (p : Proof (a ::ₘ Γ)) (q : Proof (b ::ₘ Δ)) : Proof (a.tensor b ::ₘ Γ) :=
--   ⟨CLL.Proof.tensor p.val q.val, by grind only [CLL.Proof.IsMLL]⟩

  -- ⟨bot_cons ▸ CLL.Proof.bot p.val, by grind only [CLL.Proof.IsMLL]⟩

/- Recursor for MLL derivations. -/
-- @[induction_eliminator, elab_as_elim]
-- def Proof.rec
--     {motive : (Γ : Sequent Atom) → Proof Γ → Sort u}
--     (ax : ∀ a : Proposition Atom, motive {a, a⫠} ⟨.ax, by simp⟩)
--     (one : motive {Proposition.one} ⟨.one, by simp⟩)
--     (bot : ∀ p : Proof Γ, motive Γ p → motive (.bot ::ₘ Γ) ⟨Proof.bot p, by simp⟩)
--     (tensor : ∀ a b : Proposition Atom, motive a → motive b →
--       motive ⟨.tensor a.1 b.1, ⟨a.2, b.2⟩⟩)
--     (parr : ∀ a b : Proposition Atom, motive a → motive b →
--       motive ⟨.parr a.1 b.1, ⟨a.2, b.2⟩⟩)
--     (p : Proof Γ) : motive p :=
--   match a with
--   | ⟨.atom x, _⟩ => atom x
--   | ⟨.atomDual x, _⟩ => atomDual x
--   | ⟨.one, _⟩ => one
--   | ⟨.bot, _⟩ => bot
--   | ⟨.tensor a b, ⟨ha, hb⟩⟩ =>
--     tensor ⟨a, ha⟩ ⟨b, hb⟩
--       (Proposition.rec atom atomDual one bot tensor parr ⟨a, ha⟩)
--       (Proposition.rec atom atomDual one bot tensor parr ⟨b, hb⟩)
--   | ⟨.parr a b, ⟨ha, hb⟩⟩ =>
--       parr ⟨a, ha⟩ ⟨b, hb⟩
--         (Proposition.rec atom atomDual one bot tensor parr ⟨a, ha⟩)
--         (Proposition.rec atom atomDual one bot tensor parr ⟨b, hb⟩)
--   | ⟨.zero, h⟩ | ⟨.top, h⟩ | ⟨.oplus _ _, h⟩ | ⟨.with _ _, h⟩
--     | ⟨.bang _, h⟩ | ⟨.quest _, h⟩ => nomatch h

/-- The sequent calculus of MLL. -/
instance : Logic.InferenceSystem (Sequent Atom) := ⟨Proof⟩

end Cslib.Logic.MLL
