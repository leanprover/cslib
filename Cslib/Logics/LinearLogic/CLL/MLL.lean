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

/-- Duality in MLL stays in MLL. -/
@[scoped grind →]
theorem Proposition.isMLL_dual {a : Proposition Atom} (ha : a.IsMLL) : a⫠.IsMLL := by
  induction a with
  | atom | atomDual | one | bot | tensor | parr => grind [dual, IsMLL]
  | _ => grind [IsMLL]

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

open scoped Sequent Proposition in
/-- An MLL proof can only prove MLL sequents. -/
theorem Proof.isMLL_sequent {Γ : Sequent Atom} (p : ⇓Γ) (hp : p.IsMLL) : Γ.IsMLL := by
  -- This should be simpler, grind seems to have some trouble.
  induction p
  case ax =>
    grind [Proof.IsMLL, Multiset.insert_eq_cons, Multiset.mem_singleton]
  case one =>
    simp [Sequent.IsMLL, Proposition.IsMLL]
  case parr | tensor | cut => grind [Proposition.IsMLL, Proof.IsMLL]
  case bot Γ p ih =>
    simp only [Proof.IsMLL] at hp
    simp only [Sequent.IsMLL, Multiset.mem_cons, forall_eq_or_imp]
    apply And.intro
    · simp only [Proposition.IsMLL]
    · grind only [Sequent.IsMLL]
  case oplus₁ | oplus₂ | «with» | top | quest | weaken | contract | bang => contradiction

end Cslib.Logic.CLL

namespace Cslib.Logic.MLL

/-- MLL propositions. -/
abbrev Proposition (Atom : Type u) := {a : CLL.Proposition Atom // a.IsMLL}

/-- MLL propositional contexts. -/
abbrev Proposition.Context (Atom : Type u) := {c : CLL.Proposition.Context Atom // c.IsMLL}

open scoped CLL.Proposition CLL.Proposition.Context in
/-- Filling of an MLL propositional context. -/
def Proposition.Context.fill (c : MLL.Proposition.Context Atom) (a : MLL.Proposition Atom) :
    MLL.Proposition Atom :=
  ⟨CLL.Proposition.Context.fill c a, (CLL.Proposition.Context.isMLL_fill c.property).2 a.property⟩

/-- MLL sequents. -/
abbrev Sequent (Atom : Type u) := {Γ : CLL.Sequent Atom // Γ.IsMLL}

/-- MLL derivations. -/
abbrev Proof {Atom : Type u} (Γ : Sequent Atom) := {p : CLL.Proof (Atom := Atom) Γ // p.IsMLL}

/-- The sequent calculus of MLL. -/
instance : Logic.InferenceSystem (Sequent Atom) := ⟨Proof⟩

open scoped Logic.InferenceSystem

end Cslib.Logic.MLL
