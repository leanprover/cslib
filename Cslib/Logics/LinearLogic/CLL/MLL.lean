/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Logics.LinearLogic.CLL.Basic
public import Cslib.Foundations.Logic.InferenceSystem

@[expose] public section

/-! # Multiplicative Classical Linear Logic -/

namespace Cslib.CLL

@[scoped grind =]
def Proposition.IsMLL : Proposition Atom → Prop
  | atom _ | atomDual _ | one | bot => True
  | top | zero => False
  | tensor a b | parr a b => a.IsMLL ∧ b.IsMLL
  | oplus _ _ | .with _ _ => False
  | bang _ | quest _ => False

@[scoped grind →]
theorem Proposition.isMLL_dual {a : Proposition Atom} (ha : a.IsMLL) : a⫠.IsMLL := by
  induction a <;> grind

@[scoped grind =]
def Proposition.Context.IsMLL : Context Atom → Prop
  | hole => True
  | tensorL a b | tensorR a b | parrL a b | parrR a b => a.IsMLL ∧ b.IsMLL
  | _ => False

@[scoped grind .]
theorem Proposition.Context.isMLL_fill {c : CLL.Proposition.Context Atom} {a : CLL.Proposition Atom}
    (hc : c.IsMLL) : (c.fill a).IsMLL ↔ a.IsMLL := by induction c <;> grind

@[scoped grind =]
def Sequent.IsMLL (Γ : Sequent Atom) := ∀ a ∈ Γ, a.IsMLL

open scoped Logic.InferenceSystem

@[scoped grind =]
def Proof.IsMLL {Γ : Sequent Atom} : ⇓Γ → Prop
  | ax (a := a) => a.IsMLL
  | cut p q | tensor p q => p.IsMLL ∧ q.IsMLL
  | one => True
  | bot p | parr p => p.IsMLL
  | _ => False

open scoped Sequent Proposition in
theorem Proof.isMLL_sequent {Γ : Sequent Atom} (p : ⇓Γ) (hp : p.IsMLL) : Γ.IsMLL := by
  -- This should be much simpler, gotta figure out how to make grind work.
  induction p
  case ax => grind [Multiset.insert_eq_cons, Multiset.mem_singleton]
  case one =>
    simp [Sequent.IsMLL]
    simp [Proposition.IsMLL]
  case parr | tensor | cut => grind
  case bot Γ p ih =>
    simp only [Proof.IsMLL] at hp
    simp only [Sequent.IsMLL, Multiset.mem_cons, forall_eq_or_imp]
    apply And.intro
    · simp [Proposition.IsMLL]
    · grind
  case oplus₁ | oplus₂ | «with» | top | quest | weaken | contract | bang => contradiction

end Cslib.CLL

namespace Cslib.CLL.MLL

abbrev Proposition (Atom : Type u) := {a : CLL.Proposition Atom // a.IsMLL}

abbrev Proposition.Context (Atom : Type u) := {c : CLL.Proposition.Context Atom // c.IsMLL}

open scoped CLL.Proposition CLL.Proposition.Context in
def Proposition.Context.fill (c : MLL.Proposition.Context Atom) (a : MLL.Proposition Atom) :
    MLL.Proposition Atom :=
  ⟨CLL.Proposition.Context.fill c a, (CLL.Proposition.Context.isMLL_fill c.property).2 a.property⟩

abbrev Sequent (Atom : Type u) := {Γ : CLL.Sequent Atom // Γ.IsMLL}

abbrev Proof {Atom : Type u} (Γ : Sequent Atom) := {p : CLL.Proof (Atom := Atom) Γ // p.IsMLL}

instance : Logic.InferenceSystem (Sequent Atom) := ⟨Proof⟩

end Cslib.CLL.MLL
