/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Batteries.Util.ProofWanted
import Cslib.Logics.LinearLogic.CLL.Basic

namespace CLL

universe u

variable {Atom : Type u}

/-- A proof is cut-free if it does not contain any applications of rule cut. -/
inductive Proof.CutFree : {Γ : Sequent Atom} → ⊢Γ → Prop where
  | ax : Proof.ax.CutFree
  | one : Proof.one.CutFree
  | bot (p : ⊢Γ) (hp : CutFree p) : p.bot.CutFree
  | exchange (hperm : Γ.Perm Δ) (p : ⊢Γ) : p.CutFree → (Proof.exchange hperm p).CutFree
  | parr (p : ⊢(a :: b :: Γ)) : p.CutFree → p.parr.CutFree
  | tensor (p : ⊢(a :: Γ)) (q : ⊢(b :: Δ)) :
    p.CutFree → q.CutFree → (Proof.tensor p q).CutFree
  | oplus₁ (p : ⊢(a :: Γ)) : p.CutFree → p.oplus₁.CutFree
  | oplus₂ (p : ⊢(b :: Γ)) : p.CutFree → p.oplus₂.CutFree
  | with (p : ⊢(a :: Γ)) (q : ⊢(b :: Γ)) :
    p.CutFree → q.CutFree → (Proof.with p q).CutFree
  | top : Proof.top.CutFree
  | quest (p : ⊢(a :: Γ)) : p.CutFree → p.quest.CutFree
  | weaken (p : ⊢Γ) : p.CutFree → p.weaken.CutFree
  | contract (p : ⊢(ʔa :: ʔa :: Γ)) : p.contract.CutFree
  | bang (hqs: Sequent.allQuest Γ) (p : ⊢(a :: Γ)) : p.CutFree → (p.bang hqs).CutFree
  -- No rule for cut.

/-- Size of a `Proof`. -/
inductive Proof.HasSize : {Γ : Sequent Atom} → ⊢Γ → Nat → Prop where
  | ax : Proof.ax.HasSize 1
  | one : Proof.one.HasSize 1
  | bot (p : ⊢Γ) (n : Nat) (hp : p.HasSize n) : p.bot.HasSize (n + 1)
  | exchange (hperm : Γ.Perm Δ) (p : ⊢Γ) (n : Nat) (hp : p.HasSize n) :
    (Proof.exchange hperm p).HasSize (n + 1)
  | parr (p : ⊢(a :: b :: Γ)) (n : Nat) (hp : p.HasSize n) : p.parr.HasSize (n + 1)
  | tensor (p : ⊢(a :: Γ)) (q : ⊢(b :: Δ)) (np nq : Nat)
    (hp : p.HasSize np) (hq : q.HasSize nq) :
    (Proof.tensor p q).HasSize (np + nq + 1)
  | oplus₁ (p : ⊢(a :: Γ)) (n : Nat) (hp : p.HasSize n) : p.oplus₁.HasSize (n + 1)
  | oplus₂ (p : ⊢(b :: Γ)) (n : Nat) (hp : p.HasSize n) : p.oplus₂.HasSize (n + 1)
  | with (p : ⊢(a :: Γ)) (q : ⊢(b :: Γ)) (np nq : Nat)
    (hp : p.HasSize np) (hq : q.HasSize nq) :
    (Proof.with p q).HasSize (np + nq + 1)
  | top : Proof.top.HasSize 1
  | quest (p : ⊢(a :: Γ)) (n : Nat) (hp : p.HasSize n) : p.quest.HasSize (n + 1)
  | weaken (p : ⊢Γ) (n : Nat) (hp : p.HasSize n) : p.weaken.HasSize (n + 1)
  | contract (p : ⊢(ʔa :: ʔa :: Γ)) (n : Nat) (hp : p.HasSize n) :
    p.contract.HasSize (n + 1)
  | bang (hqs: Sequent.allQuest Γ) (p : ⊢(a :: Γ)) (n : Nat) (hp : p.HasSize n) :
    (p.bang hqs).HasSize (n + 1)
  | cut (p : ⊢(a :: Γ)) (q : ⊢(a⫠ :: Δ)) (np nq : Nat)
    (hp : p.HasSize np) (hq : q.HasSize nq) :
    (Proof.cut p q).HasSize (np + nq + 1)

/-- Cut is admissible. -/
proof_wanted Proof.cut_admissible
  {a : Proposition Atom} (p : ⊢(a :: Γ)) (q : ⊢(a⫠ :: Δ)) (hp : p.CutFree) (hq : q.CutFree) :
  ∃ r : ⊢(Γ ++ Δ), r.CutFree

/-- Cut elimination: for any sequent Γ, if there is a proof of Γ, then there exists a cut-free
proof of Γ. -/
proof_wanted Proof.cut_elim (p : ⊢Γ) : ∃ q : ⊢Γ, q.CutFree
  /- The following is just some sanity checks. We'll need to formulate the appropriate induction
    metric to satisfy the termination checker, as usual for this kind of proofs.
  -/
  /-
  cases p
  case ax a =>
    exists Proof.ax
    constructor
  case cut a Γ Δ p q =>
    have ihp := Proof.cut_elim p
    have ihq := Proof.cut_elim q
    grind [Proof.cut_admissible]
  case exchange Atom Δ p hperm =>
    obtain ⟨pcf, hp⟩ := Proof.cut_elim p
    exists (pcf.exchange hperm)
    apply CutFree.exchange hperm pcf
  case one =>
    exists one; constructor
  -/



end CLL
