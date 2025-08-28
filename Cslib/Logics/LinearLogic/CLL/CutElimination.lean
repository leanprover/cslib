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
  | exchange (hperm : Γ.Perm Δ) (p : ⊢Γ) : (Proof.exchange hperm p).CutFree
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

/-- Cut is admissible. -/
proof_wanted Proof.cut_admissible
  (p : ⊢(a :: Γ)) (q : ⊢(a.dual :: Δ)) (hp : p.CutFree) (hq : q.CutFree) :
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
