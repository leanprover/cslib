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
def Proof.cutFree (p : ⇓Γ) : Bool :=
  match p with
  | ax => true
  | one => true
  | bot p => p.cutFree
  | exchange _ p => p.cutFree
  | parr p => p.cutFree
  | tensor p q => p.cutFree && q.cutFree
  | oplus₁ p => p.cutFree
  | oplus₂ p => p.cutFree
  | .with p q => p.cutFree && q.cutFree
  | top => true
  | quest p => p.cutFree
  | weaken p => p.cutFree
  | contract p => p.cutFree
  | bang _ p => p.cutFree
  | cut _ _ => false

abbrev CutFreeProof (Γ : Sequent Atom) := { q : ⇓Γ // q.cutFree }

-- TODO
/- Cut admissibility: given two proofs with dual propositions, returns a cut-free proof of their
cut. -/
-- def Proof.cutAdm
--   {a : Proposition Atom} (p : ⇓(a :: Γ)) (q : ⇓(a⫠ :: Δ)) (hp : p.cutFree) (hq : q.cutFree) :
--   CutFreeProof (Γ ++ Δ)

-- TODO
/- Cut elimination: given a proof of a sequent `Γ`, returns a cut-free proof of the same sequent.
-/
-- def Proof.cut_elim (p : ⇓Γ) : CutFreeProof Γ

end CLL
