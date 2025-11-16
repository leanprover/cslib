/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Logics.LinearLogic.CLL.Basic

namespace Cslib

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

end CLL

end Cslib
