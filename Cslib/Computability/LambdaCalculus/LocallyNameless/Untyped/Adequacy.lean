/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Computability.LambdaCalculus.Named.Untyped.Basic
import Cslib.Computability.LambdaCalculus.LocallyNameless.Untyped.Basic

universe u

variable {Var : Type u} [DecidableEq Var]

namespace LambdaCalculus

-- This seems obvious.
def Named.Term.toLocallyNameless (m : Named.Term Var) : LocallyNameless.Term Var := sorry

-- This requires nontrivial design choices.
-- def LocallyNameless.Term.toNamed (m : LocallyNameless.Term Var) : Named.Term Var := sorry

section AlphaEquiv

/-- Two named terms are α-equivalent iff their locally nameless variants are equal. -/
theorem named_locallyNameless_alphaEquiv_iff_eq (m n : Named.Term Var) :
  m =α n ↔ m.toLocallyNameless = n.toLocallyNameless := by
  sorry

/-- Two locally-closed nameless terms are equal iff they are the nameless translation of
α-equivalent named terms. -/
theorem locallyNameless_lc_named_eq_iff_alphaEquiv (m n : LocallyNameless.Term Var) (hmlc : m.LC) (hnlc : n.LC) :
  m = n ↔ (∃ m' n' : Named.Term Var,
    m = m'.toLocallyNameless ∧ n = n'.toLocallyNameless ∧
    m' =α n') := by
  sorry

end AlphaEquiv

section Semantics

/- Correspondences for the reduction systems.
Could use (strong) bisimulation or even an isomorphism between the reduction systems. -/

end Semantics
