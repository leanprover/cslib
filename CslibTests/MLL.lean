/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Logics.LinearLogic.CLL.MLL

namespace CslibTests

/-! # Tests for Multiplicative Classical Linear Logic -/

open Cslib.Logic.CLL Cslib.Logic.InferenceSystem

open Proposition Proof Sequent

-- Test the custom Proof.IsMLL recursor with induction.
example {Γ : Sequent Atom} (p : ⇓Γ) (h : p.IsMLL) : Γ.IsMLL := by
  induction h
  case ax =>
    grind [Proof.IsMLL, Multiset.insert_eq_cons, Multiset.mem_singleton]
  case one =>
    simp [Sequent.IsMLL, Proposition.IsMLL]
  case parr | tensor | cut => grind [Proposition.IsMLL, Proof.IsMLL]
  case bot Γ p ih =>
    simp
    grind [Proof.IsMLL]

-- Test the custom MLL.Proposition recursor with induction.
example (a : Cslib.Logic.MLL.Proposition Atom) : a.dual.dual = a := by
  induction a <;> grind only [= dual_involution]

end CslibTests
