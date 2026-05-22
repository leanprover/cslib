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
  induction h with
  | ax =>
    grind [Proof.IsMLL, Multiset.insert_eq_cons, Multiset.mem_singleton]
  | one =>
    simp [Sequent.IsMLL, Proposition.IsMLL]
  | parr | tensor | cut => grind [Proposition.IsMLL, Proof.IsMLL]
  | bot p h =>
    simp
    grind [Proof.IsMLL]

-- Induction on a bundled MLL proof.
example {Γ : Sequent Atom} (p : MLL⇓Γ) : Γ.IsMLL := by
  rcases p with ⟨p, h⟩
  induction h with
  | ax =>
    grind [Proof.IsMLL, Multiset.insert_eq_cons, Multiset.mem_singleton]
  | one =>
    simp [Sequent.IsMLL, Proposition.IsMLL]
  | parr | tensor | cut =>
    grind [Proposition.IsMLL, Proof.IsMLL]
  | bot p h =>
    simp
    grind [Proof.IsMLL]

-- Test that MLL proofs can be coerced into CLL proofs.
example {Γ : Sequent Atom} (p : MLL⇓Γ) : ⇓Γ := (p : ⇓Γ)

end CslibTests
