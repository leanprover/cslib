/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Logics.LTL.Basic
import Cslib.Logics.Modal.Denotation

namespace Cslib.Logic.Modal.LTL

open scoped InferenceSystem Modal.Proposition Modal.Satisfies

-- States differ from their positions, so interpreting atoms on positions would fail these tests.
private def trace : ωSequence ℕ := ⟨fun n => n + 10⟩
private def before : Proposition (StateAtom ℕ) := .atom (· < 12)
private def reached : Proposition (StateAtom ℕ) := .atom (· = 12)

example : ⇓Modal[Model.ofTracePredicates trace,⟨0, 7⟩ ⊨ before] := by
  change 10 < 12
  omega

example : ⇓Modal[Model.ofTracePredicates trace,⟨1, 7⟩ ⊨ reached.next] := by
  unfold Model.ofTracePredicates
  rw [Satisfies.next_iff]
  rfl

-- Until includes the current position and excludes its witness from the left operand's interval.
example : ⇓Modal[Model.ofTracePredicates trace,⟨0, 7⟩ ⊨ before.until reached] := by
  unfold Model.ofTracePredicates
  rw [Satisfies.until_iff]
  refine ⟨2, by omega, ?_, ?_⟩
  · rfl
  · intro j _ hj
    change j + 10 < 12
    omega

-- Nested temporal operators quantify over the future of each current position.
example : ⇓Modal[Model.ofTracePredicates trace,⟨0, 7⟩ ⊨
    (Proposition.eventually (.atom (fun s : ℕ => 12 ≤ s))).always] := by
  unfold Model.ofTracePredicates
  rw [Satisfies.always_iff]
  intro k _
  rw [Satisfies.eventually_iff]
  refine ⟨k + 2, by omega, ?_⟩
  change 12 ≤ k + 2 + 10
  omega

-- An immediate witness does not require the left operand.
example : ⇓Modal[Model.ofTracePredicates trace,⟨2, 7⟩ ⊨
    (⊥ : Proposition (StateAtom ℕ)).until reached] := by
  unfold Model.ofTracePredicates
  rw [Satisfies.until_iff]
  exact ⟨2, by omega, rfl, by omega⟩

-- Strong until requires a witness even when the left operand always holds.
example : ¬⇓Modal[Model.ofTracePredicates trace,⟨0, 7⟩ ⊨
    (⊤ : Proposition (StateAtom ℕ)).until ⊥] := by
  simp only [Model.ofTracePredicates, Satisfies.until_iff, Modal.Satisfies.false,
    false_and, and_false, exists_false, not_false_eq_true]

-- Release allows its right operand to hold forever without the left operand ever holding.
example : ⇓Modal[Model.ofTracePredicates trace,⟨0, 7⟩ ⊨
    (⊥ : Proposition (StateAtom ℕ)).release ⊤] := by
  unfold Model.ofTracePredicates
  rw [Satisfies.release_iff]
  exact fun _ _ => Or.inl Modal.Satisfies.true

-- The right operand of release must hold at the releasing position as well.
example : ¬⇓Modal[Model.ofTracePredicates trace,⟨2, 7⟩ ⊨ reached.release before] := by
  unfold Model.ofTracePredicates
  rw [Satisfies.release_iff]
  intro h
  rcases h 2 (by omega) with h | ⟨j, hj, hk, _⟩
  · change 12 < 12 at h
    omega
  · omega

-- Nested untils reset their own anchors without affecting an enclosing interval.
example (t : ωSequence State) (v : State → Atom → Prop) (p q r : Atom) (n a b : ℕ) :
    ⇓Modal[Model.ofωSequence t v,⟨n, a⟩ ⊨
      Proposition.until (Proposition.until (.atom p) (.atom q)) (.atom r)] ↔
    ⇓Modal[Model.ofωSequence t v,⟨n, b⟩ ⊨
      Proposition.until (Proposition.until (.atom p) (.atom q)) (.atom r)] :=
  Satisfies.anchor_iff t v ((Proposition.IsLTL.atom p |>.until (.atom q)).until (.atom r)) n a b

-- Generic modal denotation applies directly to temporal propositions.
example (t : ωSequence State) (v : State → Atom → Prop) (φ : Proposition Atom) (n a : ℕ) :
    (⟨n, a⟩ : Point) ∈ φ.next.denotation (Model.ofωSequence t v) ↔
      ⇓Modal[Model.ofωSequence t v,⟨n + 1, a⟩ ⊨ φ] := by
  rw [satisfies_mem_denotation, Satisfies.next_iff]

end Cslib.Logic.Modal.LTL
