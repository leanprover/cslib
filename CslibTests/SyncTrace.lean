/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Foundations.Semantics.FLTS.SyncTrace

/-! # The finite-state hypothesis in pairwise synchronisation

This module proves that `Cslib.FLTS.hasSyncTrace_iff_pairwiseHasSyncTrace` does not hold for
infinite `FLTS`, and exercises the cubic bound on synchronising traces on the Černý automaton.
-/

namespace CslibTests.SyncTrace

open Cslib FLTS

def countdown : FLTS ℕ Unit := ⟨fun s₁ _ => s₁ - 1⟩

theorem countdown_mtr (s₁ : ℕ) (μs : List Unit) :
    countdown.mtr s₁ μs = s₁ - μs.length := by
  induction μs using List.reverseRecOn with
  | nil => simp
  | append_singleton μs μ ih =>
    nth_rw 1 [mtr_concat_eq, countdown]
    lia [List.length_append, List.length_singleton]

theorem countdown_pairwiseHasSyncTrace : countdown.PairwiseHasSyncTrace := by
  intro s₁ s₂
  refine ⟨List.replicate (max s₁ s₂) (), ?_⟩
  simp [countdown_mtr]

theorem countdown_not_hasSyncTrace : ¬countdown.HasSyncTrace := by
  intro ⟨μs, hμs⟩
  simpa [countdown_mtr] using hμs 0 (μs.length + 1)

/-- The Černý automaton with four states: `false` rotates the states, and `true` sends `0` to `1`
and fixes every other state. Its shortest synchronising traces have length `(4 - 1) ^ 2 = 9`. -/
def cerny4 : FLTS (Fin 4) Bool := ⟨fun s b => if b then (if s = 0 then 1 else s) else s + 1⟩

theorem cerny4_isSyncTrace :
    cerny4.IsSyncTrace [true, false, false, false, true, false, false, false, true] := by
  unfold IsSyncTrace
  decide

/-- The cubic bound `(n - 1) * n.choose 2` gives a synchronising trace of length at most `18`. -/
example : ∃ μs, cerny4.IsSyncTrace μs ∧ μs.length ≤ 18 := by
  obtain ⟨μs, hμs, hlen⟩ := HasSyncTrace.exists_isSyncTrace_length_le ⟨_, cerny4_isSyncTrace⟩
  refine ⟨μs, hμs, hlen.trans ?_⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

end CslibTests.SyncTrace
