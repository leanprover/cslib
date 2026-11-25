/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Foundations.Semantics.FLTS.SyncTrace

/-! # The finite-state hypothesis in pairwise synchronisation

This module proves that `Cslib.FLTS.hasSyncTrace_iff_pairwiseHasSyncTrace` does not hold for
infinite `FLTS`.
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

end CslibTests.SyncTrace
