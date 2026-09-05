/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Composition
import Mathlib.Tactic.FinCases

/-! Regression tests for composition: empty output, boundary clamping, final-step output,
disjoint work tapes, and padded component runs. -/

namespace CslibTests.MultiTapeComposition

open Turing.MultiTapeTM

private def emit (symbol : Option Bool) : Turing.MultiTapeTM 0 Bool Unit where
  q₀ := ()
  tr _ _ _ := ⟨0, Fin.elim0, symbol, none⟩

private def probe : Turing.MultiTapeTM 0 Bool (Fin 8) where
  q₀ := 0
  tr q input _ :=
    ⟨(![-1, -1, 1, 1, 1, -1, -1, 1] : Fin 8 → SignType) q,
      Fin.elim0, some input.isSome,
      if h : q.val + 1 < 8 then some ⟨q.val + 1, h⟩ else none⟩

-- Both outward moves clamp; the subsequent inward moves recover the only input symbol.
example : ((comp (emit (some true)) probe).runFrom
    ((comp (emit (some true)) probe).initCfg []) 21).output =
      [true, false, false, true, false, false, true, false] := by rfl

-- Empty intermediate output has adjacent blank boundaries and still reaches the second phase.
example : ((comp (emit none) probe).runFrom
    ((comp (emit none) probe).initCfg []) 20).output = List.replicate 8 false := by rfl

-- Output emitted on the halting transition is retained, including when both machines have no tapes.
example : ((comp (emit none) (emit (some true))).runFrom
    ((comp (emit none) (emit (some true))).initCfg []) 6).output = [true] := by rfl

example : ((comp (emit none) (emit (some true))).runFrom
    ((comp (emit none) (emit (some true))).initCfg []) 6).state = none := by rfl

private def writeEmit (symbol : Bool) : Turing.MultiTapeTM 1 Bool Bool where
  q₀ := false
  tr q _ work :=
    if q then ⟨0, fun _ => (none, 0), work 0, none⟩
    else ⟨0, fun _ => (some (some symbol), 0), none, some true⟩

-- Each component reads its own write; the first component's output does not escape directly.
example : ((comp (writeEmit true) (writeEmit false)).runFrom
    ((comp (writeEmit true) (writeEmit false)).initCfg []) 10).output = [false] := by rfl

example : ((comp (writeEmit true) (writeEmit false)).runFrom
    ((comp (writeEmit true) (writeEmit false)).initCfg []) 10).workTapeSymbols =
      ![some true, some true, some false] := by
  funext i
  fin_cases i <;> rfl

-- The public computation theorem accepts padded halting times for both components.
example : ∃ t ≤ 10 + (0 + 3) + 2 * 12, ∃ s ≤ 0 + (0 + 2) + 0,
    ComputesInTimeAndSpace (comp (emit none) (emit (some true))) [] [true] t s := by
  apply comp_computesInTimeAndSpace (emit none) (emit (some true))
    (middle := []) (t₀ := 10) (s₀ := 0) (t₁ := 12) (s₁ := 0)
  · exact ⟨rfl, rfl, spaceUsed_zero_tapes_eq_zero _ _ rfl⟩
  · exact ⟨rfl, rfl, spaceUsed_zero_tapes_eq_zero _ _ rfl⟩

end CslibTests.MultiTapeComposition
