/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Basic
public import Cslib.Computability.Machines.MultiTapeTuring.TapeExtension


namespace Turing

variable [Inhabited Symbol] [Fintype Symbol]

variable {k : ℕ}

/-- Statistics on the tape head movements. -/
public structure HeadStats where
  /-- The minimal (left-most) position of the head during the computation,
  relative to the starting position. -/
  min : ℤ
  /-- The maximal (right-most) position of the head during the computation,
  relative to the starting position. -/
  max : ℤ
  /-- The final position of the head after the computation, relative to the
  starting position. -/
  final : ℤ
  h_bounds : min ≤ final ∧ final ≤ max ∧ min ≤ 0 ∧ 0 ≤ max

/-- The space required. -/
public def HeadStats.space (hs : HeadStats) : ℕ :=
  (1 + hs.max - hs.min).toNat -- TODO we know it is nonnegative, is there a way to make use of that?


/-- Compute the head statistics for a turing machine starting with a certain tape configuration. -/
public def headStats (tm : MultiTapeTM k Symbol) (tapes : Fin k → BiTape Symbol) :
  Part (Fin k → HeadStats) := sorry

/-- Execute a Turing machine and also compute head statistics. -/
public def MultiTapeTM.evalWithStats (tm : MultiTapeTM k Symbol) (tapes : Fin k → BiTape Symbol) :
  Part ((Fin k → BiTape Symbol) × (Fin k → HeadStats)) := sorry

-- move this somewhere else
def seq (tm₁ tm₂ : MultiTapeTM k Symbol) : MultiTapeTM k Symbol := sorry

def seq_combine_stats (stats₁ stats₂ : Fin k → HeadStats) : Fin k → HeadStats :=
  fun i => match (stats₁ i, stats₂ i) with
  | (⟨min₁, max₁, final₁, h₁⟩, ⟨min₂, max₂, final₂, h₂⟩) =>
    ⟨min min₁ (min₂ + final₁),
    max max₁ (max₂ + final₁),
    final₁ + final₂,
    by omega⟩

lemma seq_evalWithStats (tm₁ tm₂ : MultiTapeTM k Symbol) (tapes : Fin k → BiTape Symbol) (i : Fin k) :
  (seq tm₁ tm₂).evalWithStats tapes = do
      let (tapes', stats₁) ← tm₁.evalWithStats tapes
      let (tapes'', stats₂) ← tm₂.evalWithStats tapes'
      return (tapes'', seq_combine_stats stats₁ stats₂) := by sorry

-- Next step: relate space requirements and head stats.

theorem stats_and_space (tm : MultiTapeTM k Symbol) (tapes tapes' : Fin k → BiTape Symbol) (s : ℕ) :
  (∃ t, tm.TransformsTapesInTimeAndSpace tapes tapes' t s) ↔
    ∃ hs, (∑ i, (hs i).space) ≤ s ∧ tm.evalWithStats tapes = .some (tapes', hs) := by sorry
end Turing
