/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Rewind
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Sequential

/-!
# Halting with the input head rewound

`rewindInput` follows an arbitrary machine with the native-input rewind controller. It preserves
all work tapes, work-tape head positions, and output, and halts with the input head at position one.
The overhead is at most the input length plus two, including for empty input.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- Normalize a machine to halt with its input head at the initial position. -/
def rewindInput (tm : MultiTapeTM k Symbol State) : MultiTapeTM k Symbol (State ⊕ RewindState) :=
  tm.seq (rewind .input)

/-- Exact input-rewind execution from any configuration, once the first machine reaches its
least halting time. Everything other than the input head and control state is preserved. -/
lemma runFrom_rewindInput (tm : MultiTapeTM k Symbol State) (cfg : Cfg k Symbol State input)
    (u : ℕ) (hhalt : (tm.runFrom cfg u).state = none)
    (hactive : ∀ m < u, (tm.runFrom cfg m).state ≠ none) :
    tm.rewindInput.runFrom (Sequential.left (rewind .input) cfg)
        (u + ((tm.runFrom cfg u).inputPos.val - 1 + 2)) =
      Sequential.right (Rewind.inputCfg (tm.runFrom cfg u) none 1) := by
  rw [rewindInput, runFrom_seq tm (rewind .input) cfg u _ hhalt hactive]
  exact congrArg Sequential.right (Rewind.runFrom_input (tm.runFrom cfg u))

/-- Any halting computation can be normalized to finish with its input head reset.
The bound accepts padded native halting times. -/
lemma rewindInput_halts (tm : MultiTapeTM k Symbol State) (t : ℕ)
    (hhalt : (tm.runFrom (tm.initCfg input) t).state = none) :
    ∃ t' ≤ t + input.length + 2,
      tm.rewindInput.runFrom (tm.rewindInput.initCfg input) t' =
        Sequential.right (Rewind.inputCfg (tm.runFrom (tm.initCfg input) t) none 1) := by
  obtain ⟨u, hu, hhaltu, hactiveu⟩ := exists_minimal_halting_time tm (tm.initCfg input) t hhalt
  refine ⟨u + ((tm.runFrom (tm.initCfg input) u).inputPos.val - 1 + 2), ?_, ?_⟩
  · have := (tm.runFrom (tm.initCfg input) u).inputPos.isLt
    omega
  · rw [tm.runFrom_eq_of_halt (tm.initCfg input) hu hhaltu]
    exact runFrom_rewindInput tm (tm.initCfg input) u hhaltu hactiveu

/-- Every halting run from an initial configuration has its input head at the initial position. -/
def HaltsWithInputAtStart (tm : MultiTapeTM k Symbol State) : Prop :=
  ∀ (input : List Symbol) (t : ℕ), (tm.runFrom (tm.initCfg input) t).state = none →
    (tm.runFrom (tm.initCfg input) t).inputPos = 1

/-- The transformed machine satisfies the normal form at every halting time, including padding. -/
lemma rewindInput_haltsWithInputAtStart (tm : MultiTapeTM k Symbol State) :
    HaltsWithInputAtStart tm.rewindInput := by
  intro input t ht
  have hnative : (tm.runFrom (tm.initCfg input) t).state = none := by
    by_contra hn
    have hactive (m : ℕ) (hm : m < t) : (tm.runFrom (tm.initCfg input) m).state ≠ none :=
      fun h => hn (tm.runFrom_state_eq_none_mono (tm.initCfg input) (by omega) h)
    have hleft := Sequential.runFrom_left tm (rewind .input) (tm.initCfg input) t hactive
    change ((tm.seq (rewind .input)).runFrom
      (Sequential.left (rewind .input) (tm.initCfg input)) t).state = none at ht
    rw [hleft] at ht
    simp [Sequential.left] at ht
  obtain ⟨s, _, hfinal⟩ := rewindInput_halts tm t hnative
  have hs : (tm.rewindInput.runFrom (tm.rewindInput.initCfg input) s).state = none := by
    rw [hfinal]
    rfl
  rcases Nat.le_total t s with hle | hle
  · have heq := tm.rewindInput.runFrom_eq_of_halt (tm.rewindInput.initCfg input) hle ht
    exact congrArg Cfg.inputPos (heq.symm.trans hfinal)
  · rw [tm.rewindInput.runFrom_eq_of_halt (tm.rewindInput.initCfg input) hle hs, hfinal]
    rfl

end Turing.MultiTapeTM
