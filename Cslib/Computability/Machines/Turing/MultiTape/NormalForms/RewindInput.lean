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

/-- The normalized machine starts in the original machine's initial configuration. -/
lemma initCfg_rewindInput (tm : MultiTapeTM k Symbol State) (input : List Symbol) :
    tm.rewindInput.initCfg input = Sequential.left (rewind .input) (tm.initCfg input) := rfl

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

/-- **Normalizing costs no space.** The rewind moves no work-tape head, so every cell the
normalized machine visits was already visited by the original one. This is what makes the normal
form free to use inside a combinator: only the time bound grows. -/
lemma spaceUsed_rewindInput_le (tm : MultiTapeTM k Symbol State) (cfg : Cfg k Symbol State input)
    (u v : ℕ) (hhalt : (tm.runFrom cfg u).state = none)
    (hactive : ∀ m < u, (tm.runFrom cfg m).state ≠ none) :
    tm.rewindInput.spaceUsed (Sequential.left (rewind .input) cfg) (u + v) ≤
      tm.spaceUsed cfg u := by
  refine spaceUsed_le_of_workTapePos_mem _ _ (u + v) u fun m _ i => ?_
  rcases Nat.lt_or_ge m u with hm | hm
  · rw [rewindInput,
      Sequential.runFrom_left tm (rewind .input) cfg m fun r hr => hactive r (by omega)]
    exact mem_visitedByTapeHead.mpr ⟨m, by omega, rfl⟩
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [rewindInput, runFrom_seq tm (rewind .input) cfg u j hhalt hactive]
    simp only [Sequential.right, Cfg.withState_workTapePos, Rewind.runFrom_input_workTapePos,
      Cfg.withState_workTapePos]
    exact mem_visitedByTapeHead.mpr ⟨u, by omega, rfl⟩

/-- The normal form together with its cost: the run takes at most the input length plus two extra
steps, and uses no extra space at all. The bound accepts padded native halting times. -/
lemma rewindInput_halts_spaceUsed (tm : MultiTapeTM k Symbol State) (t : ℕ)
    (hhalt : (tm.runFrom (tm.initCfg input) t).state = none) :
    ∃ t' ≤ t + input.length + 2,
      tm.rewindInput.runFrom (tm.rewindInput.initCfg input) t' =
          Sequential.right (Rewind.inputCfg (tm.runFrom (tm.initCfg input) t) none 1) ∧
        tm.rewindInput.spaceUsed (tm.rewindInput.initCfg input) t' ≤
          tm.spaceUsed (tm.initCfg input) t := by
  obtain ⟨u, hu, hhaltu, hactiveu⟩ := exists_minimal_halting_time tm (tm.initCfg input) t hhalt
  refine ⟨u + ((tm.runFrom (tm.initCfg input) u).inputPos.val - 1 + 2), ?_, ?_, ?_⟩
  · have := (tm.runFrom (tm.initCfg input) u).inputPos.isLt
    omega
  · rw [tm.runFrom_eq_of_halt (tm.initCfg input) hu hhaltu]
    exact runFrom_rewindInput tm (tm.initCfg input) u hhaltu hactiveu
  · exact (spaceUsed_rewindInput_le tm (tm.initCfg input) u _ hhaltu hactiveu).trans
      (spaceUsed_mono tm (tm.initCfg input) hu)

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
