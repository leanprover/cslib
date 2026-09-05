/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Composition.Simulation

/-!
# First-phase simulation and handoff

The first machine runs in lockstep with the composite. Its output is rewound to the left
boundary, then classified to establish the second machine's initial configuration.
-/

@[expose] public section

namespace Turing.MultiTapeTM.Composition

variable {k₀ k₁ : ℕ}
variable {Symbol State₀ State₁ : Type*}

variable (tm₀ : MultiTapeTM k₀ Symbol State₀) (tm₁ : MultiTapeTM k₁ Symbol State₁)

/-- The first-phase embedding sends an initial configuration to the composite initial
configuration. -/
private lemma embedFirst_initCfg (input : List Symbol) :
    embedFirst tm₀ tm₁ (tm₀.initCfg input) =
      (comp tm₀ tm₁).initCfg input := by
  apply Cfg.ext <;> try rfl
  · funext i p
    cases p <;> simp [embedFirst, ite_apply, listTape]
  · funext i
    simp [embedFirst]

/-- The first-phase embedding preserves the symbol read from the real input. -/
@[simp]
private lemma embedFirst_inputSymbol {input : List Symbol}
    (cfg : Cfg k₀ Symbol State₀ input) :
    (embedFirst tm₀ tm₁ cfg).inputSymbol = cfg.inputSymbol := rfl

/-- The first-phase embedding preserves every symbol read from a first-machine work tape. -/
private lemma compositionFirstWorkSymbols_embedFirst {input : List Symbol}
    (cfg : Cfg k₀ Symbol State₀ input) :
    compositionFirstWorkSymbols
      (embedFirst tm₀ tm₁ cfg).workTapeSymbols =
      cfg.workTapeSymbols := by
  funext i
  simp [compositionFirstWorkSymbols, Cfg.workTapeSymbols, embedFirst,
    compositionFirstTapeIdx]

/-- One first-machine step is one composite first-phase step. A halt of the first machine enters
the rewind phase instead of halting the composite machine. -/
private lemma step_embedFirst {input : List Symbol}
    (cfg : Cfg k₀ Symbol State₀ input) (hactive : cfg.state ≠ none) :
    (comp tm₀ tm₁).step (embedFirst tm₀ tm₁ cfg) =
      embedFirst tm₀ tm₁ (tm₀.step cfg) := by
  cases hstate : cfg.state with
  | none => exact absurd hstate hactive
  | some q =>
      have hinput := embedFirst_inputSymbol tm₀ tm₁ cfg
      have hwork := compositionFirstWorkSymbols_embedFirst tm₀ tm₁ cfg
      unfold step
      rw [show (embedFirst tm₀ tm₁ cfg).state =
        some (.first q) by simp [embedFirst, hstate]]
      rw [hstate]
      simp only [comp]
      rw [hinput, hwork]
      generalize htr : tm₀.tr q cfg.inputSymbol cfg.workTapeSymbols = trOut
      obtain ⟨inputMove, workActions, outS, q'⟩ := trOut
      simp only [htr]
      apply Cfg.ext
      · cases q' <;> rfl
      · rfl
      · funext i p
        by_cases hfirst : i.val < k₀
        · cases hwrite : (workActions ⟨i.val, hfirst⟩).1 <;>
            simp [embedFirst, compositionFirstWorkActions, hfirst, hwrite]
        · by_cases hmiddle : i.val = k₀
          · cases outS <;>
              simp [embedFirst, compositionFirstWorkActions, hmiddle,
                idleWorkAction, listTape_append_single]
          · simp [embedFirst, compositionFirstWorkActions, hfirst, hmiddle,
              idleWorkAction]
      · funext i
        by_cases hfirst : i.val < k₀
        · simp [embedFirst, compositionFirstWorkActions, hfirst]
        · by_cases hmiddle : i.val = k₀
          · cases outS <;>
              simp [embedFirst, compositionFirstWorkActions, hmiddle,
                idleWorkAction]
          · simp [embedFirst, compositionFirstWorkActions, hfirst, hmiddle,
              idleWorkAction]
      · rfl

/-- Simulation of the first component up to a time at which it has not halted earlier. -/
lemma runFrom_firstPhase (input : List Symbol) (n : ℕ)
    (hactive : ∀ m < n, (tm₀.runFrom (tm₀.initCfg input) m).state ≠ none) :
    (comp tm₀ tm₁).runFrom ((comp tm₀ tm₁).initCfg input) n =
      embedFirst tm₀ tm₁
        (tm₀.runFrom (tm₀.initCfg input) n) := by
  induction n with
  | zero => simpa using (embedFirst_initCfg tm₀ tm₁ input).symm
  | succ n ih =>
      rw [tm₀.runFrom_succ_eq_step', (comp tm₀ tm₁).runFrom_succ_eq_step',
        ih (fun m hm => hactive m (by omega))]
      exact step_embedFirst tm₀ tm₁
        (tm₀.runFrom (tm₀.initCfg input) n) (hactive n (by omega))

/-- At position zero, the post-rewind classifier configuration is the classifier half of the
second machine's initial configuration. -/
private lemma intermediateCfg_classify_init {input : List Symbol}
    (cfg : Cfg k₀ Symbol State₀ input) :
    intermediateCfg tm₀ tm₁ cfg
        (.classify tm₁.q₀ .right) 0 =
      classifyCfg tm₀ tm₁ cfg (tm₁.initCfg cfg.output) .right := by
  ext i p <;>
    simp [intermediateCfg, embedFirst, classifyCfg, embedSecond, virtualInputPos]
  split_ifs <;> simp_all
  omega

/-- Entering the rewind phase moves the intermediate head one cell to the left. -/
private lemma step_rewindStart {input : List Symbol}
    (cfg : Cfg k₀ Symbol State₀ input) (hhalt : cfg.state = none) :
    (comp tm₀ tm₁).step (embedFirst tm₀ tm₁ cfg) =
      intermediateCfg tm₀ tm₁ cfg .rewind
        (cfg.output.length - 1) := by
  ext i p <;>
    simp [step, embedFirst, intermediateCfg, comp, hhalt,
      compositionMoveIntermediate, idleWorkAction] <;>
    split_ifs <;> simp_all <;> omega

/-- One rewind step over a nonblank intermediate cell. -/
private lemma step_rewind_some {input : List Symbol}
    (cfg : Cfg k₀ Symbol State₀ input) (pos : ℤ)
    (hcell : (listTape cfg.output pos).isSome) :
    (comp tm₀ tm₁).step
        (intermediateCfg tm₀ tm₁ cfg .rewind pos) =
      intermediateCfg tm₀ tm₁ cfg .rewind (pos - 1) := by
  ext i p <;>
    simp [step, intermediateCfg, embedFirst, comp, Cfg.workTapeSymbols,
      hcell, compositionMoveIntermediate, idleWorkAction, sub_eq_add_neg] <;>
    split_ifs <;> simp_all

/-- The blank just left of the intermediate output ends rewinding and moves the head to cell
zero for classification. -/
private lemma step_rewind_none {input : List Symbol}
    (cfg : Cfg k₀ Symbol State₀ input) (pos : ℤ)
    (hcell : listTape cfg.output pos = none) :
    (comp tm₀ tm₁).step
        (intermediateCfg tm₀ tm₁ cfg .rewind pos) =
      intermediateCfg tm₀ tm₁ cfg
        (.classify tm₁.q₀ .right) (pos + 1) := by
  ext i p <;>
    simp [step, intermediateCfg, embedFirst, comp, Cfg.workTapeSymbols,
      hcell, compositionMoveIntermediate, idleWorkAction] <;>
    split_ifs <;> simp_all

/-- A canonical list tape is nonblank at every position inside the represented list. -/
private lemma listTape_isSome_of_lt (xs : List Symbol) {r : ℕ} (h : r < xs.length) :
    (listTape xs ((xs.length : ℤ) - 1 - r)).isSome := by
  have hp : (xs.length : ℤ) - 1 - r = (xs.length - 1 - r : ℕ) := by omega
  rw [hp]
  simp [listTape]
  omega

/-- Rewinding scans exactly the cells occupied by the intermediate output. -/
private lemma runFrom_rewind {input : List Symbol}
    (cfg : Cfg k₀ Symbol State₀ input)
    (r : ℕ) (hr : r ≤ cfg.output.length) :
    (comp tm₀ tm₁).runFrom
        (intermediateCfg tm₀ tm₁ cfg .rewind
          ((cfg.output.length : ℤ) - 1)) r =
      intermediateCfg tm₀ tm₁ cfg .rewind
        ((cfg.output.length : ℤ) - 1 - r) := by
  induction r with
  | zero => simp [runFrom]
  | succ r ih =>
      rw [(comp tm₀ tm₁).runFrom_succ_eq_step', ih (by omega)]
      convert step_rewind_some tm₀ tm₁ cfg _
        (listTape_isSome_of_lt cfg.output (r := r) (by omega)) using 1
      congr 1
      omega

/-- The prefix of the post-halting phase that consists of entering and running the rewind loop. -/
lemma runFrom_firstHalt_rewind {input : List Symbol}
    (cfg : Cfg k₀ Symbol State₀ input) (hhalt : cfg.state = none)
    (r : ℕ) (hr : r ≤ cfg.output.length) :
    (comp tm₀ tm₁).runFrom
        (embedFirst tm₀ tm₁ cfg) (r + 1) =
      intermediateCfg tm₀ tm₁ cfg .rewind
        ((cfg.output.length : ℤ) - 1 - r) := by
  rw [(comp tm₀ tm₁).runFrom_succ_eq_step, step_rewindStart tm₀ tm₁ cfg hhalt]
  exact runFrom_rewind tm₀ tm₁ cfg r hr

/-- The configuration immediately after the rewind loop is the initial classifier
configuration at intermediate-tape position zero. -/
lemma runFrom_firstHalt_classify {input : List Symbol}
    (cfg : Cfg k₀ Symbol State₀ input) (hhalt : cfg.state = none) :
    (comp tm₀ tm₁).runFrom
        (embedFirst tm₀ tm₁ cfg) (cfg.output.length + 2) =
      intermediateCfg tm₀ tm₁ cfg
        (.classify tm₁.q₀ .right) 0 := by
  rw [(comp tm₀ tm₁).runFrom_succ_eq_step']
  rw [runFrom_firstHalt_rewind tm₀ tm₁ cfg hhalt cfg.output.length le_rfl]
  rw [show (cfg.output.length : ℤ) - 1 - cfg.output.length = -1 by omega]
  simpa using step_rewind_none tm₀ tm₁ cfg (-1) (by rfl)

/-- After rewinding, one classification step enters the second machine's initial configuration. -/
private lemma step_intermediateCfg_classify_init {input : List Symbol}
    (cfg : Cfg k₀ Symbol State₀ input) :
    (comp tm₀ tm₁).step
        (intermediateCfg tm₀ tm₁ cfg
          (.classify tm₁.q₀ .right) 0) =
      embedSecond tm₀ tm₁ cfg (tm₁.initCfg cfg.output) := by
  rw [intermediateCfg_classify_init]
  apply step_classifyCfg
  cases cfg.output <;>
    simp [compositionClassifyMode, inputMode, virtualInputPos,
      CompositionBoundary.inputMode, listTape]

/-- Starting from a halted first-machine configuration, rewinding and initialization take exactly
the output length plus three steps. -/
private lemma runFrom_firstHalt_to_secondInit {input : List Symbol}
    (cfg : Cfg k₀ Symbol State₀ input) (hhalt : cfg.state = none) :
    (comp tm₀ tm₁).runFrom
        (embedFirst tm₀ tm₁ cfg) (cfg.output.length + 3) =
      embedSecond tm₀ tm₁ cfg (tm₁.initCfg cfg.output) := by
  rw [(comp tm₀ tm₁).runFrom_succ_eq_step', runFrom_firstHalt_classify tm₀ tm₁ cfg hhalt]
  exact step_intermediateCfg_classify_init tm₀ tm₁ cfg

/-- Running the first phase and rewinding its output reaches the second machine's initial
configuration. -/
lemma runFrom_to_secondInit (input : List Symbol) (u : ℕ)
    (hhalt : (tm₀.runFrom (tm₀.initCfg input) u).state = none)
    (hactive : ∀ m < u, (tm₀.runFrom (tm₀.initCfg input) m).state ≠ none) :
    (comp tm₀ tm₁).runFrom ((comp tm₀ tm₁).initCfg input)
        (u + ((tm₀.runFrom (tm₀.initCfg input) u).output.length + 3)) =
      embedSecond tm₀ tm₁
        (tm₀.runFrom (tm₀.initCfg input) u)
        (tm₁.initCfg ((tm₀.runFrom (tm₀.initCfg input) u).output)) := by
  rw [(comp tm₀ tm₁).runFrom_add, runFrom_firstPhase tm₀ tm₁ input u hactive,
    runFrom_firstHalt_to_secondInit tm₀ tm₁ _ hhalt]

end Turing.MultiTapeTM.Composition
