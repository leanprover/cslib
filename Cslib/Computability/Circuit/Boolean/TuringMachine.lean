/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas
public import Cslib.Computability.Circuit.Boolean.PPoly
public import Cslib.Computability.Complexity.PolynomialTime
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic.DeriveFintype

/-!
# Turing machine simulation by Boolean circuits

A bounded run is unrolled into circuits for the control state, head positions and tape cells.
Each step reads the symbols under the heads once, applies the fixed transition table,
then updates the configuration observations and emits an optional output symbol.
Heads remain within the time bound of their starting positions, so the circuit only stores a
finite window of each work tape. A separate packing circuit collects the emitted symbols into
a frame holding the output word.

The bounds are deliberately coarse polynomials. The resulting inclusion rules let `fun_prop`
use an `FP` or `P` hypothesis, or a machine's verified polynomial running-time bound.

## References

* [Sanjeev Arora and Boaz Barak, *Computational Complexity: A Modern Approach*,
  Section 6.1][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.TuringSimulation

open Turing BitString.Encoding

variable {k : ℕ} {State : Type*}

/-- The work-tape window visible within the chosen time bound. -/
def window (bound : ℕ) : Finset ℤ := Finset.Icc (-bound) bound

@[simp] theorem card_window (bound : ℕ) : (window bound).card = 2 * bound + 1 := by
  simp only [window, Int.card_Icc]
  lia

/-- Individual observations of a configuration, avoiding enumeration of whole tapes. -/
inductive Feature (k bound : ℕ) (State : Type*)
  | state (value : Option State)
  | inputPos (pos : Fin (bound + 2))
  | workPos (tape : Fin k) (pos : ↥(window bound))
  | cell (tape : Fin k) (pos : ↥(window bound)) (value : Option Bool)
  deriving Fintype

@[simp] theorem card_feature [Fintype State] (k bound : ℕ) :
    Fintype.card (Feature k bound State) = Fintype.card (Option State) +
      (bound + 2 + (k * (2 * bound + 1) + k * ((2 * bound + 1) * 3))) := by
  rw [← Fintype.card_congr (proxy_equiv% (Feature k bound State))]
  simp

/-- Interpret a configuration observation as a Boolean indicator. -/
def observe [DecidableEq State] {bound : ℕ} {input : BitString} (cfg : Cfg k Bool State input) :
    Feature k bound State → Bool
  | .state q => decide (cfg.state = q)
  | .inputPos j => decide (cfg.inputPos.val = j.val)
  | .workPos i z => decide (cfg.workTapePos i = z.val)
  | .cell i z b => decide (cfg.workTapes i z.val = b)

/-- The finite information read by the transition table. -/
structure Control (k : ℕ) (State : Type*) where
  /-- Current state, or `none` after halting. -/
  state : Option State
  /-- Symbol under the input head, or `none` at an end marker. -/
  input : Option Bool
  /-- Symbols under the work heads, with `none` denoting a blank cell. -/
  work : Fin k → Option Bool
  deriving Fintype, DecidableEq

/-- Read the transition table's arguments from a configuration. -/
def control {input : BitString} (cfg : Cfg k Bool State input) : Control k State :=
  ⟨cfg.state, cfg.inputSymbol, cfg.workTapeSymbols⟩

/-- A halted configuration issues an idle command, so every step has the same interface. -/
noncomputable def command (tm : MultiTapeTM k Bool State)
    (view : Control k State) : Action k Bool State :=
  match view.state with
  | none => ⟨0, fun _ => (none, 0), none, none⟩
  | some q => tm.tr q view.input view.work

/-- The command interface agrees exactly with the library's Turing machine step. -/
theorem command_apply (tm : MultiTapeTM k Bool State) {input : BitString}
    (cfg : Cfg k Bool State input) :
    (command tm (control cfg)).apply cfg = tm.step cfg := by
  cases hq : cfg.state with
  | none =>
    rw [MultiTapeTM.step_of_halt hq]
    apply Cfg.ext <;> simp [command, control, hq, Action.apply]
  | some q => rw [MultiTapeTM.step_of_state hq, command]; simp [control, hq]

/-- The optional output field of a command is the symbol emitted by that step. -/
theorem command_output (tm : MultiTapeTM k Bool State) {input : BitString}
    (cfg : Cfg k Bool State input) :
    (command tm (control cfg)).output = tm.outputSymbol cfg := by
  cases hq : cfg.state <;> simp [command, control, MultiTapeTM.outputSymbol, hq]

/-! ### The observable effects of one transition

Each feature of the successor configuration is a fixed function of the command and of the
features of the current configuration. These equations are independent of circuit synthesis.
-/

section ObserveStep

variable [DecidableEq State] (tm : MultiTapeTM k Bool State) {bound : ℕ} {input : BitString}
  (cfg : Cfg k Bool State input)

@[simp] theorem observe_step_state (q : Option State) :
    observe (bound := bound) (tm.step cfg) (.state q) =
      decide ((command tm (control cfg)).state = q) := by
  rw [← command_apply tm cfg]
  rfl

@[simp] theorem observe_step_inputPos (j : Fin (bound + 2)) :
    observe (tm.step cfg) (.inputPos j) = decide (min (input.length + 1)
      (((cfg.inputPos.val : ℤ) + ((command tm (control cfg)).inputTape : ℤ)).toNat) = j.val) := by
  rw [← command_apply tm cfg]
  simp only [observe, Action.apply_inputPos, val_moveInputPos_eq_min]

@[simp] theorem observe_step_workPos (i : Fin k) (z : ↥(window bound)) :
    observe (tm.step cfg) (.workPos i z) =
      decide (cfg.workTapePos i + (((command tm (control cfg)).workTapes i).2 : ℤ) = z.val) := by
  rw [← command_apply tm cfg]
  rfl

@[simp] theorem observe_step_cell (i : Fin k) (z : ↥(window bound)) (b : Option Bool) :
    observe (tm.step cfg) (.cell i z b) =
      if decide (cfg.workTapePos i = z.val) then
        (decide (((command tm (control cfg)).workTapes i).1 = none) &&
          decide (cfg.workTapes i z.val = b)) ||
            decide (((command tm (control cfg)).workTapes i).1 = some b)
      else decide (cfg.workTapes i z.val = b) := by
  rw [← command_apply tm cfg]
  simp only [observe, Action.apply_workTapes]
  cases ((command tm (control cfg)).workTapes i).1 <;> split_ifs <;> simp_all [eq_comm]

end ObserveStep

variable {n : ℕ} {input : (Fin n → Bool) → BitString}

/-- The Boolean functions recording all observations of a configuration family. -/
def configurationTargets [DecidableEq State] (bound : ℕ)
    (cfg : (x : Fin n → Bool) → Cfg k Bool State (input x)) :
    Set (BooleanFunction n) :=
  Set.range fun (feature : Feature k bound State) x => observe (cfg x) feature

/-- Indicators for every possible input to the transition table. -/
def controlTargets [DecidableEq State]
    (cfg : (x : Fin n → Bool) → Cfg k Bool State (input x)) :
    Set (BooleanFunction n) :=
  observations (fun view v => decide (view = v)) fun x => control (cfg x)

/-- Cost of testing one value of the state and the symbols currently under the heads. -/
def controlCost (k : ℕ) (bound : ℕ) : ℕ :=
  (3 * (bound + 2) + 1) + (k * (2 * (2 * bound + 1) + 2) + 1) + 2

/-- Read a symbol by selecting the input position, treating position zero as the left marker. -/
theorem synthesis_inputSymbol {bound : ℕ} {s : Set (BooleanFunction n)}
    (cfg : (x : Fin n → Bool) → Cfg k Bool State (input x))
    (hinput : ∀ x, (input x).length ≤ bound)
    (hpos : ∀ j : Fin (bound + 2),
      Synthesis interpretation s {fun x => decide ((cfg x).inputPos.val = j.val)} 0)
    (hbit : ∀ j ≤ bound, ∀ b : Option Bool,
      Synthesis interpretation s {fun x => decide ((input x)[j]? = b)} 0) (b : Option Bool) :
    Synthesis interpretation s {fun x => decide ((cfg x).inputSymbol = b)}
      (3 * (bound + 2) + 1) := by
  have hb (j : ℕ) (hj : j ∈ Finset.range (bound + 2)) :
      Synthesis interpretation s
        {fun x => decide ((if j = 0 then none else (input x)[j - 1]?) = b)} 1 := by
    by_cases hj0 : j = 0
    · simpa only [hj0, ite_true] using Synthesis.const (s := s) (decide (none = b))
    · have hj' : j - 1 ≤ bound := by simp only [Finset.mem_range] at hj; lia
      simpa only [ite_eq_right hj0] using (hbit (j - 1) hj' b).mono_cost (by lia : 0 ≤ 1)
  have h := Synthesis.select (Finset.range (bound + 2)) (fun x => (cfg x).inputPos.val)
    (fun j x => decide ((if j = 0 then none else (input x)[j - 1]?) = b))
    (fun x => by
        have := (cfg x).inputPos.isLt
        have := hinput x
        simpa only [Finset.mem_range] using (show (cfg x).inputPos.val < bound + 2 by lia))
    (fun j hj => hpos ⟨j, Finset.mem_range.mp hj⟩) hb
  simpa only [← Cfg.inputSymbol_eq_getElem?, Finset.card_range, zero_add, Nat.mul_comm] using h

/-- Test the state and symbols under the heads using the available configuration observations. -/
theorem synthesis_control [DecidableEq State] {bound : ℕ}
    (cfg : (x : Fin n → Bool) → Cfg k Bool State (input x))
    (hinput : ∀ x : Fin n → Bool, (input x).length ≤ bound)
    (hheads : ∀ x i, |(cfg x).workTapePos i| ≤ (bound : ℤ)) (v : Control k State) :
    Synthesis interpretation
      (Word.observations input bound ∪ configurationTargets bound cfg)
      {fun x => decide (control (cfg x) = v)} (controlCost k bound) := by
  let s := Word.observations input bound ∪ configurationTargets bound cfg
  have hcfg (feature : Feature k bound State) :
      Synthesis interpretation s {fun x => observe (cfg x) feature} 0 :=
    Synthesis.of_mem (Set.mem_union_right _ ⟨feature, rfl⟩)
  have hbit (j : ℕ) (hj : j ≤ bound) (b : Option Bool) :
      Synthesis interpretation s {fun x => decide ((input x)[j]? = b)} 0 :=
    Synthesis.of_mem (Set.mem_union_left _ (Word.symbol_mem_observations ⟨j, by lia⟩ b))
  have hinputSymbol := synthesis_inputSymbol cfg hinput (fun j => hcfg (.inputPos j)) hbit
  have hwork (i : Fin k) (b : Option Bool) :
      Synthesis interpretation s {fun x => decide ((cfg x).workTapeSymbols i = b)}
        (2 * (2 * bound + 1) + 1) := by
    have h := Synthesis.select (s := s) (window bound) (fun x => (cfg x).workTapePos i)
      (fun z x => decide ((cfg x).workTapes i z = b))
      (fun x => by simpa only [window, Finset.mem_Icc, abs_le] using hheads x i)
      (fun z hz => hcfg (.workPos i ⟨z, hz⟩)) (fun z hz => hcfg (.cell i ⟨z, hz⟩ b))
    exact h.mono_cost (by simp [Nat.mul_comm])
  obtain ⟨q, b, work⟩ := v
  have hw := Synthesis.forall_mem Finset.univ
    (fun i x => decide ((cfg x).workTapeSymbols i = work i))
    (fun _ => 2 * (2 * bound + 1) + 1) (fun i _ => hwork i (work i))
  refine ((((hcfg (.state q)).and (hinputSymbol b)).and hw).congr fun x => ?_).mono_cost ?_
  · apply Bool.eq_iff_iff.mpr
    simp [control, observe, Control.mk.injEq, funext_iff, and_assoc]
  · simp only [controlCost, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    lia

/-- Cost of computing every indicator of the transition table's input, once per step. -/
def readCost [Fintype State] (k : ℕ) (bound : ℕ) : ℕ :=
  Fintype.card (Control k State) * controlCost k bound

/-- Applying the fixed transition table to the available control indicators has constant cost. -/
def commandCost [Fintype State] (k : ℕ) : ℕ := Fintype.card (Control k State) + 1

/-- Any Boolean observation of the command is a fixed lookup on the available control indicators. -/
theorem synthesis_command [Fintype State] [DecidableEq State]
    (tm : MultiTapeTM k Bool State) {s : Set (BooleanFunction n)}
    (cfg : (x : Fin n → Bool) → Cfg k Bool State (input x))
    (op : Action k Bool State → Bool) :
    Synthesis interpretation (s ∪ controlTargets cfg)
      {fun x => op (command tm (control (cfg x)))} (commandCost (State := State) k) := by
  have hv (view : Control k State) : Synthesis interpretation (s ∪ controlTargets cfg)
      {fun x => decide (control (cfg x) = view)} 0 :=
    (synthesis_observe (fun view v => decide (view = v)) (fun x => control (cfg x))
      view).mono_sources Set.subset_union_right
  simpa [commandCost] using Synthesis.of_indicators (op ∘ command tm) hv

/-- Sum of the bounds for updating the state, work head, input head, and tape cell. -/
def featureCost [Fintype State] (k : ℕ) (bound : ℕ) : ℕ :=
  let lookup := commandCost (State := State) k
  let workHead := (2 * bound + 1) * (lookup + 2) + 1
  let inputHead := (bound + 2) * (bound + 1) * (lookup + 3) + 1
  let cell := 2 * lookup + 6
  lookup + workHead + inputHead + cell

/-- One step computes every configuration observation with a polynomial number of gates. -/
theorem synthesis_step_feature [Fintype State] [DecidableEq State]
    (tm : MultiTapeTM k Bool State) {bound : ℕ}
    (cfg : (x : Fin n → Bool) → Cfg k Bool State (input x))
    (hinput : ∀ x : Fin n → Bool, (input x).length ≤ bound)
    (hheads : ∀ x i, |(cfg x).workTapePos i| ≤ (bound : ℤ)) (feature : Feature k bound State) :
    Synthesis interpretation
      ((Word.observations input bound ∪ configurationTargets bound cfg) ∪
        controlTargets cfg)
      {fun x => observe (tm.step (cfg x)) feature} (featureCost (State := State) k bound) := by
  let s := (Word.observations input bound ∪ configurationTargets bound cfg) ∪
    controlTargets cfg
  let action x := command tm (control (cfg x))
  let c := commandCost (State := State) k
  have hCommand (op : Action k Bool State → Bool) :
      Synthesis interpretation s {fun x => op (action x)} c :=
    synthesis_command tm cfg op
  have hFeature (feature : Feature k bound State) :
      Synthesis interpretation s {fun x => observe (cfg x) feature} 0 :=
    Synthesis.of_mem (Set.mem_union_left _ (Set.mem_union_right _ ⟨feature, rfl⟩))
  cases feature with
  | state q =>
    simp only [observe_step_state]
    exact (hCommand (fun a => decide (a.state = q))).mono_cost
      (show c ≤ featureCost (State := State) k bound by
        dsimp [featureCost, c]; lia)
  | inputPos j =>
    simp only [observe_step_inputPos]
    have hLength len := (Word.synthesis_length (f := input) (capacity := bound) len).mono_sources
      (s' := s) (Set.subset_union_left.trans Set.subset_union_left)
    -- The input head is clamped at the end marker, so select both position and input length.
    have h := Synthesis.select₂ (s := s) (Finset.range (bound + 2)) (Finset.range (bound + 1))
      (fun x => (cfg x).inputPos.val) (fun x => (input x).length)
      (fun pos len x => decide (min (len + 1)
        (((pos : ℤ) + ((action x).inputTape : ℤ)).toNat) = j.val))
      (fun x => by
        have := (cfg x).inputPos.isLt
        have := hinput x
        simpa only [Finset.mem_range] using (show (cfg x).inputPos.val < bound + 2 by lia))
      (fun x => by simp only [Finset.mem_range]; have := hinput x; lia)
      (fun pos hp => hFeature (.inputPos ⟨pos, Finset.mem_range.mp hp⟩))
      (fun len hl => hLength ⟨len, Finset.mem_range.mp hl⟩)
      (fun pos _ len _ => hCommand (fun a => decide (min (len + 1)
        (((pos : ℤ) + (a.inputTape : ℤ)).toNat) = j.val)))
    exact h.mono_cost
      (by simp only [Finset.card_range, featureCost]; lia)
  | workPos i z =>
    simp only [observe_step_workPos]
    have h := Synthesis.select (s := s) (window bound) (fun x => (cfg x).workTapePos i)
      (fun pos x => decide (pos + (((action x).workTapes i).2 : ℤ) = z.val))
      (fun x => by simpa only [window, Finset.mem_Icc, abs_le] using hheads x i)
      (fun pos hp => hFeature (.workPos i ⟨pos, hp⟩))
      (fun pos _ => hCommand (fun a => decide (pos + ((a.workTapes i).2 : ℤ) = z.val)))
    exact h.mono_cost
      (by simp only [card_window, featureCost]; lia)
  | cell i z b =>
    simp only [observe_step_cell]
    have hOld := hFeature (.cell i z b)
    have hKeep := (hCommand (fun a => decide ((a.workTapes i).1 = none))).and hOld
    have hWrite := hCommand (fun a => decide ((a.workTapes i).1 = some b))
    have h := (hFeature (.workPos i z)).ite (hKeep.or hWrite) hOld
    exact h.mono_cost (by dsimp [featureCost]; lia)

/-- Two observations of an optional emitted symbol: its presence and its value. -/
def outputBit (symbol : Option Bool) (present : Bool) : Bool :=
  if present then symbol.isSome else symbol.getD false

/-- The presence and value of the symbol emitted by a configuration family. -/
def outputTargets (tm : MultiTapeTM k Bool State)
    (cfg : (x : Fin n → Bool) → Cfg k Bool State (input x)) :
    Set (BooleanFunction n) :=
  Set.range fun present x => outputBit (tm.outputSymbol (cfg x)) present

/-- Simultaneously compute the next configuration and the emitted symbol. -/
theorem synthesis_step [Fintype State] [DecidableEq State]
    (tm : MultiTapeTM k Bool State) {bound : ℕ}
    (cfg : (x : Fin n → Bool) → Cfg k Bool State (input x))
    (hinput : ∀ x : Fin n → Bool, (input x).length ≤ bound)
    (hheads : ∀ x i, |(cfg x).workTapePos i| ≤ (bound : ℤ)) :
    Synthesis interpretation
      (Word.observations input bound ∪ configurationTargets bound cfg)
      (configurationTargets bound (fun x => tm.step (cfg x)) ∪ outputTargets tm cfg)
      (readCost (State := State) k bound +
        (Fintype.card (Feature k bound State) + 2) * featureCost (State := State) k bound) := by
  have hread : Synthesis interpretation
      (Word.observations input bound ∪ configurationTargets bound cfg)
      (controlTargets cfg) (readCost (State := State) k bound) :=
    Boolean.synthesis_observations (fun view v => decide (view = v)) (fun x => control (cfg x))
      (synthesis_control cfg hinput hheads)
  have hc := Synthesis.family _ (fun _ => featureCost (State := State) k bound)
    (synthesis_step_feature tm cfg hinput hheads)
  have ho (present : Bool) : Synthesis interpretation
      ((Word.observations input bound ∪ configurationTargets bound cfg) ∪
        controlTargets cfg)
      {fun x => outputBit (tm.outputSymbol (cfg x)) present}
      (featureCost (State := State) k bound) := by
    have h := (synthesis_command tm
      (s := Word.observations input bound ∪ configurationTargets bound cfg) cfg
      (fun action => outputBit action.output present)).mono_cost
        (show commandCost (State := State) k ≤ featureCost (State := State) k bound by
          dsimp [featureCost]; lia)
    simpa only [command_output] using h
  simpa [configurationTargets, outputTargets, Nat.add_mul] using hread.trans
    (hc.union (Synthesis.family _ (fun _ => featureCost (State := State) k bound) ho))

/-- Observations of the current configuration and all symbols emitted so far. -/
def traceTargets [DecidableEq State] (tm : MultiTapeTM k Bool State)
    (input : (Fin n → Bool) → BitString) (bound t : ℕ) :
    Set (BooleanFunction n) :=
  configurationTargets bound (fun x => tm.runFrom (tm.initCfg (input x)) t) ∪
    Set.range (fun (ib : Fin t × Bool) x =>
      outputBit (tm.outputSymbol (tm.runFrom (tm.initCfg (input x)) ib.1.val)) ib.2)

/-- Unroll a bounded run, retaining previous output wires at each step. -/
theorem synthesis_run [Fintype State] [DecidableEq State]
    (tm : MultiTapeTM k Bool State)
    (input : (Fin n → Bool) → BitString) (bound t : ℕ) (hinput : ∀ x, (input x).length ≤ bound)
    (ht : t ≤ bound) :
    Synthesis interpretation
      (inputs n ∪ Word.observations input bound) (traceTargets tm input bound t)
      (Fintype.card (Feature k bound State) +
        t * (readCost (State := State) k bound + (Fintype.card (Feature k bound State) + 2) *
          featureCost (State := State) k bound)) := by
  let cfg (t : ℕ) (x : Fin n → Bool) := tm.runFrom (tm.initCfg (input x)) t
  have hheads (t : ℕ) (ht : t ≤ bound) (x : Fin n → Bool) (i : Fin k) :
      |(cfg t x).workTapePos i| ≤ (bound : ℤ) := by
    have h := tm.abs_workTapePos_runFrom_le (tm.initCfg (input x)) t i
    change |(cfg t x).workTapePos i - 0| ≤ (t : ℤ) at h
    rw [sub_zero] at h
    exact h.trans (Int.ofNat_le.mpr ht)
  induction t with
  | zero =>
    have hc (feature : Feature k bound State) : Synthesis interpretation
        (inputs n ∪ Word.observations input bound)
        {fun x => observe (tm.initCfg (input x)) feature} 1 := by
      convert Synthesis.const (observe (tm.initCfg []) feature) using 1
      congr 1
    have h := Synthesis.family _ (fun _ => 1) hc
    apply h.mono Set.Subset.rfl ?_ (by simp)
    rintro f (hf | ⟨⟨i, b⟩, h⟩)
    · simpa only [configurationTargets, MultiTapeTM.runFrom, Function.iterate_zero_apply] using hf
    · exact i.elim0
  | succ t ih =>
    have hstep := (synthesis_step tm (cfg t) hinput (hheads t (by lia))).mono_sources
      (show Word.observations input bound ∪ configurationTargets bound (cfg t) ⊆
          (inputs n ∪ Word.observations input bound) ∪ traceTargets tm input bound t from
        Set.union_subset (Set.subset_union_right.trans Set.subset_union_left)
          (Set.subset_union_left.trans Set.subset_union_right))
    apply ((ih (by lia)).comp hstep).mono Set.Subset.rfl ?_ (by simp [Nat.add_mul, Nat.add_assoc])
    rintro f (hf | ⟨⟨i, b⟩, rfl⟩)
    · apply Set.mem_union_right _ (Set.mem_union_left _ ?_)
      simpa only [configurationTargets, cfg, MultiTapeTM.runFrom,
        Function.iterate_succ_apply'] using hf
    · refine Fin.lastCases ?_ (fun j => ?_) i
      · exact Set.mem_union_right _ (Set.mem_union_right _ ⟨b, rfl⟩)
      · exact Set.mem_union_left _ (Set.mem_union_right _ ⟨⟨j, b⟩, rfl⟩)

/-- Pack the emitted symbols into a frame holding the output word. -/
theorem synthesis_output [DecidableEq State] (tm : MultiTapeTM k Bool State)
    (input : (Fin n → Bool) → BitString) (bound t : ℕ) :
    Synthesis interpretation (traceTargets tm input bound t)
      (Set.range fun j x => encode t (tm.runFrom (tm.initCfg (input x)) t).output j)
      (4 * (t + 1) * (1 + 6 * t) + Encoding.encodeCost t) := by
  let symbols (i : ℕ) (x : Fin n → Bool) :=
    tm.outputSymbol (tm.runFrom (tm.initCfg (input x)) i)
  have hs : WordSynthesis (traceTargets tm input bound t)
      (fun x => (List.range t).filterMap (fun i => symbols i x)) t (4 * (t + 1) * (1 + 6 * t)) := by
    simpa only [List.length_range] using
      WordSynthesis.filterMap (s := traceTargets tm input bound t) symbols (List.range t)
        (fun i hi => Set.mem_union_right _ ⟨⟨⟨i, List.mem_range.mp hi⟩, true⟩, rfl⟩)
        (fun i hi => Set.mem_union_right _ ⟨⟨⟨i, List.mem_range.mp hi⟩, false⟩, rfl⟩)
  simpa only [tm.runFrom_output_eq_filterMap, MultiTapeNTM.initCfg, Cfg.init,
    List.nil_append, symbols] using hs.encode

/-- Output capacity and gate budget for reading, initializing, running, and packing the output. -/
noncomputable def runCost [Fintype State] (k bound : ℕ) : ℕ :=
  let input := Encoding.observationsCost bound bound
  let initial := Fintype.card (Feature k bound State)
  let step := readCost (State := State) k bound +
    (initial + 2) * featureCost (State := State) k bound
  let output := 4 * (bound + 1) * (1 + 6 * bound) + 2 * bound * (bound + 2)
  bound + input + initial + bound * step + output

/-- For a fixed machine, the bounded simulation cost has polynomial growth. -/
@[fun_prop] theorem polynomiallyBounded_runCost [Fintype State] (k : ℕ) :
    PolynomiallyBounded (runCost (State := State) k) := by
  unfold runCost
  simp only [card_feature, featureCost]
  fun_prop [readCost, controlCost]

/-- A circuit simulates exactly `t` steps and produces a frame holding the output word. -/
theorem exists_circuit_run [Fintype State]
    (tm : MultiTapeTM k Bool State) (n bound t : ℕ) (hn : n ≤ bound) (ht : t ≤ bound) :
    ∃ c : Circuit signature (width n) (width t),
      (∀ x, decode (c.eval interpretation x) =
        (tm.runFrom (tm.initCfg (decode x)) t).output) ∧
      t + c.size ≤ runCost (State := State) k bound := by
  classical
  have hinput (x : Frame n) : (decode x).length ≤ bound := (length_decode_le x).trans hn
  have hs := (Encoding.synthesis_observations n bound).trans
    (synthesis_run tm decode bound t hinput ht)
  have hout := hs.trans ((synthesis_output tm decode bound t).mono_sources Set.subset_union_right)
  obtain ⟨c, hc, hsize⟩ := hout.exists_circuit_outputs
  refine ⟨c, fun x => ?_, ?_⟩
  · rw [hc]
    exact decode_encode_of_length_le
      (by simpa using tm.length_output_runFrom_le (tm.initCfg (decode x)) t)
  · have hobs : Encoding.observationsCost n bound ≤ Encoding.observationsCost bound bound := by
      unfold Encoding.observationsCost Encoding.symbolCost
      gcongr
    have htime := Nat.mul_le_mul_right
      (readCost (State := State) k bound +
        (Fintype.card (Feature k bound State) + 2) * featureCost (State := State) k bound) ht
    have hpack : 4 * (t + 1) * (1 + 6 * t) + Encoding.encodeCost t ≤
        4 * (bound + 1) * (1 + 6 * bound) + 2 * bound * (bound + 2) := by
      have hw := width_le t
      unfold Encoding.encodeCost
      gcongr
      exact hw.trans (Nat.mul_le_mul_left 2 ht)
    dsimp only [runCost]
    lia

/-- A finite binary machine with a polynomially bounded running time computes an FP/poly
function. The finiteness instance comes last so `fun_prop` can infer the machine from `h`. -/
@[fun_prop] theorem fpPoly_of_computes (tm : MultiTapeTM k Bool State)
    {f : BitString → BitString} {time space : BitString → ℕ}
    (h : tm.ComputesFunInTimeAndSpace (Function.Embedding.refl _) (Function.Embedding.refl _) f
      time space) (htime : PolynomiallyBoundedIn time List.length) [Finite State] :
    FPPoly f := by
  classical
  let : Fintype State := Fintype.ofFinite State
  obtain ⟨b, hb, htb⟩ := htime
  obtain ⟨p, hp, hpb, hbp⟩ := hb.exists_monotone
  refine ⟨fun n => runCost (State := State) k (n + p n), by fun_prop, fun n => ?_⟩
  obtain ⟨c, hc, hs⟩ := exists_circuit_run tm n (n + p n) (p n) (by lia) (by lia)
  refine ⟨p n, c.eval interpretation, fun x => ?_, ?_⟩
  · rw [hc]
    exact (h (decode x)).runFrom_output
      ((htb _).trans ((hbp _).trans (hp (length_decode_le x))))
  · exact (Nat.add_le_add_left (complexity_le_of_computes c (fun _ => rfl)) _).trans hs

end Cslib.Circuits.Boolean.TuringSimulation

namespace Cslib.Complexity

open Circuits.Boolean

/-- Every polynomial-time word function has polynomial-size nonuniform Boolean circuits. -/
@[fun_prop] theorem FP.fpPoly {f : BitString → BitString} (hf : FP f) : FPPoly f := by
  obtain ⟨time, ht, space, k, State, hfinite, tm, htm⟩ := hf
  exact TuringSimulation.fpPoly_of_computes tm htm ht

/-- Every polynomial-time predicate has polynomial-size nonuniform Boolean circuits. -/
@[fun_prop] theorem P.pPoly {f : BitString → Bool} (hf : P f) : PPoly f :=
  pPoly_iff_fpPoly.mpr hf.fpPoly

end Cslib.Complexity
