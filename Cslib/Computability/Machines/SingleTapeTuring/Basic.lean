/-
Copyright (c) 2025 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey TODO add the authors of the mathlib file this is based on
-/

module

public import Cslib.Foundations.Data.OTape
public import Cslib.Foundations.Semantics.ReductionSystem.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs

@[expose] public section

/-!
# Single-Tape Turing Machine

Defines a single-tape Turing machine over the alphabet of `Option Bool`,
where `none` represents a blank OTape symbol.

## TODOs

- Generalize Bool to an arbitrary (finite?) alphabet
- switch transition system to use the `ReductionSystem` framework
- refactor polynomial time to another file
- remove unfold

-/

open Cslib

namespace Turing

namespace BinTM0

/-- A Turing machine "statement" is just a command to move
  left or right, and write a symbol on the OTape. -/
def Stmt := (Option Bool) × Option (Dir)
deriving Inhabited

end BinTM0

/-- A TM0 over the alphabet of Option Bool (none is blank OTape symbol). -/
structure BinTM0 where
  /-- type of state labels -/
  (Λ : Type)
  /-- finiteness of the state type -/
  [FintypeΛ : Fintype Λ]
  /-- Initial state -/
  (q₀ : Λ)
  /-- Transition function, mapping a state and a head symbol
  to a Stmt to invoke, and optionally a new state (none for halt) -/
  (M : Λ → (Option Bool) → (Turing.BinTM0.Stmt × Option Λ))


namespace BinTM0

section

variable (tm : BinTM0)

instance : Inhabited tm.Λ :=
  ⟨tm.q₀⟩

instance : Fintype tm.Λ :=
  tm.FintypeΛ

instance inhabitedStmt : Inhabited (Stmt) := inferInstance

/-- The type of configurations (functions) corresponding to this TM. -/
structure Cfg : Type where
  /-- the state of the TM (or none for the halting state) -/
  state : Option tm.Λ
  /-- the OTape contents, which -/
  OTape : OTape (Bool)
deriving Inhabited

/-- The step function corresponding to this TM. -/
@[simp]
def step : tm.Cfg → Option tm.Cfg :=
  fun ⟨q, t⟩ =>
    match q with
    -- If in the halting state, there is no next configuration
    | none => none
    -- If in state q'
    | some q' =>
      -- Look up the transition function
      match tm.M q' t.head with
      | ⟨(wr, dir), q''⟩ =>
          -- enter a new configuration
          some ⟨
            -- With state q'' (or none for halting)
            q'',
            -- And OTape updated according to the Stmt
            (t.write wr).move? dir⟩
end

/-- The initial configuration corresponding to a list in the input alphabet. -/
def initCfg (tm : BinTM0) (s : List Bool) : tm.Cfg := ⟨some tm.q₀, OTape.mk₁ s⟩

/-- The final configuration corresponding to a list in the output alphabet.
(We demand that the head halts at the leftmost position of the output.)
-/
def haltCfg (tm : BinTM0) (s : List (Bool)) : tm.Cfg := ⟨none, OTape.mk₁ s⟩

/--
The `ReductionSystem` corresponding to a `BinTM0` is defined by the `step` function,
which maps a configuration to its next configuration if it exists.
-/
def ReductionSystem (tm : BinTM0) : Cslib.ReductionSystem (tm.Cfg) :=
  { Red := fun cfg cfg' => tm.step cfg = some cfg' }
-- TODO use this, rather than the current setup, or better yet an LTS? 


noncomputable def Cfg.space_used (tm : BinTM0) (cfg : tm.Cfg) : ℕ :=
  cfg.OTape.space_used

lemma Cfg.space_used_initCfg (tm : BinTM0) (s : List Bool) :
    (tm.initCfg s).space_used = max 1 s.length := by
  simp [initCfg, Cfg.space_used, OTape.space_used_mk₁]

lemma Cfg.space_used_haltCfg (tm : BinTM0) (s : List Bool) :
    (tm.haltCfg s).space_used = max 1 s.length := by
  simp [haltCfg, Cfg.space_used, OTape.space_used_mk₁]

lemma Cfg.space_used_step {tm : BinTM0} (cfg cfg' : tm.Cfg)
    (hstep : tm.step cfg = some cfg') : cfg'.space_used ≤ cfg.space_used + 1 := by
  obtain ⟨_ | q, tape⟩ := cfg
  · simp [step] at hstep
  · simp only [step] at hstep
    generalize hM : tm.M q tape.head = result at hstep
    obtain ⟨⟨wr, dir⟩, q''⟩ := result
    cases hstep; cases dir with
    | none => simp [Cfg.space_used, OTape.move?, OTape.space_used_write]
    | some d =>
      have := OTape.space_used_move (tape.write wr) d
      simp only [Cfg.space_used, OTape.move?, OTape.space_used_write] at this ⊢; exact this


/-- A proof of tm outputting l' when given l. -/
def OutputsInTime (tm : BinTM0) (l : List (Bool)) (l' : Option (List (Bool))) :=
  EvalsToInTime tm.step (initCfg tm l) ((Option.map (haltCfg tm)) l')

/-- A proof of tm outputting l' when given l in at most m steps. -/
def OutputsWithinTime (tm : BinTM0) (l : List (Bool)) (l' : Option (List (Bool)))
    (m : ℕ) :=
  EvalsToWithinTime tm.step (initCfg tm l) ((Option.map (haltCfg tm)) l') m

/-- A Turing machine + a proof it outputsInTime `f`. -/
structure Computable (f : List Bool → List Bool) where
  /-- the underlying bundled TM0 -/
  tm : BinTM0
  steps : ℕ
  /-- a proof this machine outputsInTime `f` -/
  outputsFun :
    ∀ a,
      OutputsInTime tm a
        (Option.some (f a))
        steps

/-- A Turing machine + a time function +
a proof it outputsInTime `f` in at most `time(input.length)` steps. -/
structure TimeComputable (f : List Bool → List Bool) where
  /-- the underlying bundled TM0 -/
  tm : BinTM0
  /-- a time function -/
  time : ℕ → ℕ
  /-- proof this machine outputsInTime `f` in at most `time(input.length)` steps -/
  outputsFun :
    ∀ a,
      tm.OutputsWithinTime
        a
        (Option.some (f a))
        (time a.length)

/-- A Turing machine computing the identity. -/
def idComputer : BinTM0 where
  Λ := PUnit
  q₀ := PUnit.unit
  M := fun _ b => ⟨(b, none), none⟩

noncomputable section

/-- A proof that the identity map on α is computable in time. -/
def TimeComputable.id :
    @TimeComputable id :=
  ⟨idComputer, fun _ => 1, fun x => by
    use 1
    simp only [le_refl, id_eq, Option.map_some, true_and]
    simp only [EvalsToInTime, initCfg, haltCfg, idComputer,
      Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
    congr 1⟩

def compComputer {f : List Bool → List Bool} {g : List Bool → List Bool}
    (hf : TimeComputable f)
    (hg : TimeComputable g) :
    BinTM0 :=
  {
    Λ := hf.tm.Λ ⊕ hg.tm.Λ
    q₀ := Sum.inl hf.tm.q₀
    M := fun q h =>
      match q with
      -- If we are in the first machine's states, run that machine
      | Sum.inl ql => match hf.tm.M ql (h) with
        -- The action should be the same, and the state should either be the corresponding state
        -- in the first machine, or transition to the start state of the second machine if halting
        | (ql', stmt) => (ql',
            match stmt with
            -- If it halts, transition to the start state of the second machine
            | none => some (Sum.inr hg.tm.q₀)
            -- Otherwise continue as normal
            | _ => Option.map Sum.inl stmt)
      -- If we are in the second machine's states, run that machine
      | Sum.inr qr =>
        match hg.tm.M qr (h) with
        -- The action should be the same, and the state should be the corresponding state
        -- in the second machine, or halting if the second machine halts
        | (qr', stmt) => (qr',
            match stmt with
            -- If it halts, transition to the halting state
            | none => none
            -- Otherwise continue as normal
            | _ => Option.map Sum.inr stmt)
  }

lemma compComputer_q₀_eq (f : List Bool → List Bool) (g : List Bool → List Bool)
  (hf : TimeComputable f)
  (hg : TimeComputable g) :
    (compComputer hf hg).q₀ = Sum.inl hf.tm.q₀ :=
  rfl

/-- Lift a config over a tm to a config over the comp -/
def liftCompCfg_left {f : List Bool → List Bool} {g : List Bool → List Bool}
    (hf : TimeComputable f)
    (hg : TimeComputable g)
    (cfg : hf.tm.Cfg) :
    (compComputer hf hg).Cfg :=
  {
    state := Option.map Sum.inl cfg.state
    OTape := cfg.OTape
  }

def liftCompCfg_right {f : List Bool → List Bool} {g : List Bool → List Bool}
    (hf : TimeComputable f)
    (hg : TimeComputable g)
    (cfg : hg.tm.Cfg) :
    (compComputer hf hg).Cfg :=
  {
    state := Option.map Sum.inr cfg.state
    OTape := cfg.OTape
  }

theorem map_liftCompCfg_left_step
    {f : List Bool → List Bool} {g : List Bool → List Bool}
    (hf : TimeComputable f) (hg : TimeComputable g)
    (x : hf.tm.Cfg)
    (hx : ∀ cfg, hf.tm.step x = some cfg → cfg.state.isSome) :
    Option.map (liftCompCfg_left hf hg) (hf.tm.step x) =
      (compComputer hf hg).step (liftCompCfg_left hf hg x) := by
  cases x with
  | mk state OTape =>
    cases state with
    | none =>
      -- x is already in halting state, step returns none on both sides
      simp only [step, liftCompCfg_left, Option.map_none, compComputer]
    | some q =>
      simp only [step, liftCompCfg_left, compComputer, Option.map_some]
      -- Get the transition result
      generalize hM : hf.tm.M q OTape.head = result
      obtain ⟨⟨wr, dir⟩, nextState⟩ := result
      simp only
      -- Case on whether the next state is none (halting) or some
      cases nextState with
      | none =>
        -- The first machine halts, but hx says the result has state.isSome
        simp only [step, hM] at hx
        have := hx ⟨none, (OTape.write wr).move? dir⟩ rfl
        simp at this
      | some q' =>
        -- Normal step case - both sides produce the lifted config
        simp only [hM, Option.map_some, liftCompCfg_left]

/-- Helper lemma: liftCompCfg_right commutes with step for the second machine -/
theorem map_liftCompCfg_right_step
    {f : List Bool → List Bool} {g : List Bool → List Bool}
    (hf : TimeComputable f) (hg : TimeComputable g)
    (x : hg.tm.Cfg) :
    Option.map (liftCompCfg_right hf hg) (hg.tm.step x) =
      (compComputer hf hg).step (liftCompCfg_right hf hg x) := by
  cases x with
  | mk state OTape =>
    cases state with
    | none =>
      simp only [step, liftCompCfg_right, Option.map_none, compComputer]
    | some q =>
      simp only [step, liftCompCfg_right, compComputer, Option.map_some]
      generalize hM : hg.tm.M q OTape.head = result
      obtain ⟨⟨wr, dir⟩, nextState⟩ := result
      cases nextState with
      | none => simp only [hM, Option.map_some, liftCompCfg_right, Option.map_none]
      | some q' => simp only [hM, Option.map_some, liftCompCfg_right]

/-- When the first machine would halt, the composed machine transitions to the second machine -/
theorem comp_transition_to_right {f : List Bool → List Bool} {g : List Bool → List Bool}
    (hf : TimeComputable f) (hg : TimeComputable g)
    (tp : OTape (Bool))
    (q : hf.tm.Λ)
    (hM : (hf.tm.M q tp.head).2 = none) :
    (compComputer hf hg).step { state := some (Sum.inl q), OTape := tp } =
      some { state := some (Sum.inr hg.tm.q₀),
             OTape := (tp.write (hf.tm.M q tp.head).1.1).move? (hf.tm.M q tp.head).1.2 } := by
  simp only [step, compComputer, hM]
  generalize hfM_eq : hf.tm.M q tp.head = result
  obtain ⟨⟨wr, dir⟩, nextState⟩ := result
  simp only [hfM_eq]

/-- Helper: lifting to Sum.inl and transitioning to Sum.inr on halt -/
def liftCompCfg_left_or_right {f : List Bool → List Bool} {g : List Bool → List Bool}
    (hf : TimeComputable f)
    (hg : TimeComputable g)
    (cfg : hf.tm.Cfg) :
    (compComputer hf hg).Cfg :=
  match cfg.state with
  | some q => { state := some (Sum.inl q), OTape := cfg.OTape }
  | none => { state := some (Sum.inr hg.tm.q₀), OTape := cfg.OTape }

/-- The lifting function commutes with step, converting halt to transition -/
theorem map_liftCompCfg_left_or_right_step
    {f : List Bool → List Bool} {g : List Bool → List Bool}
    (hf : TimeComputable f) (hg : TimeComputable g)
    (x : hf.tm.Cfg)
    (hx : x.state.isSome) :
    Option.map (liftCompCfg_left_or_right hf hg) (hf.tm.step x) =
      (compComputer hf hg).step (liftCompCfg_left_or_right hf hg x) := by
  cases x with
  | mk state OTape =>
    cases state with
    | none => simp at hx
    | some q =>
      simp only [step, liftCompCfg_left_or_right, compComputer]
      generalize hM : hf.tm.M q OTape.head = result
      obtain ⟨⟨wr, dir⟩, nextState⟩ := result
      cases nextState with
      | none => simp only [hM, Option.map_some, liftCompCfg_left_or_right]
      | some q' => simp only [hM, Option.map_some, liftCompCfg_left_or_right]

/-- General simulation: if the first machine goes from cfg to halt, the composed machine
    goes from lifted cfg to Sum.inr hg.tm.q₀ -/
theorem comp_left_simulation_general {f : List Bool → List Bool} {g : List Bool → List Bool}
    (hf : TimeComputable f) (hg : TimeComputable g)
    (cfg : hf.tm.Cfg)
    (hcfg : cfg.state.isSome)
    (haltCfg : hf.tm.Cfg)
    -- (haltCfg_state : haltCfg.state = none)
    (steps : ℕ)
    (h : EvalsToInTime hf.tm.step cfg (some haltCfg) steps) :
    EvalsToInTime (compComputer hf hg).step
      (liftCompCfg_left_or_right hf hg cfg)
      (some (liftCompCfg_left_or_right hf hg haltCfg))
      steps := by
  -- Proof by induction on steps.
  -- Key insight: liftCompCfg_left_or_right maps:
  --   { state := some q, OTape } -> { state := some (Sum.inl q), OTape }
  --   { state := none, OTape }   -> { state := some (Sum.inr hg.tm.q₀), OTape }
  -- For non-halting configs, the composed machine simulates exactly.
  -- When the first machine halts, the composed machine transitions to Sum.inr hg.tm.q₀.
  induction steps generalizing cfg haltCfg with
  | zero =>
    simp only [EvalsToInTime, Option.bind_eq_bind, step, Function.iterate_zero, id_eq,
      Option.some.injEq] at h ⊢
    rw [h]
  | succ n ih =>
    -- Use the decomposition lemma: cfg evals to some intermediate c in n steps,
    -- and then c steps to haltCfg
    -- obtain ⟨c, hc_n, hc_step⟩ := EvalsToInTime.succ_decompose hf.tm.step cfg haltCfg n h
    rw [EvalsToInTime.succ_iff] at h ⊢
    obtain ⟨c, hc_n, hc_step⟩ := h
    use liftCompCfg_left_or_right hf hg c
    constructor
    · apply ih
      · exact hcfg
      · exact hc_n
    · cases c with
      | mk state OTape =>
        cases state with
        | none =>
          simp_all
        | some q =>
          rw [← map_liftCompCfg_left_or_right_step hf hg ⟨some q, OTape⟩ (by simp)]
          simp only [hc_step, Option.map_some]


/--
Simulation for the first phase of the composed computer.
When the first machine runs from start to halt, the composed machine
runs from start (with Sum.inl state) to Sum.inr hg.tm.q₀ (the start of the second phase).
This takes the same number of steps because the halt transition becomes a transition to the
second machine.
-/
theorem comp_left_simulation {f : List Bool → List Bool} {g : List Bool → List Bool}
    (hf : TimeComputable f) (hg : TimeComputable g)
    (a : List Bool)
    (hf_outputsFun :
      EvalsToWithinTime hf.tm.step
        { state := some hf.tm.q₀, OTape := OTape.mk₁ a }
        (some { state := none, OTape := OTape.mk₁ (f a) })
        (hf.time a.length)) :
    EvalsToWithinTime (compComputer hf hg).step
      { state := some (Sum.inl hf.tm.q₀), OTape := OTape.mk₁ a }
      (some { state := some (Sum.inr hg.tm.q₀), OTape := OTape.mk₁ (f a) })
      (hf.time a.length) := by
  obtain ⟨steps, hsteps_le, hsteps_eval⟩ := hf_outputsFun
  use steps
  constructor
  · exact hsteps_le
  · have := comp_left_simulation_general hf hg
      { state := some hf.tm.q₀, OTape := OTape.mk₁ a }
      (by simp)
      { state := none, OTape := OTape.mk₁ (f a) }
      steps
      hsteps_eval
    simp only [liftCompCfg_left_or_right] at this
    exact this

/-- Simulation lemma for the second machine in the composed computer -/
theorem comp_right_simulation
    {f : List Bool → List Bool} {g : List Bool → List Bool}
    (hf : TimeComputable f) (hg : TimeComputable g)
    (x : hg.tm.Cfg) (y : Option hg.tm.Cfg) (m : ℕ)
    (h : EvalsToWithinTime hg.tm.step x y m) :
    EvalsToWithinTime (compComputer hf hg).step
      (liftCompCfg_right hf hg x)
      (Option.map (liftCompCfg_right hf hg) y)
      m := by
  exact EvalsToWithinTime.map hg.tm.step (compComputer hf hg).step
    (liftCompCfg_right hf hg) (map_liftCompCfg_right_step hf hg) x y m h




lemma output_length_le_input_length_add_time (tm : BinTM0) (l l' : List Bool) (t : ℕ)
    (h : tm.OutputsWithinTime l (some l') t) :
    l'.length ≤ max 1 l.length + t := by
  unfold OutputsWithinTime at h
  obtain ⟨steps, hsteps_le, hevals⟩ := h
  replace hevals := hevals.small_change
  specialize hevals (Cfg.space_used tm)
  simp only [Cfg.space_used_initCfg, Cfg.space_used_haltCfg] at hevals
  suffices l'.length ≤ max 1 l.length + steps
    by omega
  specialize hevals fun a b hstep ↦ Cfg.space_used_step a b (Option.mem_def.mp hstep)
  omega

/--
A composition for TimeComputable.

If f and g are computed by turing machines M₁ and M₂
then we can construct a turing machine M which computes g ∘ f by first running M₁
and then, when M₁ halts, transitioning to the start state of M₂ and running M₂.

This results in time bounded by the amount of time taken by M₁ plus the maximum time taken by M₂ on
inputs of length of the maximum output length of M₁ for that input size (which is itself bounded by
the time taken by M₁).

Note that we require the time function of the second machine to be monotone;
this is to ensure that if the first machine returns an output
which is shorter than the maximum possible length of output for that input size,
then the time bound for the second machine still holds for that shorter input to the second machine.

TODO refactor out the definition of the composed TM.
Prove separately that it
evals to the intermediate state from the start state and
then from the intermediate state to the final state.
-/
def TimeComputable.comp
    {f : List Bool → List Bool} {g : List Bool → List Bool}
    (hf : TimeComputable f)
    (hg : TimeComputable g)
    (h_mono : Monotone hg.time) :
    (TimeComputable (g ∘ f)) where
  tm := compComputer hf hg
  time l := (hf.time l) + hg.time (max 1 l + hf.time l)
  outputsFun a := by
    have hf_outputsFun := hf.outputsFun a
    have hg_outputsFun := hg.outputsFun (f a)
    simp only [OutputsWithinTime, initCfg, compComputer_q₀_eq, Function.comp_apply,
      Option.map_some, haltCfg] at hg_outputsFun hf_outputsFun ⊢
    -- The computer evals a to f a in time hf.time a
    have h_a_evalsTo_f_a :
        EvalsToWithinTime (compComputer hf hg).step
          { state := some (Sum.inl hf.tm.q₀), OTape := OTape.mk₁ a }
          (some { state := some (Sum.inr hg.tm.q₀), OTape := OTape.mk₁ (f a) })
          (hf.time a.length) :=
      comp_left_simulation hf hg a hf_outputsFun
    have h_f_a_evalsTo_g_f_a :
        EvalsToWithinTime (compComputer hf hg).step
          { state := some (Sum.inr hg.tm.q₀), OTape := OTape.mk₁ (f a) }
          (some { state := none, OTape := OTape.mk₁ (g (f a)) })
          (hg.time (f a).length) := by
      -- Use the simulation lemma for the second machine
      have := comp_right_simulation hf hg
        { state := some hg.tm.q₀, OTape := OTape.mk₁ (f a) }
        (some { state := none, OTape := OTape.mk₁ (g (f a)) })
        (hg.time (f a).length)
        hg_outputsFun
      simp only [liftCompCfg_right, Option.map_some] at this
      exact this
    have h_a_evalsTo_g_f_a :=
      EvalsToWithinTime.trans
        (compComputer hf hg).step _ _ _ _ _ h_a_evalsTo_f_a h_f_a_evalsTo_g_f_a
    apply EvalsToWithinTime.mono_time _ _ _ h_a_evalsTo_g_f_a
    nth_rw 1 [← add_comm]
    apply add_le_add
    · omega
    · apply h_mono
      -- Use the lemma about output length being bounded by input length + time
      exact output_length_le_input_length_add_time hf.tm _ _ _ (hf.outputsFun a)

end

/-!
## Polynomial Time Computability

This section defines polynomial time computable functions on Turing machines.
-/

section PolyTime

/-- A Turing machine + a polynomial time function +
a proof it outputsInTime `f` in at most `time(input.length)` steps. -/
structure PolyTimeComputable (f : List Bool → List Bool) extends TimeComputable f where
  /-- a polynomial time bound -/
  poly : Polynomial ℕ
  /-- proof that this machine outputsInTime `f` in at most `time(input.length)` steps -/
  bounds : ∀ n, time n ≤ poly.eval n

/-- A proof that the identity map on α is computable in polytime. -/
noncomputable def PolyTimeComputable.id : @PolyTimeComputable id where
  toTimeComputable := TimeComputable.id
  poly := 1
  bounds n := by simp only [TimeComputable.id, Polynomial.eval_one, le_refl]

/--
A proof that the composition of two polytime computable functions is polytime computable.
-/
noncomputable def PolyTimeComputable.comp
    {f : List Bool → List Bool} {g : List Bool → List Bool}
    (hf : PolyTimeComputable f)
    (hg : PolyTimeComputable g)
    -- all Nat polynomials are monotone, but the tighter internal bound maybe is not
    (h_mono : Monotone hg.time) :
    PolyTimeComputable (g ∘ f) where
  toTimeComputable := TimeComputable.comp hf.toTimeComputable hg.toTimeComputable h_mono

  poly := hf.poly + hg.poly.comp (1 + Polynomial.X + hf.poly)
  bounds n := by
    simp only [TimeComputable.comp, Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_X,
      Polynomial.eval_one]
    apply add_le_add
    · exact hf.bounds n
    · have : hg.time (max 1 n + hf.time n) ≤ hg.time (1 + n + hf.poly.eval n) := by
        apply h_mono
        apply add_le_add
        · omega
        · exact hf.bounds n
      apply le_trans this _
      exact hg.bounds (1 + n + hf.poly.eval n)

end PolyTime

end BinTM0

end Turing
