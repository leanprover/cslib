/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Pim Spelier, Daan van Gent
-/

module

public import Cslib.Foundations.Data.BiTape
public import Cslib.Foundations.Data.RelatesInSteps
public import Mathlib.Algebra.Polynomial.Eval.Defs

@[expose] public section

/-!
# Single-Tape Turing Machines

Defines a single-tape Turing machine for computing functions on `List α` for finite alphabet `α`.
These machines have access to a single bidirectionally-infinite tape (`BiTape`)
which uses symbols from `Option α`.

## TODOs

- encoding?
- refactor polynomial time to another file?

-/

open Cslib Relation

namespace Turing

variable {α : Type}

namespace SingleTapeTM

-- TODO make into a structure?
/--
A Turing machine "statement" is just a `Option`al command to move left or right,
and write a symbol on the `BiTape`.
-/
def Stmt (α : Type) := Option α × Option Dir
deriving Inhabited

def Stmt.symbol : Stmt α → Option α
  | (symbol, _) => symbol

def Stmt.movement : Stmt α → Option Dir
  | (_, movement) => movement

end SingleTapeTM

/-- A SingleTapeTM over the alphabet of Option α (none is blank BiTape symbol). -/
structure SingleTapeTM α where
  /-- Inhabited instance for the alphabet -/
  [Inhabitedα : Inhabited α]
  /-- Finiteness of the alphabet -/
  [Fintypeα : Fintype α]
  /-- type of state labels -/
  (Λ : Type)
  /-- finiteness of the state type -/
  [FintypeΛ : Fintype Λ]
  /-- Initial state -/
  (q₀ : Λ)
  /-- Transition function, mapping a state and a head symbol
  to a Stmt to invoke, and optionally a new state (none for halt) -/
  (M : Λ → (Option α) → (Turing.SingleTapeTM.Stmt α × Option Λ))

namespace SingleTapeTM

section Cfg

/-!
## Configurations of a Turing Machine

This section defines the configurations of a Turing machine,
the step function that lets the machine transition from one configuration to the next,
and the intended initial and final configurations.
-/

variable (tm : SingleTapeTM α)

instance : Inhabited tm.Λ :=
  ⟨tm.q₀⟩

instance : Fintype tm.Λ :=
  tm.FintypeΛ

instance inhabitedStmt : Inhabited (Stmt α) := inferInstance

/--
The configurations of a Turing machine consist of an `Option`al state
(or none for the halting state)
and an BiTape representing the tape contents.
-/
structure Cfg : Type where
  /-- the state of the TM (or none for the halting state) -/
  state : Option tm.Λ
  /-- the BiTape contents -/
  BiTape : BiTape α
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
            -- And BiTape updated according to the Stmt
            (t.write wr).optionMove dir⟩

/-- The initial configuration corresponding to a list in the input alphabet. -/
def initCfg (tm : SingleTapeTM α) (s : List α) : tm.Cfg := ⟨some tm.q₀, BiTape.mk₁ s⟩

/-- The final configuration corresponding to a list in the output alphabet.
(We demand that the head halts at the leftmost position of the output.)
-/
def haltCfg (tm : SingleTapeTM α) (s : List α) : tm.Cfg := ⟨none, BiTape.mk₁ s⟩

def Cfg.space_used (tm : SingleTapeTM α) (cfg : tm.Cfg) : ℕ :=
  cfg.BiTape.space_used

lemma Cfg.space_used_initCfg (tm : SingleTapeTM α) (s : List α) :
    (tm.initCfg s).space_used = max 1 s.length := by
  simp only [space_used, initCfg, BiTape.space_used_mk₁]

lemma Cfg.space_used_haltCfg (tm : SingleTapeTM α) (s : List α) :
    (tm.haltCfg s).space_used = max 1 s.length := by
  simp [haltCfg, Cfg.space_used, BiTape.space_used_mk₁]

lemma Cfg.space_used_step {tm : SingleTapeTM α} (cfg cfg' : tm.Cfg)
    (hstep : tm.step cfg = some cfg') : cfg'.space_used ≤ cfg.space_used + 1 := by
  obtain ⟨_ | q, tape⟩ := cfg
  · simp [step] at hstep
  · simp only [step] at hstep
    generalize hM : tm.M q tape.head = result at hstep
    obtain ⟨⟨wr, dir⟩, q''⟩ := result
    cases hstep; cases dir with
    | none => simp [Cfg.space_used, BiTape.optionMove, BiTape.space_used_write]
    | some d =>
      have := BiTape.space_used_move (tape.write wr) d
      simp only [Cfg.space_used, BiTape.optionMove, BiTape.space_used_write] at this ⊢; exact this

end Cfg

/--
The `TerminalReductionSystem` corresponding to a `SingleTapeTM α`
is defined by the `step` function,
which maps a configuration to its next configuration if it exists.
-/
def TransitionRelation (tm : SingleTapeTM α) (c₁ c₂ : tm.Cfg) : Prop :=
  tm.step c₁ = some c₂


/-- A proof of tm outputting l' when given l. -/
def Outputs (tm : SingleTapeTM α) (l : List α) (l' : List α) : Prop :=
  ReflTransGen tm.TransitionRelation (initCfg tm l) (haltCfg tm l')

/-- A proof of tm outputting l' when given l in at most m steps. -/
def OutputsWithinTime (tm : SingleTapeTM α) (l : List α) (l' : List α)
    (m : ℕ) :=
  RelatesWithinSteps tm.TransitionRelation (initCfg tm l) (haltCfg tm l') m

/--
This lemma bounds the size blow-up of the output of a Turing machine.
It states that the increase in length of the output over the input is bounded by the runtime.
This is important for guaranteeing that composition of polynomial time Turing machines
remains polynomial time, as the input to the second machine
is bounded by the output length of the first machine.
-/
lemma output_length_le_input_length_add_time (tm : SingleTapeTM α) (l l' : List α) (t : ℕ)
    (h : tm.OutputsWithinTime l l' t) :
    l'.length ≤ max 1 l.length + t := by
  simp only [OutputsWithinTime] at h
  obtain ⟨steps, hsteps_le, hevals⟩ := h
  replace hevals := hevals.apply_le_apply_add
  specialize hevals (Cfg.space_used tm)
  simp only [Cfg.space_used_initCfg, Cfg.space_used_haltCfg] at hevals
  suffices l'.length ≤ max 1 l.length + steps
    by omega
  specialize hevals fun a b hstep ↦ Cfg.space_used_step a b (Option.mem_def.mp hstep)
  omega

/-- A Turing machine + a proof it outputsInTime `f`. -/
structure Computable (f : List α → List α) where
  /-- the underlying bundled SingleTapeTM -/
  tm : SingleTapeTM α
  /-- a proof this machine outputsInTime `f` -/
  outputsFun : ∀ a, tm.Outputs a (f a)

/-- A Turing machine + a time function +
a proof it outputsInTime `f` in at most `time(input.length)` steps. -/
structure TimeComputable (f : List α → List α) where
  /-- the underlying bundled SingleTapeTM -/
  tm : SingleTapeTM α
  /-- a time function -/
  time : ℕ → ℕ
  /-- proof this machine outputsInTime `f` in at most `time(input.length)` steps -/
  outputsFun : ∀ a, tm.OutputsWithinTime a (f a) (time a.length)

section

variable [Inhabited α] [Fintype α]

/-- A Turing machine computing the identity. -/
def idComputer : SingleTapeTM α where
  Λ := PUnit
  q₀ := PUnit.unit
  M := fun _ b => ⟨(b, none), none⟩

-- TODO switch to where syntax
/-- A proof that the identity map on α is computable in time. -/
def TimeComputable.id : TimeComputable (α := α) id :=
  ⟨idComputer, fun _ => 1, fun x => by
    refine ⟨1, le_refl 1, ?_⟩
    -- Need to show reducesToInSteps for 1 step
    refine RelatesInSteps.head _ _ _ 0 ?_
      (RelatesInSteps.refl _)
    -- Show the single step reduction: step (init x) = some (halt x)
    simp only [TransitionRelation, initCfg, haltCfg, idComputer, step, BiTape.optionMove]
    congr 1⟩

def compComputer {f : List α → List α} {g : List α → List α}
    (hf : TimeComputable f)
    (hg : TimeComputable g) :
    SingleTapeTM α :=
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

lemma compComputer_q₀_eq (f : List α → List α) (g : List α → List α)
  (hf : TimeComputable f) (hg : TimeComputable g) :
    (compComputer hf hg).q₀ = Sum.inl hf.tm.q₀ :=
  rfl

/-- Lift a config over a tm to a config over the comp -/
def liftCompCfg_left {f : List α → List α} {g : List α → List α}
    (hf : TimeComputable f) (hg : TimeComputable g)
    (cfg : hf.tm.Cfg) :
    (compComputer hf hg).Cfg :=
  {
    state := Option.map Sum.inl cfg.state
    BiTape := cfg.BiTape
  }

def liftCompCfg_right {f : List α → List α} {g : List α → List α}
    (hf : TimeComputable f) (hg : TimeComputable g)
    (cfg : hg.tm.Cfg) :
    (compComputer hf hg).Cfg :=
  {
    state := Option.map Sum.inr cfg.state
    BiTape := cfg.BiTape
  }

theorem map_liftCompCfg_left_step
    {f : List α → List α} {g : List α → List α}
    (hf : TimeComputable f) (hg : TimeComputable g)
    (x : hf.tm.Cfg) (hx : ∀ cfg, hf.tm.step x = some cfg → cfg.state.isSome) :
    Option.map (liftCompCfg_left hf hg) (hf.tm.step x) =
      (compComputer hf hg).step (liftCompCfg_left hf hg x) := by
  cases x with
  | mk state BiTape =>
    cases state with
    | none =>
      -- x is already in halting state, step returns none on both sides
      simp only [step, liftCompCfg_left, Option.map_none, compComputer]
    | some q =>
      simp only [step, liftCompCfg_left, compComputer, Option.map_some]
      -- Get the transition result
      generalize hM : hf.tm.M q BiTape.head = result
      obtain ⟨⟨wr, dir⟩, nextState⟩ := result
      simp only
      -- Case on whether the next state is none (halting) or some
      cases nextState with
      | none =>
        -- The first machine halts, but hx says the result has state.isSome
        simp only [step, hM] at hx
        have := hx ⟨none, (BiTape.write wr).optionMove dir⟩ rfl
        simp at this
      | some q' =>
        -- Normal step case - both sides produce the lifted config
        simp only [hM, Option.map_some, liftCompCfg_left]

/-- Helper lemma: liftCompCfg_right commutes with step for the second machine -/
theorem map_liftCompCfg_right_step
    {f : List α → List α} {g : List α → List α}
    (hf : TimeComputable f) (hg : TimeComputable g)
    (x : hg.tm.Cfg) :
    Option.map (liftCompCfg_right hf hg) (hg.tm.step x) =
      (compComputer hf hg).step (liftCompCfg_right hf hg x) := by
  cases x with
  | mk state BiTape =>
    cases state with
    | none =>
      simp only [step, liftCompCfg_right, Option.map_none, compComputer]
    | some q =>
      simp only [step, liftCompCfg_right, compComputer, Option.map_some]
      generalize hM : hg.tm.M q BiTape.head = result
      obtain ⟨⟨wr, dir⟩, nextState⟩ := result
      cases nextState with
      | none => simp only [hM, Option.map_some, liftCompCfg_right, Option.map_none]
      | some q' => simp only [hM, Option.map_some, liftCompCfg_right]

theorem comp_transition_to_right {f : List α → List α} {g : List α → List α}
    (hf : TimeComputable f) (hg : TimeComputable g)
    (tp : BiTape α)
    (q : hf.tm.Λ)
    (hM : (hf.tm.M q tp.head).2 = none) :
    (compComputer hf hg).step { state := some (Sum.inl q), BiTape := tp } =
      some { state := some (Sum.inr hg.tm.q₀),
             BiTape := (tp.write (hf.tm.M q tp.head).1.symbol).optionMove
                        (hf.tm.M q tp.head).1.movement } := by
  simp only [step, compComputer, hM, Stmt.symbol, Stmt.movement]
  generalize hfM_eq : hf.tm.M q tp.head = result
  obtain ⟨⟨wr, dir⟩, nextState⟩ := result
  simp only [hfM_eq]

/-- Helper: lifting to Sum.inl and transitioning to Sum.inr on halt -/
def liftCompCfg_left_or_right {f : List α → List α} {g : List α → List α}
    (hf : TimeComputable f) (hg : TimeComputable g)
    (cfg : hf.tm.Cfg) :
    (compComputer hf hg).Cfg :=
  match cfg.state with
  | some q => { state := some (Sum.inl q), BiTape := cfg.BiTape }
  | none => { state := some (Sum.inr hg.tm.q₀), BiTape := cfg.BiTape }

/-- The lifting function commutes with step, converting halt to transition -/
theorem map_liftCompCfg_left_or_right_step
    {f : List α → List α} {g : List α → List α}
    (hf : TimeComputable f) (hg : TimeComputable g)
    (x : hf.tm.Cfg)
    (hx : x.state.isSome) :
    Option.map (liftCompCfg_left_or_right hf hg) (hf.tm.step x) =
      (compComputer hf hg).step (liftCompCfg_left_or_right hf hg x) := by
  cases x with
  | mk state BiTape =>
    cases state with
    | none => simp at hx
    | some q =>
      simp only [step, liftCompCfg_left_or_right, compComputer]
      generalize hM : hf.tm.M q BiTape.head = result
      obtain ⟨⟨wr, dir⟩, nextState⟩ := result
      cases nextState with
      | none => simp only [hM, Option.map_some, liftCompCfg_left_or_right]
      | some q' => simp only [hM, Option.map_some, liftCompCfg_left_or_right]

/-- General simulation: if the first machine goes from cfg to halt, the composed machine
    goes from lifted cfg to Sum.inr hg.tm.q₀ -/
theorem comp_left_simulation_general {f : List α → List α} {g : List α → List α}
    (hf : TimeComputable f) (hg : TimeComputable g)
    (cfg : hf.tm.Cfg)
    (hcfg : cfg.state.isSome)
    (haltCfg : hf.tm.Cfg)
    (steps : ℕ)
    (h : RelatesInSteps hf.tm.TransitionRelation cfg haltCfg steps) :
    RelatesInSteps (compComputer hf hg).TransitionRelation
      (liftCompCfg_left_or_right hf hg cfg)
      (liftCompCfg_left_or_right hf hg haltCfg)
      steps := by
  -- Proof by induction on steps.
  -- Key insight: liftCompCfg_left_or_right maps:
  --   { state := some q, BiTape } -> { state := some (Sum.inl q), BiTape }
  --   { state := none, BiTape }   -> { state := some (Sum.inr hg.tm.q₀), BiTape }
  -- For non-halting configs, the composed machine simulates exactly.
  -- When the first machine halts, the composed machine transitions to Sum.inr hg.tm.q₀.
  induction steps generalizing cfg haltCfg with
  | zero =>
    simp only [RelatesInSteps.zero_iff] at h ⊢
    rw [h]
  | succ n ih =>
    -- Use the decomposition lemma: cfg evals to some intermediate c in n steps,
    -- and then c steps to haltCfg
    -- obtain ⟨c, hc_n, hc_step⟩ := EvalsToInTime.succ_decompose hf.tm.step cfg haltCfg n h
    rw [RelatesInSteps.succ_iff] at h ⊢
    obtain ⟨c, hc_n, hc_step⟩ := h
    use liftCompCfg_left_or_right hf hg c
    constructor
    · apply ih
      · exact hcfg
      · exact hc_n
    · cases c with
      | mk state BiTape =>
        cases state with
        | none =>
          -- c is in halting state, but step of halting state is none, contradiction
          simp only [TransitionRelation, step] at hc_step
          cases hc_step
        | some q =>
          -- Use the lifting lemma
          have h1 := map_liftCompCfg_left_or_right_step hf hg ⟨some q, BiTape⟩ (by simp)
          simp only [TransitionRelation] at hc_step ⊢
          rw [hc_step, Option.map_some] at h1
          exact h1.symm


/--
Simulation for the first phase of the composed computer.
When the first machine runs from start to halt, the composed machine
runs from start (with Sum.inl state) to Sum.inr hg.tm.q₀ (the start of the second phase).
This takes the same number of steps because the halt transition becomes a transition to the
second machine.
-/
theorem comp_left_simulation {f : List α → List α} {g : List α → List α}
    (hf : TimeComputable f) (hg : TimeComputable g)
    (a : List α)
    (hf_outputsFun :
      RelatesWithinSteps hf.tm.TransitionRelation
        { state := some hf.tm.q₀, BiTape := BiTape.mk₁ a }
        ({ state := none, BiTape := BiTape.mk₁ (f a) })
        (hf.time a.length)) :
    RelatesWithinSteps (compComputer hf hg).TransitionRelation
      { state := some (Sum.inl hf.tm.q₀), BiTape := BiTape.mk₁ a }
      ({ state := some (Sum.inr hg.tm.q₀), BiTape := BiTape.mk₁ (f a) })
      (hf.time a.length) := by
  obtain ⟨steps, hsteps_le, hsteps_eval⟩ := hf_outputsFun
  use steps
  constructor
  · exact hsteps_le
  · have := comp_left_simulation_general hf hg
      { state := some hf.tm.q₀, BiTape := BiTape.mk₁ a }
      (by simp)
      { state := none, BiTape := BiTape.mk₁ (f a) }
      steps
      hsteps_eval
    simp only [liftCompCfg_left_or_right] at this
    exact this

/-- Simulation lemma for the second machine in the composed computer -/
theorem comp_right_simulation
    {f : List α → List α} {g : List α → List α}
    (hf : TimeComputable f) (hg : TimeComputable g)
    (x : hg.tm.Cfg) (y : hg.tm.Cfg) (m : ℕ)
    (h : RelatesWithinSteps hg.tm.TransitionRelation x y m) :
    RelatesWithinSteps (compComputer hf hg).TransitionRelation
      (liftCompCfg_right hf hg x)
      ((liftCompCfg_right hf hg) y)
      m := by
  refine RelatesWithinSteps.map (liftCompCfg_right hf hg) ?_ h
  intro a b hab
  have h1 := map_liftCompCfg_right_step hf hg a
  rw [hab, Option.map_some] at h1
  exact h1.symm

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
    {f : List α → List α} {g : List α → List α}
    (hf : TimeComputable f) (hg : TimeComputable g)
    (h_mono : Monotone hg.time) :
    (TimeComputable (g ∘ f)) where
  tm := compComputer hf hg
  -- perhaps it would be good to track the blow up separately?
  time l := (hf.time l) + hg.time (max 1 l + hf.time l)
  outputsFun a := by
    have hf_outputsFun := hf.outputsFun a
    have hg_outputsFun := hg.outputsFun (f a)
    simp only [OutputsWithinTime, initCfg, compComputer_q₀_eq, Function.comp_apply,
      haltCfg] at hg_outputsFun hf_outputsFun ⊢
    -- The computer reduces a to f a in time hf.time a
    have h_a_reducesTo_f_a :
        RelatesWithinSteps (compComputer hf hg).TransitionRelation
          { state := some (Sum.inl hf.tm.q₀), BiTape := BiTape.mk₁ a }
          { state := some (Sum.inr hg.tm.q₀), BiTape := BiTape.mk₁ (f a) }
          (hf.time a.length) :=
      comp_left_simulation hf hg a hf_outputsFun
    have h_f_a_reducesTo_g_f_a :
        RelatesWithinSteps (compComputer hf hg).TransitionRelation
          { state := some (Sum.inr hg.tm.q₀), BiTape := BiTape.mk₁ (f a) }
          { state := none, BiTape := BiTape.mk₁ (g (f a)) }
          (hg.time (f a).length) := by
      -- Use the simulation lemma for the second machine
      have := comp_right_simulation hf hg
        { state := some hg.tm.q₀, BiTape := BiTape.mk₁ (f a) }
        { state := none, BiTape := BiTape.mk₁ (g (f a)) }
        (hg.time (f a).length)
        hg_outputsFun
      simp only [liftCompCfg_right] at this
      exact this
    have h_a_reducesTo_g_f_a :=
      RelatesWithinSteps.trans
        h_a_reducesTo_f_a h_f_a_reducesTo_g_f_a
    apply RelatesWithinSteps.of_le h_a_reducesTo_g_f_a
    apply add_le_add
    · omega
    · apply h_mono
      -- Use the lemma about output length being bounded by input length + time
      exact output_length_le_input_length_add_time hf.tm _ _ _ (hf.outputsFun a)

end

/-!
## Polynomial Time Computability

This section defines polynomial time computable functions on Turing machines,
and proves that
* The identity function is polynomial time computable
* The composition of two polynomial time computable functions is polynomial time computable

### TODO

- Use of mathlib's `Polynomial` type leads to noncomputable definitions here.
Perhaps we could switch to a computable polynomial representation?
- Move to dedicated file?

-/

section PolyTime

variable [Inhabited α] [Fintype α]


/-- A Turing machine + a polynomial time function +
a proof it outputsInTime `f` in at most `time(input.length)` steps. -/
structure PolyTimeComputable (f : List α → List α) extends TimeComputable f where
  /-- a polynomial time bound -/
  poly : Polynomial ℕ
  /-- proof that this machine outputsInTime `f` in at most `time(input.length)` steps -/
  bounds : ∀ n, time n ≤ poly.eval n

/-- A proof that the identity map on α is computable in polytime. -/
noncomputable def PolyTimeComputable.id : @PolyTimeComputable (α := α) id where
  toTimeComputable := TimeComputable.id
  poly := 1
  bounds n := by simp only [TimeComputable.id, Polynomial.eval_one, le_refl]

/--
A proof that the composition of two polytime computable functions is polytime computable.
-/
noncomputable def PolyTimeComputable.comp
    {f : List α → List α} {g : List α → List α}
    (hf : PolyTimeComputable f)
    (hg : PolyTimeComputable g)
    -- all Nat polynomials are monotone, but the tighter internal bound maybe is not, awkwardly
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
        · omega -- lia fails
        · exact hf.bounds n
      apply le_trans this _
      exact hg.bounds (1 + n + hf.poly.eval n)

end PolyTime

end SingleTapeTM

end Turing
