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

## Important Declarations

We define a number of structures related to Turing machine computation:

* `Stmt`: the write and movement operations a TM can do in a single step.
* `SingleTapeTM`: the TM itself.
* `Cfg`: the configuration of a TM, including internal and tape state.
* `Computable f`: a TM for computing function `f`, packaged with a proof of correctness.
* `TimeComputable f`: `Computable f` additionally packaged with a bound on runtime.
* `PolyTimeComputable f`: `TimeComputable f` packaged with a polynomial bound on runtime.

We also provide ways of constructing polynomial-runtime TMs

* `PolyTimeComputable.id`: computes the identity function
* `PolyTimeComputable.comp`: computes the composition of polynomial time machines

## TODOs

- Encoding of types in lists to represent computations on arbitrary types.
- Composition notation
- Check I can't put more args on the same line

-/

open Cslib Relation

namespace Turing

variable {α : Type}

namespace SingleTapeTM

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

/--
The space used by a configuration is the space used by its tape.
-/
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
The `TransitionRelation` corresponding to a `SingleTapeTM α`
is defined by the `step` function,
which maps a configuration to its next configuration, if it exists.
-/
def TransitionRelation (tm : SingleTapeTM α) (c₁ c₂ : tm.Cfg) : Prop :=
  tm.step c₁ = some c₂

/-- A proof of `tm` outputting `l'` on input `l`. -/
def Outputs (tm : SingleTapeTM α) (l l' : List α) : Prop :=
  ReflTransGen tm.TransitionRelation (initCfg tm l) (haltCfg tm l')

/-- A proof of `tm` outputting `l'` on input `l` in at most `m` steps. -/
def OutputsWithinTime (tm : SingleTapeTM α) (l l' : List α)
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

section

variable [Inhabited α] [Fintype α]

/-- A Turing machine computing the identity. -/
def idComputer : SingleTapeTM α where
  Λ := PUnit
  q₀ := PUnit.unit
  M := fun _ b => ⟨(b, none), none⟩

/-- A Turing machine computing the composition of two other Turing machines. -/
def compComputer (tm1 tm2 : SingleTapeTM α) : SingleTapeTM α where
  -- The states of the composed machine are the disjoint union of the states of the input machines.
  Λ := tm1.Λ ⊕ tm2.Λ
  -- The start state is the start state of the first input machine.
  q₀ := .inl tm1.q₀
  M q h :=
    match q with
    -- If we are in the first input machine's states, run that machine ...
    | .inl ql => match tm1.M ql h with
      | (stmt, state) =>
        -- ... taking the same tape action as the first input machine would.
        (stmt,
          match state with
          -- If it halts, transition to the start state of the second input machine
          | none => some (.inr tm2.q₀)
          -- Otherwise continue as normal
          | _ => Option.map .inl state)
    -- If we are in the second input machine's states, run that machine ...
    | .inr qr =>
      match tm2.M qr h with
      | (stmt, state) =>
        -- ... taking the same tape action as the second input machine would.
        (stmt,
          match state with
          -- If it halts, transition to the halting state
          | none => none
          -- Otherwise continue as normal
          | _ => Option.map .inr state)

section compComputerLemmas

/-! ### Composition Computer Lemmas -/

lemma compComputer_q₀_eq (tm1 tm2 : SingleTapeTM α) :
    (compComputer tm1 tm2).q₀ = Sum.inl tm1.q₀ :=
  rfl

/-- Convert a `Cfg` over the first input machine to a config over the composed machine -/
private def toCompCfg_left (tm1 tm2 : SingleTapeTM α)
    (cfg : tm1.Cfg) :
    (compComputer tm1 tm2).Cfg :=
  {
    state := Option.map Sum.inl cfg.state
    BiTape := cfg.BiTape
  }

/-- Convert a `Cfg` over the second input machine to a config over the composed machine -/
private def toCompCfg_right (tm1 tm2 : SingleTapeTM α)
    (cfg : tm2.Cfg) :
    (compComputer tm1 tm2).Cfg :=
  {
    state := Option.map Sum.inr cfg.state
    BiTape := cfg.BiTape
  }

private theorem map_toCompCfg_left_step
    (tm1 tm2 : SingleTapeTM α)
    (x : tm1.Cfg) (hx : ∀ cfg, tm1.step x = some cfg → cfg.state.isSome) :
    Option.map (toCompCfg_left tm1 tm2) (tm1.step x) =
      (compComputer tm1 tm2).step (toCompCfg_left tm1 tm2 x) := by
  cases x with
  | mk state BiTape =>
    cases state with
    | none =>
      -- x is already in halting state, step returns none on both sides
      simp only [step, toCompCfg_left, Option.map_none, compComputer]
    | some q =>
      simp only [step, toCompCfg_left, compComputer, Option.map_some]
      -- Get the transition result
      generalize hM : tm1.M q BiTape.head = result
      obtain ⟨⟨wr, dir⟩, nextState⟩ := result
      simp only
      -- Case on whether the next state is none (halting) or some
      cases nextState with
      | none =>
        -- The first machine halts, but hx says the result has state.isSome
        simp only [step, hM] at hx
        grind [hx ⟨none, (BiTape.write wr).optionMove dir⟩ rfl]
      | some q' =>
        -- Normal step case - both sides produce the toed config
        simp only [hM, Option.map_some, toCompCfg_left]

/-- Helper lemma: toCompCfg_right commutes with step for the second machine -/
private theorem map_toCompCfg_right_step
    (tm1 tm2 : SingleTapeTM α)
    (x : tm2.Cfg) :
    Option.map (toCompCfg_right tm1 tm2) (tm2.step x) =
      (compComputer tm1 tm2).step (toCompCfg_right tm1 tm2 x) := by
  cases x with
  | mk state BiTape =>
    cases state with
    | none =>
      simp only [step, toCompCfg_right, Option.map_none, compComputer]
    | some q =>
      simp only [step, toCompCfg_right, compComputer, Option.map_some]
      generalize hM : tm2.M q BiTape.head = result
      obtain ⟨⟨wr, dir⟩, nextState⟩ := result
      cases nextState with
      | none => simp only [hM, Option.map_some, toCompCfg_right, Option.map_none]
      | some q' => simp only [hM, Option.map_some, toCompCfg_right]

private theorem comp_transition_to_right (tm1 tm2 : SingleTapeTM α)
    (tp : BiTape α)
    (q : tm1.Λ)
    (hM : (tm1.M q tp.head).2 = none) :
    (compComputer tm1 tm2).step { state := some (Sum.inl q), BiTape := tp } =
      some { state := some (Sum.inr tm2.q₀),
             BiTape := (tp.write (tm1.M q tp.head).1.symbol).optionMove
                        (tm1.M q tp.head).1.movement } := by
  simp only [step, compComputer, hM, Stmt.symbol, Stmt.movement]
  generalize M_eq : tm1.M q tp.head = result
  obtain ⟨⟨wr, dir⟩, nextState⟩ := result
  simp only [M_eq]

/-- Helper: converting to Sum.inl and transitioning to Sum.inr on halt -/
private def toCompCfg_left_or_right (tm1 tm2 : SingleTapeTM α)
    (cfg : tm1.Cfg) :
    (compComputer tm1 tm2).Cfg :=
  match cfg.state with
  | some q => { state := some (Sum.inl q), BiTape := cfg.BiTape }
  | none => { state := some (Sum.inr tm2.q₀), BiTape := cfg.BiTape }

/-- The converting function commutes with step, converting halt to transition -/
private theorem map_toCompCfg_left_or_right_step
    (tm1 tm2 : SingleTapeTM α)
    (x : tm1.Cfg)
    (hx : x.state.isSome) :
    Option.map (toCompCfg_left_or_right tm1 tm2) (tm1.step x) =
      (compComputer tm1 tm2).step (toCompCfg_left_or_right tm1 tm2 x) := by
  cases x with
  | mk state BiTape =>
    cases state with
    | none => simp at hx
    | some q =>
      simp only [step, toCompCfg_left_or_right, compComputer]
      generalize hM : tm1.M q BiTape.head = result
      obtain ⟨⟨wr, dir⟩, nextState⟩ := result
      cases nextState with
      | none => simp only [hM, Option.map_some, toCompCfg_left_or_right]
      | some q' => simp only [hM, Option.map_some, toCompCfg_left_or_right]

/-- General simulation: if the first machine goes from cfg to halt, the composed machine
    goes from cfg to Sum.inr tm2.q₀ -/
private theorem comp_left_simulation_general (tm1 tm2 : SingleTapeTM α)
    (cfg : tm1.Cfg)
    (hcfg : cfg.state.isSome)
    (haltCfg : tm1.Cfg)
    (steps : ℕ)
    (h : RelatesInSteps tm1.TransitionRelation cfg haltCfg steps) :
    RelatesInSteps (compComputer tm1 tm2).TransitionRelation
      (toCompCfg_left_or_right tm1 tm2 cfg)
      (toCompCfg_left_or_right tm1 tm2 haltCfg)
      steps := by
  induction steps generalizing cfg haltCfg with
  | zero =>
    simp only [RelatesInSteps.zero_iff] at h ⊢
    rw [h]
  | succ n ih =>
    rw [RelatesInSteps.succ_iff] at h ⊢
    obtain ⟨c, hc_n, hc_step⟩ := h
    use toCompCfg_left_or_right tm1 tm2 c
    constructor
    · apply ih
      · exact hcfg
      · exact hc_n
    · cases c with
      | mk state BiTape =>
        cases state with
        | none =>
          simp only [TransitionRelation, step] at hc_step
          cases hc_step
        | some q =>
          have h1 := map_toCompCfg_left_or_right_step tm1 tm2 ⟨some q, BiTape⟩ (by simp)
          simp only [TransitionRelation] at hc_step ⊢
          rw [hc_step, Option.map_some] at h1
          exact h1.symm


/--
Simulation for the first phase of the composed computer.
When the first machine runs from start to halt, the composed machine
runs from start (with Sum.inl state) to Sum.inr tm2.q₀ (the start of the second phase).
This takes the same number of steps because the halt transition becomes a transition to the
second machine.
-/
private theorem comp_left_simulation (tm1 tm2 : SingleTapeTM α)
    (input_tape intermediate_tape : List α)
    (t : ℕ)
    (htm1 :
      RelatesWithinSteps tm1.TransitionRelation
        { state := some tm1.q₀, BiTape := BiTape.mk₁ input_tape }
        ({ state := none, BiTape := BiTape.mk₁ intermediate_tape })
        t) :
    RelatesWithinSteps (compComputer tm1 tm2).TransitionRelation
      { state := some (Sum.inl tm1.q₀), BiTape := BiTape.mk₁ input_tape }
      ({ state := some (Sum.inr tm2.q₀), BiTape := BiTape.mk₁ intermediate_tape })
      t := by
  obtain ⟨steps, hsteps_le, hsteps_eval⟩ := htm1
  use steps
  constructor
  · exact hsteps_le
  · have := comp_left_simulation_general tm1 tm2
      { state := some tm1.q₀, BiTape := BiTape.mk₁ input_tape }
      (by simp)
      { state := none, BiTape := BiTape.mk₁ intermediate_tape }
      steps
      hsteps_eval
    simp only [toCompCfg_left_or_right] at this
    exact this

/-- Simulation lemma for the second machine in the composed computer -/
private theorem comp_right_simulation
    (tm1 tm2 : SingleTapeTM α)
    (x : tm2.Cfg) (y : tm2.Cfg) (m : ℕ)
    (h : RelatesWithinSteps tm2.TransitionRelation x y m) :
    RelatesWithinSteps (compComputer tm1 tm2).TransitionRelation
      (toCompCfg_right tm1 tm2 x)
      ((toCompCfg_right tm1 tm2) y)
      m := by
  refine RelatesWithinSteps.map (toCompCfg_right tm1 tm2) ?_ h
  intro a b hab
  have h1 := map_toCompCfg_right_step tm1 tm2 a
  rw [hab, Option.map_some] at h1
  exact h1.symm

end compComputerLemmas

/-- A Turing machine + a time function +
a proof it outputsInTime `f` in at most `time(input.length)` steps. -/
structure TimeComputable (f : List α → List α) where
  /-- the underlying bundled SingleTapeTM -/
  tm : SingleTapeTM α
  /-- a time function -/
  time : ℕ → ℕ
  /-- proof this machine outputsInTime `f` in at most `time(input.length)` steps -/
  outputsFun : ∀ a, tm.OutputsWithinTime a (f a) (time a.length)


/-- The identity map on α is computable in constant time. -/
def TimeComputable.id : TimeComputable (α := α) id where
  tm := idComputer
  time _ := 1
  outputsFun x := by
    refine ⟨1, le_refl 1, RelatesInSteps.single ?_⟩
    simp only [TransitionRelation, initCfg, haltCfg, idComputer, step, BiTape.optionMove]
    rfl

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
    {f g : List α → List α}
    (hf : TimeComputable f) (hg : TimeComputable g)
    (h_mono : Monotone hg.time) :
    (TimeComputable (g ∘ f)) where
  tm := compComputer hf.tm hg.tm
  -- perhaps it would be good to track the blow up separately?
  time l := (hf.time l) + hg.time (max 1 l + hf.time l)
  outputsFun a := by
    have hf_outputsFun := hf.outputsFun a
    have hg_outputsFun := hg.outputsFun (f a)
    simp only [OutputsWithinTime, initCfg, compComputer_q₀_eq, Function.comp_apply,
      haltCfg] at hg_outputsFun hf_outputsFun ⊢
    -- The computer reduces a to f a in time hf.time a
    have h_a_reducesTo_f_a :
        RelatesWithinSteps (compComputer hf.tm hg.tm).TransitionRelation
          { state := some (Sum.inl hf.tm.q₀), BiTape := BiTape.mk₁ a }
          { state := some (Sum.inr hg.tm.q₀), BiTape := BiTape.mk₁ (f a) }
          (hf.time a.length) :=
      comp_left_simulation hf.tm hg.tm a (f a) (hf.time a.length) hf_outputsFun
    have h_f_a_reducesTo_g_f_a :
        RelatesWithinSteps (compComputer hf.tm hg.tm).TransitionRelation
          { state := some (Sum.inr hg.tm.q₀), BiTape := BiTape.mk₁ (f a) }
          { state := none, BiTape := BiTape.mk₁ (g (f a)) }
          (hg.time (f a).length) := by
      -- Use the simulation lemma for the second machine
      have := comp_right_simulation hf.tm hg.tm
        { state := some hg.tm.q₀, BiTape := BiTape.mk₁ (f a) }
        { state := none, BiTape := BiTape.mk₁ (g (f a)) }
        (hg.time (f a).length)
        hg_outputsFun
      simp only [toCompCfg_right] at this
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
    {f g : List α → List α}
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
