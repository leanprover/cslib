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

Defines a single-tape Turing machine for computing functions on `List Symbol`
for finite alphabet `Symbol`.

## Design

Here are some design choices made in this file:

These machines have access to a single bidirectionally-infinite tape (`BiTape`)
which uses symbols from `Option Symbol`.

The transition function of the machine takes a state
and a tape alphabet character under the read-head (i.e. an `Option Symbol`)
and returns a `Stmt` describing the tape action to take,
as well as an optional new state to transition to (where `none` means halt).

We do not make the "halting state" a member of the state type for a few reasons:

* To avoid the need for passing a subtype of "non-halting states" to the transition function.
* To make clear that TMs are not expected to continue on after entering this special state
  (in contrast to, say, a DFA entering/leaving an accepting state).
* To make it simpler to match on halting when modifying a machine.

We also include the possibility for non-movement actions,
for convenience in composition of machines.

## Important Declarations

We define a number of structures related to Turing machine computation:

* `Stmt`: the write and movement operations a TM can do in a single step.
* `SingleTapeTM`: the TM itself.
* `Cfg`: the configuration of a TM, including internal and tape state.
* `TimeComputable f`: a TM for computing `f`, packaged with a bound on runtime.
* `PolyTimeComputable f`: `TimeComputable f` packaged with a polynomial bound on runtime.

We also provide ways of constructing polynomial-runtime TMs

* `PolyTimeComputable.id`: computes the identity function
* `PolyTimeComputable.comp`: computes the composition of polynomial time machines

## TODOs

- Encoding of types in lists to represent computations on arbitrary types.
- Add `∘` notation for `compComputer`.

-/

open Cslib Relation

namespace Turing

open BiTape StackTape

variable {Symbol : Type}

namespace SingleTapeTM

/--
A Turing machine "statement" is just a `Option`al command to move left or right,
and write a symbol (i.e. an `Option Symbol`, where `none` is the blank symbol) on the `BiTape`
-/
structure Stmt (Symbol : Type) where
  /-- The symbol to write at the current head position -/
  symbol : Option Symbol
  /-- The direction to move the tape head -/
  movement : Option Dir
deriving Inhabited

end SingleTapeTM

/--
A single-tape Turing machine
over the alphabet of `Option Symbol` (where `none` is the blank `BiTape` symbol).
-/
structure SingleTapeTM Symbol [Inhabited Symbol] [Fintype Symbol] where
  /-- type of state labels -/
  (State : Type)
  /-- finiteness of the state type -/
  [stateFintype : Fintype State]
  /-- Initial state -/
  (q₀ : State)
  /-- Transition function, mapping a state and a head symbol to a `Stmt` to invoke,
  and optionally the new state to transition to afterwards (`none` for halt) -/
  (tr : State → Option Symbol → SingleTapeTM.Stmt Symbol × Option State)

namespace SingleTapeTM

section Cfg

/-!
## Configurations of a Turing Machine

This section defines the configurations of a Turing machine,
the step function that lets the machine transition from one configuration to the next,
and the intended initial and final configurations.
-/

variable [Inhabited Symbol] [Fintype Symbol] (tm : SingleTapeTM Symbol)

instance : Inhabited tm.State := ⟨tm.q₀⟩

instance : Fintype tm.State := tm.stateFintype

instance inhabitedStmt : Inhabited (Stmt Symbol) := inferInstance

/--
The configurations of a Turing machine consist of:
an `Option`al state (or none for the halting state),
and a `BiTape` representing the tape contents.
-/
structure Cfg : Type where
  /-- the state of the TM (or none for the halting state) -/
  state : Option tm.State
  /-- the BiTape contents -/
  BiTape : BiTape Symbol
deriving Inhabited

/-- The step function corresponding to a `SingleTapeTM`. -/
@[simp]
def step : tm.Cfg → Option tm.Cfg
  | ⟨none, _⟩ =>
    -- If in the halting state, there is no next configuration
    none
  | ⟨some q', t⟩ =>
    -- If in state q', perform look up in the transition function
    match tm.tr q' t.head with
    -- and enter a new configuration with state q'' (or none for halting)
    -- and tape updated according to the Stmt
    | ⟨⟨wr, dir⟩, q''⟩ => some ⟨q'', (t.write wr).optionMove dir⟩

/--
The initial configuration corresponding to a list in the input alphabet.
Note that the entries of the tape constructed by `BiTape.mk₁` are all `some` values.
This is to ensure that distinct lists map to distinct initial configurations.
-/
def initCfg (tm : SingleTapeTM Symbol) (s : List Symbol) : tm.Cfg := ⟨some tm.q₀, BiTape.mk₁ s⟩

/-- The final configuration corresponding to a list in the output alphabet.
(We demand that the head halts at the leftmost position of the output.)
-/
def haltCfg (tm : SingleTapeTM Symbol) (s : List Symbol) : tm.Cfg := ⟨none, BiTape.mk₁ s⟩

/--
The space used by a configuration is the space used by its tape.
-/
def Cfg.space_used (tm : SingleTapeTM Symbol) (cfg : tm.Cfg) : ℕ := cfg.BiTape.space_used

@[scoped grind =]
lemma Cfg.space_used_initCfg (tm : SingleTapeTM Symbol) (s : List Symbol) :
    (tm.initCfg s).space_used = max 1 s.length := BiTape.space_used_mk₁ s

@[scoped grind =]
lemma Cfg.space_used_haltCfg (tm : SingleTapeTM Symbol) (s : List Symbol) :
    (tm.haltCfg s).space_used = max 1 s.length := BiTape.space_used_mk₁ s

lemma Cfg.space_used_step {tm : SingleTapeTM Symbol} (cfg cfg' : tm.Cfg)
    (hstep : tm.step cfg = some cfg') : cfg'.space_used ≤ cfg.space_used + 1 := by
  obtain ⟨_ | q, tape⟩ := cfg
  · simp [step] at hstep
  · simp only [step] at hstep
    generalize hM : tm.tr q tape.head = result at hstep
    obtain ⟨⟨wr, dir⟩, q''⟩ := result
    cases hstep; cases dir with
    | none => simp [Cfg.space_used, BiTape.optionMove, BiTape.space_used_write, hM]
    | some d => simpa [Cfg.space_used, BiTape.optionMove, BiTape.space_used_write, hM] using
        BiTape.space_used_move (tape.write wr) d

end Cfg

open Cfg

variable [Inhabited Symbol] [Fintype Symbol]

/--
The `TransitionRelation` corresponding to a `SingleTapeTM Symbol`
is defined by the `step` function,
which maps a configuration to its next configuration, if it exists.
-/
@[scoped grind =]
def TransitionRelation (tm : SingleTapeTM Symbol) (c₁ c₂ : tm.Cfg) : Prop := tm.step c₁ = some c₂

/-- A proof of `tm` outputting `l'` on input `l`. -/
def Outputs (tm : SingleTapeTM Symbol) (l l' : List Symbol) : Prop :=
  ReflTransGen tm.TransitionRelation (initCfg tm l) (haltCfg tm l')

/-- A proof of `tm` outputting `l'` on input `l` in at most `m` steps. -/
def OutputsWithinTime (tm : SingleTapeTM Symbol) (l l' : List Symbol) (m : ℕ) :=
  RelatesWithinSteps tm.TransitionRelation (initCfg tm l) (haltCfg tm l') m

/--
This lemma bounds the size blow-up of the output of a Turing machine.
It states that the increase in length of the output over the input is bounded by the runtime.
This is important for guaranteeing that composition of polynomial time Turing machines
remains polynomial time, as the input to the second machine
is bounded by the output length of the first machine.
-/
lemma output_length_le_input_length_add_time (tm : SingleTapeTM Symbol) (l l' : List Symbol) (t : ℕ)
    (h : tm.OutputsWithinTime l l' t) :
    l'.length ≤ max 1 l.length + t := by
  obtain ⟨steps, hsteps_le, hevals⟩ := h
  grind [hevals.apply_le_apply_add (Cfg.space_used tm)
      fun a b hstep ↦ Cfg.space_used_step a b (Option.mem_def.mp hstep)]

section Computers

/-- A Turing machine computing the identity. -/
def idComputer : SingleTapeTM Symbol where
  State := PUnit
  q₀ := PUnit.unit
  tr _ b := ⟨⟨b, none⟩, none⟩

/--
A Turing machine computing the composition of two other Turing machines.

If f and g are computed by Turing machines `tm1` and `tm2`
then we can construct a Turing machine which computes g ∘ f by first running `tm1`
and then, when `tm1` halts, transitioning to the start state of `tm2` and running `tm2`.
-/
def compComputer (tm1 tm2 : SingleTapeTM Symbol) : SingleTapeTM Symbol where
  -- The states of the composed machine are the disjoint union of the states of the input machines.
  State := tm1.State ⊕ tm2.State
  -- The start state is the start state of the first input machine.
  q₀ := .inl tm1.q₀
  tr q h :=
    match q with
    -- If we are in the first input machine's states, run that machine ...
    | .inl ql => match tm1.tr ql h with
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
      match tm2.tr qr h with
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

variable (tm1 tm2 : SingleTapeTM Symbol) (cfg1 : tm1.Cfg) (cfg2 : tm2.Cfg)

lemma compComputer_q₀_eq : (compComputer tm1 tm2).q₀ = Sum.inl tm1.q₀ := rfl

/--
Convert a `Cfg` over the first input machine to a config over the composed machine.
Note it may transition to the start state of the second machine if the first machine halts.
-/
private def toCompCfg_left : (compComputer tm1 tm2).Cfg :=
  match cfg1.state with
  | some q => ⟨some (Sum.inl q), cfg1.BiTape⟩
  | none => ⟨some (Sum.inr tm2.q₀), cfg1.BiTape⟩

/-- Convert a `Cfg` over the second input machine to a config over the composed machine -/
private def toCompCfg_right : (compComputer tm1 tm2).Cfg :=
  ⟨Option.map Sum.inr cfg2.state, cfg2.BiTape⟩

/-- The initial configuration for the composed machine, with the first machine starting. -/
private def initialCfg (input : List Symbol) : (compComputer tm1 tm2).Cfg :=
  ⟨some (Sum.inl tm1.q₀), BiTape.mk₁ input⟩

/-- The intermediate configuration for the composed machine,
after the first machine halts and the second machine starts. -/
private def intermediateCfg (intermediate : List Symbol) : (compComputer tm1 tm2).Cfg :=
  ⟨some (Sum.inr tm2.q₀), BiTape.mk₁ intermediate⟩

/-- The final configuration for the composed machine, after the second machine halts. -/
private def finalCfg (output : List Symbol) : (compComputer tm1 tm2).Cfg :=
  ⟨none, BiTape.mk₁ output⟩

/-- The left converting function commutes with steps of the machines. -/
private theorem map_toCompCfg_left_step (hcfg1 : cfg1.state.isSome) :
    Option.map (toCompCfg_left tm1 tm2) (tm1.step cfg1) =
      (compComputer tm1 tm2).step (toCompCfg_left tm1 tm2 cfg1) := by
  cases cfg1 with | mk state BiTape => cases state with
    | none => grind
    | some q =>
      simp only [step, toCompCfg_left, compComputer]
      generalize hM : tm1.tr q BiTape.head = result
      obtain ⟨⟨wr, dir⟩, nextState⟩ := result
      cases nextState <;> grind [toCompCfg_left]

/-- The right converting function commutes with steps of the machines. -/
private theorem map_toCompCfg_right_step :
    Option.map (toCompCfg_right tm1 tm2) (tm2.step cfg2) =
      (compComputer tm1 tm2).step (toCompCfg_right tm1 tm2 cfg2) := by
  cases cfg2 with
  | mk state BiTape =>
    cases state with
    | none =>
      simp only [step, toCompCfg_right, Option.map_none, compComputer]
    | some q =>
      generalize hM : tm2.tr q BiTape.head = result
      obtain ⟨⟨wr, dir⟩, nextState⟩ := result
      simp only [compComputer]
      grind [toCompCfg_right, step, compComputer]

/--
Simulation for the first phase of the composed computer.
When the first machine runs from start to halt, the composed machine
runs from start (with Sum.inl state) to Sum.inr tm2.q₀ (the start of the second phase).
This takes the same number of steps because the halt transition becomes a transition to the
second machine.
-/
private theorem comp_left_relatesWithinSteps (input intermediate : List Symbol) (t : ℕ)
    (htm1 :
      RelatesWithinSteps tm1.TransitionRelation
        (tm1.initCfg input)
        (tm1.haltCfg intermediate)
        t) :
    RelatesWithinSteps (compComputer tm1 tm2).TransitionRelation
      (initialCfg tm1 tm2 input)
      (intermediateCfg tm1 tm2 intermediate)
      t := by
  simp only [initialCfg, intermediateCfg, initCfg, haltCfg] at htm1 ⊢
  refine RelatesWithinSteps.map (toCompCfg_left tm1 tm2) ?_ htm1
  intro a b hab
  have ha : a.state.isSome := by
    simp only [TransitionRelation, step] at hab
    cases a with | mk state _ => cases state <;> simp_all
  have h1 := map_toCompCfg_left_step tm1 tm2 a ha
  rw [hab, Option.map_some] at h1
  exact h1.symm

/--
Simulation for the second phase of the composed computer.
When the second machine runs from start to halt, the composed machine
runs from Sum.inr tm2.q₀ to halt.
-/
private theorem comp_right_relatesWithinSteps (intermediate output : List Symbol) (t : ℕ)
    (htm2 :
      RelatesWithinSteps tm2.TransitionRelation
        (tm2.initCfg intermediate)
        (tm2.haltCfg output)
        t) :
    RelatesWithinSteps (compComputer tm1 tm2).TransitionRelation
      (intermediateCfg tm1 tm2 intermediate)
      (finalCfg tm1 tm2 output)
      t := by
  simp only [intermediateCfg, finalCfg, initCfg, haltCfg] at htm2 ⊢
  refine RelatesWithinSteps.map (toCompCfg_right tm1 tm2) ?_ htm2
  intro a b hab
  grind [map_toCompCfg_right_step tm1 tm2 a]

end compComputerLemmas

end Computers

/-!
## Time Computability

This section defines the notion of time-bounded Turing Machines
-/

section TimeComputable

variable [Inhabited Symbol] [Fintype Symbol]

/-- A Turing machine + a time function +
a proof it outputs `f` in at most `time(input.length)` steps. -/
structure TimeComputable (f : List Symbol → List Symbol) where
  /-- the underlying bundled SingleTapeTM -/
  tm : SingleTapeTM Symbol
  /-- a bound on runtime -/
  time_bound : ℕ → ℕ
  /-- proof this machine outputs `f` in at most `time_bound(input.length)` steps -/
  outputsFunInTime (a) : tm.OutputsWithinTime a (f a) (time_bound a.length)


/-- The identity map on Symbol is computable in constant time. -/
def TimeComputable.id : TimeComputable (Symbol := Symbol) id where
  tm := idComputer
  time_bound _ := 1
  outputsFunInTime _ := ⟨1, le_rfl, RelatesInSteps.single rfl⟩

/--
Time bounds for `compComputer`.

The `compComputer` of two machines which have time bounds is bounded by

* The time taken by the first machine on the input size
* added to the time taken by the second machine on the output size of the first machine
  (which is itself bounded by the time taken by the first machine)

Note that we require the time function of the second machine to be monotone;
this is to ensure that if the first machine returns an output
which is shorter than the maximum possible length of output for that input size,
then the time bound for the second machine still holds for that shorter input to the second machine.
-/
def TimeComputable.comp {f g : List Symbol → List Symbol}
    (hf : TimeComputable f) (hg : TimeComputable g)
    (h_mono : Monotone hg.time_bound) :
    (TimeComputable (g ∘ f)) where
  tm := compComputer hf.tm hg.tm
  -- perhaps it would be good to track the blow up separately?
  time_bound l := (hf.time_bound l) + hg.time_bound (max 1 l + hf.time_bound l)
  outputsFunInTime a := by
    have hf_outputsFun := hf.outputsFunInTime a
    have hg_outputsFun := hg.outputsFunInTime (f a)
    simp only [OutputsWithinTime, initCfg, compComputer_q₀_eq, Function.comp_apply,
      haltCfg] at hg_outputsFun hf_outputsFun ⊢
    -- The computer reduces a to f a in time hf.time_bound a.length
    have h_a_reducesTo_f_a :
        RelatesWithinSteps (compComputer hf.tm hg.tm).TransitionRelation
          (initialCfg hf.tm hg.tm a)
          (intermediateCfg hf.tm hg.tm (f a))
          (hf.time_bound a.length) :=
      comp_left_relatesWithinSteps hf.tm hg.tm a (f a)
        (hf.time_bound a.length) hf_outputsFun
    -- The computer reduces f a to g (f a) in time hg.time_bound (f a).length
    have h_f_a_reducesTo_g_f_a :
        RelatesWithinSteps (compComputer hf.tm hg.tm).TransitionRelation
          (intermediateCfg hf.tm hg.tm (f a))
          (finalCfg hf.tm hg.tm (g (f a)))
          (hg.time_bound (f a).length) :=
      comp_right_relatesWithinSteps hf.tm hg.tm (f a) (g (f a))
        (hg.time_bound (f a).length) hg_outputsFun
    -- Therefore, the computer reduces a to g (f a) in the sum of those times.
    have h_a_reducesTo_g_f_a := RelatesWithinSteps.trans h_a_reducesTo_f_a h_f_a_reducesTo_g_f_a
    apply RelatesWithinSteps.of_le h_a_reducesTo_g_f_a
    refine Nat.add_le_add_left ?_ (hf.time_bound a.length)
    · apply h_mono
      -- Use the lemma about output length being bounded by input length + time
      exact output_length_le_input_length_add_time hf.tm _ _ _ (hf.outputsFunInTime a)

end TimeComputable

/-!
## Polynomial Time Computability

This section defines polynomial time computable functions on Turing machines,
and proves that:

* The identity function is polynomial time computable
* The composition of two polynomial time computable functions is polynomial time computable

-/

section PolyTimeComputable

open Polynomial

variable [Inhabited Symbol] [Fintype Symbol]

/-- A Turing machine + a polynomial time function +
a proof it outputs `f` in at most `time(input.length)` steps. -/
structure PolyTimeComputable (f : List Symbol → List Symbol) extends TimeComputable f where
  /-- a polynomial time bound -/
  poly : Polynomial ℕ
  /-- proof that this machine outputs `f` in at most `time(input.length)` steps -/
  bounds : ∀ n, time_bound n ≤ poly.eval n

/-- A proof that the identity map on Symbol is computable in polytime. -/
noncomputable def PolyTimeComputable.id : PolyTimeComputable (Symbol := Symbol) id where
  toTimeComputable := TimeComputable.id
  poly := 1
  bounds _ := by simp [TimeComputable.id]

-- TODO remove `h_mono` assumption
-- by developing function to convert PolyTimeComputable into one with monotone time bound
/--
A proof that the composition of two polytime computable functions is polytime computable.
-/
noncomputable def PolyTimeComputable.comp {f g : List Symbol → List Symbol}
    (hf : PolyTimeComputable f) (hg : PolyTimeComputable g)
    (h_mono : Monotone hg.time_bound) :
    PolyTimeComputable (g ∘ f) where
  toTimeComputable := TimeComputable.comp hf.toTimeComputable hg.toTimeComputable h_mono
  poly := hf.poly + hg.poly.comp (1 + X + hf.poly)
  bounds n := by
    simp only [TimeComputable.comp, eval_add, eval_comp, eval_X, eval_one]
    apply add_le_add
    · exact hf.bounds n
    · exact (h_mono (add_le_add (by omega) (hf.bounds n))).trans (hg.bounds _)

end PolyTimeComputable

end SingleTapeTM

end Turing
