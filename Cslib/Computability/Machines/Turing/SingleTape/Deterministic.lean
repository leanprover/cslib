/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Pim Spelier, Daan van Gent
-/

module

public import Cslib.Foundations.Data.BiTape
public import Cslib.Foundations.Data.RelatesInSteps
public import Mathlib.Algebra.Polynomial.Eval.Defs

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

@[expose] public section

open Relation

namespace Cslib.Turing

open BiTape StackTape
open _root_.Turing

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
def Cfg.spaceUsed (tm : SingleTapeTM Symbol) (cfg : tm.Cfg) : ℕ := cfg.BiTape.spaceUsed

@[scoped grind =]
lemma Cfg.spaceUsed_initCfg (tm : SingleTapeTM Symbol) (s : List Symbol) :
    (tm.initCfg s).spaceUsed = max 1 s.length := BiTape.spaceUsed_mk₁ s

@[scoped grind =]
lemma Cfg.spaceUsed_haltCfg (tm : SingleTapeTM Symbol) (s : List Symbol) :
    (tm.haltCfg s).spaceUsed = max 1 s.length := BiTape.spaceUsed_mk₁ s

lemma Cfg.spaceUsed_step {tm : SingleTapeTM Symbol} (cfg cfg' : tm.Cfg)
    (hstep : tm.step cfg = some cfg') : cfg'.spaceUsed ≤ cfg.spaceUsed + 1 := by
  obtain ⟨_ | q, tape⟩ := cfg
  · simp [step] at hstep
  · simp only [step] at hstep
    generalize hM : tm.tr q tape.head = result at hstep
    obtain ⟨⟨wr, dir⟩, q''⟩ := result
    cases hstep; cases dir with
    | none => simp [Cfg.spaceUsed, BiTape.optionMove, BiTape.spaceUsed_write, hM]
    | some d => simpa [Cfg.spaceUsed, BiTape.optionMove, BiTape.spaceUsed_write, hM] using
        BiTape.spaceUsed_move (tape.write wr) d

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
  grind [hevals.apply_le_apply_add (Cfg.spaceUsed tm)
      fun a b hstep ↦ Cfg.spaceUsed_step a b (Option.mem_def.mp hstep)]

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
      #adaptation_note
      /-- A grind regression found moving to nightly-2026-03-31 (changes from lean#13166) -/
      cases nextState <;> (simp_all; rfl)

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

/-- A Turing machine + a time function +
a proof it outputs `f` in at most `time(input.length)` steps. -/
structure TimeComputable (f : List Symbol → List Symbol) where
  /-- the underlying bundled SingleTapeTM -/
  tm : SingleTapeTM Symbol
  /-- a bound on runtime -/
  timeBound : ℕ → ℕ
  /-- proof this machine outputs `f` in at most `timeBound(input.length)` steps -/
  outputsFunInTime (a) : tm.OutputsWithinTime a (f a) (timeBound a.length)


/-- The identity map on Symbol is computable in constant time. -/
def TimeComputable.id : TimeComputable (Symbol := Symbol) id where
  tm := idComputer
  timeBound _ := 1
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
    (h_mono : Monotone hg.timeBound) :
    (TimeComputable (g ∘ f)) where
  tm := compComputer hf.tm hg.tm
  -- perhaps it would be good to track the blow up separately?
  timeBound l := (hf.timeBound l) + hg.timeBound (max 1 l + hf.timeBound l)
  outputsFunInTime a := by
    have hf_outputsFun := hf.outputsFunInTime a
    have hg_outputsFun := hg.outputsFunInTime (f a)
    simp only [OutputsWithinTime, initCfg, compComputer_q₀_eq, Function.comp_apply,
      haltCfg] at hg_outputsFun hf_outputsFun ⊢
    -- The computer reduces a to f a in time hf.timeBound a.length
    have h_a_reducesTo_f_a :
        RelatesWithinSteps (compComputer hf.tm hg.tm).TransitionRelation
          (initialCfg hf.tm hg.tm a)
          (intermediateCfg hf.tm hg.tm (f a))
          (hf.timeBound a.length) :=
      comp_left_relatesWithinSteps hf.tm hg.tm a (f a)
        (hf.timeBound a.length) hf_outputsFun
    -- The computer reduces f a to g (f a) in time hg.timeBound (f a).length
    have h_f_a_reducesTo_g_f_a :
        RelatesWithinSteps (compComputer hf.tm hg.tm).TransitionRelation
          (intermediateCfg hf.tm hg.tm (f a))
          (finalCfg hf.tm hg.tm (g (f a)))
          (hg.timeBound (f a).length) :=
      comp_right_relatesWithinSteps hf.tm hg.tm (f a) (g (f a))
        (hg.timeBound (f a).length) hg_outputsFun
    -- Therefore, the computer reduces a to g (f a) in the sum of those times.
    have h_a_reducesTo_g_f_a := RelatesWithinSteps.trans h_a_reducesTo_f_a h_f_a_reducesTo_g_f_a
    apply RelatesWithinSteps.of_le h_a_reducesTo_g_f_a
    refine Nat.add_le_add_left ?_ (hf.timeBound a.length)
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

/-- A Turing machine + a polynomial time function +
a proof it outputs `f` in at most `time(input.length)` steps. -/
structure PolyTimeComputable (f : List Symbol → List Symbol) extends TimeComputable f where
  /-- a polynomial time bound -/
  poly : Polynomial ℕ
  /-- proof that this machine outputs `f` in at most `time(input.length)` steps -/
  bounds : ∀ n, timeBound n ≤ poly.eval n

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
    (h_mono : Monotone hg.timeBound) :
    PolyTimeComputable (g ∘ f) where
  toTimeComputable := TimeComputable.comp hf.toTimeComputable hg.toTimeComputable h_mono
  poly := hf.poly + hg.poly.comp (1 + X + hf.poly)
  bounds n := by
    simp only [TimeComputable.comp, eval_add, eval_comp, eval_X, eval_one]
    apply add_le_add
    · exact hf.bounds n
    · exact (h_mono (add_le_add (by omega) (hf.bounds n))).trans (hg.bounds _)

/-- Evaluation of a polynomial with natural-number coefficients is monotone in its argument. -/
lemma monotone_poly_eval (p : Polynomial ℕ) : Monotone fun n => p.eval n := by
  intro a b hab
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [eval_add] using Nat.add_le_add hp hq
  | monomial n c =>
    simpa only [eval_monomial] using Nat.mul_le_mul le_rfl (Nat.pow_le_pow_left hab n)

/-- Renormalize a polynomial-time machine so that its time bound is the (automatically monotone)
evaluation of its bounding polynomial. This drops the monotonicity side-condition from `comp`. -/
noncomputable def PolyTimeComputable.normalize {f : List Symbol → List Symbol}
    (h : PolyTimeComputable f) : PolyTimeComputable f where
  toTimeComputable :=
    { tm := h.tm
      timeBound := fun n => h.poly.eval n
      outputsFunInTime := fun a =>
        RelatesWithinSteps.of_le (h.outputsFunInTime a) (h.bounds a.length) }
  poly := h.poly
  bounds _ := le_rfl

lemma PolyTimeComputable.monotone_normalize {f : List Symbol → List Symbol}
    (h : PolyTimeComputable f) : Monotone h.normalize.timeBound :=
  monotone_poly_eval h.poly

/-- The composition of two polynomial-time computable functions is polynomial-time computable,
with no monotonicity side-condition (unlike `comp`, which this specializes via `normalize`). -/
noncomputable def PolyTimeComputable.comp' {f g : List Symbol → List Symbol}
    (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
    PolyTimeComputable (g ∘ f) :=
  hf.comp hg.normalize hg.monotone_normalize

end PolyTimeComputable

/-!
## Functions with finite domain of interest

Given a target function `g : List Symbol → List Symbol` and a finite set `S` of "inputs of
interest", we construct a `SingleTapeTM` computing a function that agrees with `g` on every
element of `S` (and outputs `[]` elsewhere), and show it runs in linear (hence polynomial) time.

The machine works in two phases:

* **Read phase.** It scans the input left to right, erasing each symbol as it goes and tracking,
  in its (finite) state, the prefix read so far — as long as that prefix is still a prefix of some
  element of `S`; otherwise it enters a "dead" state. Writing a blank before every rightward move
  keeps the left half of the tape normalized to the empty tape.
* **Write phase.** On reaching the end of the input it knows exactly which element of `S` (if any)
  was the input, hence which fixed output string to produce. It writes that string onto the (now
  blank) tape in reverse, moving left after each symbol, landing exactly on the halting
  configuration.

Since the read phase takes `input.length` steps and the write phase is bounded by a constant
(the longest possible output), the runtime is linear.
-/

section FinsetDomain

open Polynomial

variable [DecidableEq Symbol]

/-- The finite set of all prefixes of elements of `S`. -/
def prefixesFinset (S : Finset (List Symbol)) : Finset (List Symbol) :=
  S.biUnion fun s => s.inits.toFinset

omit [Inhabited Symbol] [Fintype Symbol] in
@[simp]
lemma mem_prefixesFinset {S : Finset (List Symbol)} {p : List Symbol} :
    p ∈ prefixesFinset S ↔ ∃ s ∈ S, p <+: s := by
  simp [prefixesFinset, List.mem_inits]

omit [Inhabited Symbol] [Fintype Symbol] in
lemma mem_prefixesFinset_self {S : Finset (List Symbol)} {s : List Symbol} (hs : s ∈ S) :
    s ∈ prefixesFinset S :=
  mem_prefixesFinset.2 ⟨s, hs, List.prefix_rfl⟩

omit [Inhabited Symbol] [Fintype Symbol] in
lemma prefixesFinset_closed {S : Finset (List Symbol)} {p : List Symbol} {a : Symbol}
    (h : p ++ [a] ∈ prefixesFinset S) : p ∈ prefixesFinset S := by
  rw [mem_prefixesFinset] at *
  obtain ⟨s, hs, hp⟩ := h
  exact ⟨s, hs, (List.prefix_append p [a]).trans hp⟩

/-- The possible output strings: `g s` for `s ∈ S`, together with `[]`. -/
def outputsFinset (g : List Symbol → List Symbol) (S : Finset (List Symbol)) :
    Finset (List Symbol) :=
  insert [] (S.image g)

/-- The reachable "remaining to write" states: suffixes of the reverses of possible outputs. -/
def writeStatesFinset (g : List Symbol → List Symbol) (S : Finset (List Symbol)) :
    Finset (List Symbol) :=
  (outputsFinset g S).biUnion fun c => c.reverse.tails.toFinset

omit [Inhabited Symbol] [Fintype Symbol] in
lemma mem_writeStatesFinset {g : List Symbol → List Symbol} {S : Finset (List Symbol)}
    {w : List Symbol} :
    w ∈ writeStatesFinset g S ↔ ∃ c ∈ outputsFinset g S, w <:+ c.reverse := by
  simp [writeStatesFinset, List.mem_tails]

omit [Inhabited Symbol] [Fintype Symbol] in
lemma nil_mem_writeStatesFinset {g : List Symbol → List Symbol} {S : Finset (List Symbol)} :
    ([] : List Symbol) ∈ writeStatesFinset g S :=
  mem_writeStatesFinset.2 ⟨[], Finset.mem_insert_self _ _, List.nil_suffix⟩

omit [Inhabited Symbol] [Fintype Symbol] in
lemma writeStatesFinset_closed {g : List Symbol → List Symbol} {S : Finset (List Symbol)}
    {a : Symbol} {w : List Symbol} (h : a :: w ∈ writeStatesFinset g S) :
    w ∈ writeStatesFinset g S := by
  rw [mem_writeStatesFinset] at *
  obtain ⟨c, hc, hw⟩ := h
  exact ⟨c, hc, (List.suffix_cons a w).trans hw⟩

omit [Inhabited Symbol] [Fintype Symbol] in
lemma reverse_output_mem_writeStatesFinset {g : List Symbol → List Symbol}
    {S : Finset (List Symbol)} {input : List Symbol} :
    (if input ∈ S then g input else ([] : List Symbol)).reverse ∈ writeStatesFinset g S := by
  rw [mem_writeStatesFinset]
  refine ⟨_, ?_, List.suffix_rfl⟩
  unfold outputsFinset
  split
  · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem g ‹_›)
  · exact Finset.mem_insert_self _ _

/-- States of the lookup machine: either a read-phase state (an optional prefix, `none` being the
"dead" state after diverging from every element of `S`), or a write-phase state (the reversed
suffix of the output still to be written). -/
abbrev LookupState (g : List Symbol → List Symbol) (S : Finset (List Symbol)) : Type :=
  Option {p : List Symbol // p ∈ prefixesFinset S} ⊕ {w : List Symbol // w ∈ writeStatesFinset g S}

variable (g : List Symbol → List Symbol) (S : Finset (List Symbol))

/-- The read-phase state after having consumed prefix `p` of the input: the viable prefix `p`
itself if it is still a prefix of some element of `S`, otherwise the dead state. -/
def readState (p : List Symbol) : LookupState g S :=
  Sum.inl (if h : p ∈ prefixesFinset S then some ⟨p, h⟩ else none)

/-- The lookup machine for `g` and `S`. See the module docstring above for the construction. -/
def lookupTM : SingleTapeTM Symbol where
  State := LookupState g S
  q₀ := readState g S []
  tr q sym :=
    match q with
    | Sum.inl (some ⟨p, _⟩) =>
      match sym with
      | some a => (⟨none, some .right⟩, some (readState g S (p ++ [a])))
      | none =>
        (⟨none, none⟩,
          some (Sum.inr ⟨(if p ∈ S then g p else []).reverse,
            reverse_output_mem_writeStatesFinset⟩))
    | Sum.inl none =>
      match sym with
      | some _ => (⟨none, some .right⟩, some (Sum.inl none))
      | none => (⟨none, none⟩, some (Sum.inr ⟨[], nil_mem_writeStatesFinset⟩))
    | Sum.inr ⟨w, hw⟩ =>
      match w, hw with
      | [], _ => (⟨none, none⟩, none)
      | [a], _ => (⟨some a, none⟩, none)
      | a :: b :: rest, hw =>
        (⟨some a, some .left⟩, some (Sum.inr ⟨b :: rest, writeStatesFinset_closed hw⟩))

omit [Inhabited Symbol] [Fintype Symbol] [DecidableEq Symbol] in
/-- Erasing the head of a nonempty tape and moving right yields the tape of the remaining input.
This is the tape action performed on each step of the read phase; writing a blank before the move
keeps the left half of the tape empty. -/
private lemma mk₁_erase_moveRight (a : Symbol) (s : List Symbol) :
    ((BiTape.mk₁ (a :: s)).write none).optionMove (some .right) = BiTape.mk₁ s := by
  cases s <;> rfl

omit [Inhabited Symbol] [Fintype Symbol] [DecidableEq Symbol] in
private lemma mk₁_cons_head (a : Symbol) (s : List Symbol) :
    (BiTape.mk₁ (a :: s)).head = some a := rfl

/-- The tape configuration during the write phase: blank head, empty left half, and the
already-written suffix `r` of the output in the right half. -/
private def writeTape (r : List Symbol) : BiTape Symbol := ⟨none, ∅, StackTape.mapSome r⟩

omit [Inhabited Symbol] [Fintype Symbol] [DecidableEq Symbol] in
private lemma writeTape_nil : writeTape ([] : List Symbol) = (∅ : BiTape Symbol) := rfl

omit [Inhabited Symbol] [Fintype Symbol] [DecidableEq Symbol] in
/-- Writing the final output symbol on the blank head (without moving) completes the output tape. -/
private lemma writeTape_lastWrite (a : Symbol) (r : List Symbol) :
    ((writeTape r).write (some a)).optionMove none = BiTape.mk₁ (a :: r) := rfl

omit [Inhabited Symbol] [Fintype Symbol] [DecidableEq Symbol] in
/-- Writing a symbol on the blank head and moving left prepends it to the written suffix. -/
private lemma writeTape_step (a : Symbol) (r : List Symbol) :
    ((writeTape r).write (some a)).optionMove (some .left) = writeTape (a :: r) := rfl

/-- A single step of the read phase: reading a symbol advances the tracked prefix and erases the
symbol from the tape. -/
private lemma readState_step (p : List Symbol) (a : Symbol) (s : List Symbol) :
    (lookupTM g S).TransitionRelation
      ⟨some (readState g S p), BiTape.mk₁ (a :: s)⟩
      ⟨some (readState g S (p ++ [a])), BiTape.mk₁ s⟩ := by
  simp only [TransitionRelation]
  by_cases hp : p ∈ prefixesFinset S
  · simp only [readState, dif_pos hp, SingleTapeTM.step, lookupTM, mk₁_cons_head,
      mk₁_erase_moveRight]
  · have hp' : p ++ [a] ∉ prefixesFinset S := fun h => hp (prefixesFinset_closed h)
    simp only [readState, dif_neg hp, dif_neg hp', SingleTapeTM.step, lookupTM, mk₁_cons_head,
      mk₁_erase_moveRight]

/-- The full read phase: starting from a tracked prefix `p` and the input on the tape, the machine
consumes the whole input (erasing it), advancing the prefix to `p ++ input`, in `input.length`
steps. -/
private lemma read_phase (input p : List Symbol) :
    RelatesInSteps (lookupTM g S).TransitionRelation
      ⟨some (readState g S p), BiTape.mk₁ input⟩
      ⟨some (readState g S (p ++ input)), BiTape.mk₁ []⟩
      input.length := by
  induction input generalizing p with
  | nil => simp only [List.append_nil, List.length_nil]; exact RelatesInSteps.refl _
  | cons a rest ih =>
    have hstep := readState_step g S p a rest
    have hrest := ih (p ++ [a])
    rw [List.append_assoc] at hrest
    simp only [List.singleton_append] at hrest
    exact RelatesInSteps.head _ _ _ _ hstep hrest

omit [Inhabited Symbol] [Fintype Symbol] [DecidableEq Symbol] in
private lemma mk₁_nil_head : (BiTape.mk₁ ([] : List Symbol)).head = none := rfl

omit [Inhabited Symbol] [Fintype Symbol] [DecidableEq Symbol] in
private lemma mk₁_nil_noop :
    ((BiTape.mk₁ ([] : List Symbol)).write none).optionMove none = BiTape.mk₁ [] := rfl

omit [Inhabited Symbol] [Fintype Symbol] [DecidableEq Symbol] in
private lemma nil_noop : ((∅ : BiTape Symbol).write none).optionMove none = ∅ := rfl

/-- The write-phase state entered on reaching the end of the input: it carries the reversed output
string `(if input ∈ S then g input else []).reverse` still to be written. -/
def writeStartState (input : List Symbol) : LookupState g S :=
  Sum.inr ⟨(if input ∈ S then g input else []).reverse, reverse_output_mem_writeStatesFinset⟩

omit [Inhabited Symbol] [Fintype Symbol] in
lemma writeStartState_of_not_mem (input : List Symbol) (h : input ∉ S) :
    writeStartState g S input = Sum.inr ⟨[], nil_mem_writeStatesFinset⟩ := by
  unfold writeStartState
  congr 1
  exact Subtype.ext (by simp [if_neg h])

/-- The handoff step from the read phase to the write phase: on reaching the end of the input, the
machine switches to the write-phase state without moving. -/
private lemma handoff (input : List Symbol) :
    (lookupTM g S).TransitionRelation
      ⟨some (readState g S input), BiTape.mk₁ []⟩
      ⟨some (writeStartState g S input), BiTape.mk₁ []⟩ := by
  simp only [TransitionRelation]
  by_cases hp : input ∈ prefixesFinset S
  · simp only [readState, dif_pos hp, writeStartState, SingleTapeTM.step, lookupTM, mk₁_nil_head,
      mk₁_nil_noop]
  · have hs : input ∉ S := fun h => hp (mem_prefixesFinset_self h)
    have hstep : (lookupTM g S).step ⟨some (readState g S input), BiTape.mk₁ []⟩
        = some ⟨some (Sum.inr ⟨[], nil_mem_writeStatesFinset⟩), BiTape.mk₁ []⟩ := by
      simp only [readState, dif_neg hp, SingleTapeTM.step, lookupTM, mk₁_nil_head, mk₁_nil_noop]
    rw [hstep, writeStartState_of_not_mem g S input hs]

/-- A single non-terminal step of the write phase: write the head symbol and move left, prepending
it to the already-written output suffix. -/
private lemma write_step (a b : Symbol) (rest r : List Symbol)
    (hw : a :: b :: rest ∈ writeStatesFinset g S) :
    (lookupTM g S).TransitionRelation
      ⟨some (Sum.inr ⟨a :: b :: rest, hw⟩), writeTape r⟩
      ⟨some (Sum.inr ⟨b :: rest, writeStatesFinset_closed hw⟩), writeTape (a :: r)⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, lookupTM, writeTape_step]

/-- The terminal step of the write phase: write the last (leftmost) output symbol and halt. -/
private lemma write_step_last (a : Symbol) (r : List Symbol)
    (hw : [a] ∈ writeStatesFinset g S) :
    (lookupTM g S).TransitionRelation
      ⟨some (Sum.inr ⟨[a], hw⟩), writeTape r⟩
      ⟨none, BiTape.mk₁ (a :: r)⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, lookupTM, writeTape_lastWrite]

/-- The degenerate write phase for the empty output: halt immediately, leaving the tape blank. -/
private lemma write_step_nil (hw : ([] : List Symbol) ∈ writeStatesFinset g S) :
    (lookupTM g S).TransitionRelation
      ⟨some (Sum.inr ⟨[], hw⟩), (∅ : BiTape Symbol)⟩
      ⟨none, (∅ : BiTape Symbol)⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, lookupTM, nil_noop]

/-- The full write phase for a nonempty reversed output `w`: writes the output into the right half
of the tape, landing on the halting configuration, in `w.length` steps. -/
private lemma write_phase (w r : List Symbol) (hw : w ∈ writeStatesFinset g S) (hne : w ≠ []) :
    RelatesInSteps (lookupTM g S).TransitionRelation
      ⟨some (Sum.inr ⟨w, hw⟩), writeTape r⟩
      ⟨none, BiTape.mk₁ (w.reverse ++ r)⟩
      w.length := by
  induction w generalizing r with
  | nil => exact absurd rfl hne
  | cons a tl ih =>
    cases tl with
    | nil => simpa using RelatesInSteps.single (write_step_last g S a r hw)
    | cons b rest =>
      have hstep := write_step g S a b rest r hw
      have hrest := ih (a :: r) (writeStatesFinset_closed hw) (by simp)
      rw [show (a :: b :: rest).reverse ++ r = (b :: rest).reverse ++ (a :: r) by simp]
      exact RelatesInSteps.head _ _ _ _ hstep hrest

/-- The complete write phase (from a blank tape): writes output `c` and halts, within `c.length + 1`
steps. -/
private lemma write_run (c : List Symbol) (hw : c.reverse ∈ writeStatesFinset g S) :
    RelatesWithinSteps (lookupTM g S).TransitionRelation
      ⟨some (Sum.inr ⟨c.reverse, hw⟩), (∅ : BiTape Symbol)⟩
      ⟨none, BiTape.mk₁ c⟩
      (c.length + 1) := by
  cases c with
  | nil => exact RelatesWithinSteps.single (write_step_nil g S hw)
  | cons a tl =>
    have hwp := write_phase g S (a :: tl).reverse [] hw (by simp)
    rw [writeTape_nil, List.reverse_reverse, List.append_nil, List.length_reverse] at hwp
    exact (RelatesWithinSteps.of_relatesInSteps hwp).of_le (Nat.le_succ _)

/-- A uniform bound on the length of any output the machine can produce. -/
def maxOutputLen (g : List Symbol → List Symbol) (S : Finset (List Symbol)) : ℕ :=
  S.sup fun s => (g s).length

open Polynomial in
/-- The lookup machine runs in linear (hence polynomial) time and agrees with `g` on `S`:
any function of the form `fun s => if s ∈ S then g s else []` is polynomial-time computable. -/
noncomputable def PolyTimeComputable.ofFinsetDomain :
    PolyTimeComputable (fun s => if s ∈ S then g s else []) where
  tm := lookupTM g S
  timeBound n := n + maxOutputLen g S + 2
  poly := X + C (maxOutputLen g S + 2)
  bounds n := by simp only [eval_add, eval_X, eval_C]; omega
  outputsFunInTime a := by
    simp only [OutputsWithinTime]
    set c := (if a ∈ S then g a else []) with hc
    have hc_len : c.length ≤ maxOutputLen g S := by
      rw [hc]
      unfold maxOutputLen
      split
      · exact Finset.le_sup (f := fun s => (g s).length) ‹a ∈ S›
      · exact Nat.zero_le _
    have hread := read_phase g S a []
    rw [List.nil_append] at hread
    have hchain :
        RelatesWithinSteps (lookupTM g S).TransitionRelation
          (initCfg (lookupTM g S) a)
          (haltCfg (lookupTM g S) c)
          (a.length + (1 + (c.length + 1))) :=
      (RelatesWithinSteps.of_relatesInSteps hread).trans
        ((RelatesWithinSteps.single (handoff g S a)).trans
          (write_run g S c reverse_output_mem_writeStatesFinset))
    exact hchain.of_le (by omega)

end FinsetDomain

/-!
## Running a machine on the tail of the input

Given a machine for `f`, we build a machine computing
`fun input => match input with | [] => [] | b :: rest => b :: f rest`,
i.e. one that preserves the leading symbol and applies `f` to the remaining input. This is the
key ingredient for lifting polynomial-time computability along `Option.map` (the leading symbol
being the `some`/`none` tag of the `Option` encoding).

The machine erases the head (remembering it in its finite state), runs the underlying machine on
the tail — the erased cell reads as blank, so the simulation is faithful — and finally re-inserts
the remembered symbol to the left of the produced output.
-/

section OnTail

open Polynomial

/-- The function computed by `onTailComputer tm`: preserve the head symbol and apply the underlying
function to the tail (the empty input maps to the empty output). -/
def onTailFun (f : List Symbol → List Symbol) : List Symbol → List Symbol
  | [] => []
  | b :: rest => b :: f rest

/-- A Turing machine that runs `tm` on the tail of the input while preserving the leading symbol.
Its states are: a start state, the states of `tm` paired with the remembered leading symbol, and
two finishing states (also carrying the remembered symbol). -/
def onTailComputer (tm : SingleTapeTM Symbol) : SingleTapeTM Symbol where
  State := Unit ⊕ (tm.State × Symbol) ⊕ Symbol ⊕ Symbol
  q₀ := Sum.inl ()
  tr q sym :=
    match q with
    | Sum.inl () =>
      match sym with
      -- empty input: halt immediately with empty output
      | none => (⟨none, none⟩, none)
      -- erase the head, remember it, and start the underlying machine
      | some b => (⟨none, some .right⟩, some (Sum.inr (Sum.inl (tm.q₀, b))))
    | Sum.inr (Sum.inl (q, b)) =>
      match tm.tr q sym with
      | (stmt, some q') => (stmt, some (Sum.inr (Sum.inl (q', b))))
      -- underlying machine halts: move to the finishing phase
      | (stmt, none) => (stmt, some (Sum.inr (Sum.inr (Sum.inl b))))
    -- finish (read): write the head back unchanged and step left onto the blank cell
    | Sum.inr (Sum.inr (Sum.inl b)) => (⟨sym, some .left⟩, some (Sum.inr (Sum.inr (Sum.inr b))))
    -- finish (write): write the remembered symbol and halt
    | Sum.inr (Sum.inr (Sum.inr b)) => (⟨some b, none⟩, none)

omit [Inhabited Symbol] [Fintype Symbol] in
/-- Writing the head symbol back unchanged and moving left turns `mk₁ out` into `writeTape out`,
placing a blank under the head ready to receive the preserved symbol. -/
private lemma mk₁_writeHead_moveLeft (out : List Symbol) :
    ((BiTape.mk₁ out).write (BiTape.mk₁ out).head).optionMove (some .left) = writeTape out := by
  cases out <;> rfl

variable (tm : SingleTapeTM Symbol)

/-- Embedding of a `tm`-configuration into an `onTailComputer tm`-configuration during the run
phase, carrying the preserved leading symbol `b`. -/
private def toRunCfg (b : Symbol) (cfg : tm.Cfg) : (onTailComputer tm).Cfg :=
  match cfg.state with
  | some q => ⟨some (Sum.inr (Sum.inl (q, b))), cfg.BiTape⟩
  | none => ⟨some (Sum.inr (Sum.inr (Sum.inl b))), cfg.BiTape⟩

/-- The embedding commutes with a step of the underlying machine. -/
private theorem map_toRunCfg_step (b : Symbol) (cfg : tm.Cfg) (hcfg : cfg.state.isSome) :
    Option.map (toRunCfg tm b) (tm.step cfg) = (onTailComputer tm).step (toRunCfg tm b cfg) := by
  cases cfg with | mk state BiTape => cases state with
    | none => simp at hcfg
    | some q =>
      simp only [step, toRunCfg, onTailComputer]
      generalize hM : tm.tr q BiTape.head = result
      obtain ⟨⟨wr, dir⟩, nextState⟩ := result
      cases nextState <;> (simp_all; rfl)

/-- The run phase: while `tm` runs from its initial to its halting configuration, the composed
machine runs from the (remembered-symbol) run state to the finishing state, in the same time. -/
private theorem run_relatesWithinSteps (b : Symbol) (rest out : List Symbol) (t : ℕ)
    (h : RelatesWithinSteps tm.TransitionRelation (tm.initCfg rest) (tm.haltCfg out) t) :
    RelatesWithinSteps (onTailComputer tm).TransitionRelation
      ⟨some (Sum.inr (Sum.inl (tm.q₀, b))), BiTape.mk₁ rest⟩
      ⟨some (Sum.inr (Sum.inr (Sum.inl b))), BiTape.mk₁ out⟩
      t := by
  have hhom : ∀ x y : tm.Cfg, tm.TransitionRelation x y →
      (onTailComputer tm).TransitionRelation (toRunCfg tm b x) (toRunCfg tm b y) := by
    intro x y hxy
    have hx : x.state.isSome := by
      simp only [TransitionRelation, step] at hxy
      cases x with | mk st _ => cases st <;> simp_all
    have h1 := map_toRunCfg_step tm b x hx
    rw [hxy, Option.map_some] at h1
    exact h1.symm
  have hmap := RelatesWithinSteps.map (toRunCfg tm b) hhom h
  simpa only [toRunCfg, initCfg, haltCfg] using hmap

/-- The start step on a nonempty input: erase and remember the head, positioning to run `tm`. -/
private lemma onTail_start (b : Symbol) (rest : List Symbol) :
    (onTailComputer tm).TransitionRelation
      (initCfg (onTailComputer tm) (b :: rest))
      ⟨some (Sum.inr (Sum.inl (tm.q₀, b))), BiTape.mk₁ rest⟩ := by
  simp only [TransitionRelation, initCfg, onTailComputer, SingleTapeTM.step, mk₁_cons_head,
    mk₁_erase_moveRight]

/-- The start step on the empty input: halt immediately with empty output. -/
private lemma onTail_start_nil :
    (onTailComputer tm).TransitionRelation
      (initCfg (onTailComputer tm) [])
      (haltCfg (onTailComputer tm) []) := by
  simp only [TransitionRelation, initCfg, haltCfg, onTailComputer, SingleTapeTM.step, mk₁_nil_head,
    mk₁_nil_noop]

/-- The first finishing step: rewrite the head and move left onto the blank cell. -/
private lemma onTail_finishRead (b : Symbol) (out : List Symbol) :
    (onTailComputer tm).TransitionRelation
      ⟨some (Sum.inr (Sum.inr (Sum.inl b))), BiTape.mk₁ out⟩
      ⟨some (Sum.inr (Sum.inr (Sum.inr b))), writeTape out⟩ := by
  simp only [TransitionRelation, onTailComputer, SingleTapeTM.step, mk₁_writeHead_moveLeft]

/-- The second finishing step: write the remembered symbol and halt, prepending it to the output. -/
private lemma onTail_finishWrite (b : Symbol) (out : List Symbol) :
    (onTailComputer tm).TransitionRelation
      ⟨some (Sum.inr (Sum.inr (Sum.inr b))), writeTape out⟩
      (haltCfg (onTailComputer tm) (b :: out)) := by
  simp only [TransitionRelation, haltCfg, onTailComputer, SingleTapeTM.step, writeTape_lastWrite]

/-- Running a polynomial-time machine on the tail of the input is polynomial-time. -/
noncomputable def PolyTimeComputable.onTail {f : List Symbol → List Symbol}
    (h : PolyTimeComputable f) : PolyTimeComputable (onTailFun f) where
  tm := onTailComputer h.normalize.tm
  timeBound n := h.normalize.timeBound n + 3
  poly := h.normalize.poly + C 3
  bounds n := by
    simp only [eval_add, eval_C]
    exact Nat.add_le_add_right (h.normalize.bounds n) 3
  outputsFunInTime a := by
    simp only [OutputsWithinTime]
    cases a with
    | nil =>
      exact (RelatesWithinSteps.single (onTail_start_nil h.normalize.tm)).of_le (by omega)
    | cons b rest =>
      have hrun := run_relatesWithinSteps h.normalize.tm b rest (f rest) _
        (h.normalize.outputsFunInTime rest)
      have hchain := (RelatesWithinSteps.single (onTail_start h.normalize.tm b rest)).trans
        (hrun.trans ((RelatesWithinSteps.single (onTail_finishRead h.normalize.tm b (f rest))).trans
          (RelatesWithinSteps.single (onTail_finishWrite h.normalize.tm b (f rest)))))
      refine hchain.of_le ?_
      have hmono := h.monotone_normalize (Nat.le_succ rest.length)
      simp only [List.length_cons, Nat.succ_eq_add_one] at *
      omega

end OnTail

end SingleTapeTM

end Cslib.Turing
