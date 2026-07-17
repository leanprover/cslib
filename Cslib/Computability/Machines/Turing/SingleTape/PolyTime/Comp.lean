/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Pim Spelier, Daan van Gent
-/

module

public import Cslib.Computability.Machines.Turing.SingleTape.Deterministic

/-!
# The composition machine

The Turing machine `compComputer tm1 tm2` running `tm1` and then `tm2`, together with the witnesses
that the composition of `TimeComputable`/`PolyTimeComputable` functions is again computable in the
respective sense.

* `TimeComputable.comp`, `PolyTimeComputable.comp`: composition with a monotonicity side-condition
  on the second machine's time bound.
* `PolyTimeComputable.comp'`: composition with no side-condition, obtained by first `normalize`-ing
  the second machine (defined in `Deterministic`).
-/

@[expose] public section

open Relation

namespace Cslib.Turing

open BiTape StackTape
open _root_.Turing

namespace SingleTapeTM

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

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

open Polynomial

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

/-- The composition of two polynomial-time computable functions is polynomial-time computable,
with no monotonicity side-condition (unlike `comp`, which this specializes via `normalize`). -/
noncomputable def PolyTimeComputable.comp' {f g : List Symbol → List Symbol}
    (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
    PolyTimeComputable (g ∘ f) :=
  hf.comp hg.normalize hg.monotone_normalize

end SingleTapeTM

end Cslib.Turing
