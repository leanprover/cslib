/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Cslib.Algorithms.Lean.Query.UpperBound
import Std.Tactic.Do

/-! # Monadic Map-Sum Demo

A minimal demonstration of `UpperBoundT` with a non-trivial base monad.

`mapSum f xs` applies the monadic function `f` to each element of `xs`
and accumulates the results into a `StateM Int` counter.

Since `f` is called exactly once per element, `mapSum` runs in `xs.length` queries.
This is expressed via `UpperBoundT (n := StateM Int)`, which instruments the query with tick-counting
while preserving the `StateM Int` layer used for accumulation.
-/

open Std.Do Cslib.Query

set_option mvcgen.warning false

public section

namespace Cslib.Query

/-- Apply a monadic function to each element of a list and accumulate the results in `StateM Int`.
    The function `f` is the query whose invocations we measure. -/
@[expose] def mapSum [Monad m] [MonadLiftT (StateM Int) m]
    (f : Int → m Int) : List Int → m Unit
  | [] => pure ()
  | x :: xs => do
    let y ← f x
    (modify (· + y) : StateM Int Unit)
    mapSum f xs

/-- `mapSum` calls the function exactly once per element. -/
public theorem mapSum_runsInT :
    UpperBoundT (n := StateM Int) mapSum (fun xs => xs.length) := by
  intro query hquery xs
  induction xs with
  | nil => exact TimeT.Costs.pure ()
  | cons x xs ih =>
    simp only [List.length]; rw [Nat.add_comm]
    have ih : TimeT.Costs (mapSum query xs) xs.length := ih
    exact TimeT.Costs.bind (hquery x) (fun y => by
      have := TimeT.Costs.bind
        (TimeT.Costs.monadLift (modify (· + y) : StateM Int Unit) (fun P => by mvcgen))
        (fun _ => ih)
      rwa [Nat.zero_add] at this)

/-- `mapSum` with a state-preserving monadic function accumulates `(xs.map g).sum`.

    The predicate family `pre c` captures "the Int state is c" within the
    abstract postcondition shape `ps`. The hypotheses `hf` and `h_modify`
    assert that `f` preserves this predicate and the lifted `modify` transitions it. -/
public theorem mapSum_spec_general [Monad m] [MonadLiftT (StateM Int) m] [WPMonad m ps]
    (f : Int → m Int) (g : Int → Int)
    (pre : Int → Assertion ps)
    (hf : ∀ x c, ⦃pre c⦄ f x ⦃⇓ y => pre c ∧ ⌜y = g x⌝⦄)
    (h_modify : ∀ v c, ⦃pre c⦄
      (MonadLiftT.monadLift (modify (· + v) : StateM Int Unit) : m Unit)
      ⦃⇓ _ => pre (c + v)⦄)
    (xs : List Int) :
    ∀ c, ⦃pre c⦄ mapSum f xs ⦃⇓ _ => pre (c + (xs.map g).sum)⦄ := by
  induction xs with
  | nil =>
    intro c; simp only [mapSum]; mvcgen; simp_all
  | cons x xs ih =>
    intro c; dsimp only [mapSum]; mvcgen [hf, h_modify, ih]
    subst_vars; simp only [List.map_cons, List.sum_cons, ← Int.add_assoc]; exact .rfl

/-- `mapSum` with a pure function accumulates `(xs.map f).sum`.
    Special case of `mapSum_spec_general`. -/
public theorem mapSum_spec (f : Int → Int) (xs : List Int) :
    ∀ c, ⦃fun n => ⌜n = c⌝⦄
      mapSum (m := StateM Int) (fun a => pure (f a)) xs
    ⦃⇓ _ => fun n => ⌜n = c + (xs.map f).sum⌝⦄ :=
  mapSum_spec_general (m := StateM Int) (fun a => pure (f a)) f
    (fun c => (fun n => ⌜n = c⌝ : Assertion _))
    (by intro x c; mvcgen)
    (by intro v c; mvcgen; subst_vars; rfl)
    xs

/-- `mapSum` with a tick-instrumented pure function still accumulates `(xs.map f).sum`.
    Special case of `mapSum_spec_general`. -/
public theorem mapSum_spec_tick (f : Int → Int) (xs : List Int) :
    ∀ c, ⦃fun _ => fun n => ⌜n = c⌝⦄
      mapSum (m := TimeT (StateM Int)) (TimeT.counted f) xs
    ⦃⇓ _ => fun _ => fun n => ⌜n = c + (xs.map f).sum⌝⦄ :=
  mapSum_spec_general (m := TimeT (StateM Int)) (TimeT.counted f) f
    (fun c => (fun _ => fun n => ⌜n = c⌝ : Assertion _))
    (by intro x c; simp only [TimeT.counted]; mvcgen)
    (by intro v c; simp only [Triple]; mvcgen
        simp_all [TimeT.wp_monadLift, Std.Do.WP.modifyGet_StateT])
    xs

end Cslib.Query

end -- public section
