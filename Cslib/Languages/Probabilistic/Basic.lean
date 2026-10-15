/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Foundations.Data.PFunctor.Free
public import Cslib.Probability.PMF

/-!
# Probabilistic programs with oracles

`OracleComp spec α` is a terminating program with typed oracle calls described by the
specification `spec : OracleSpec ι`, which gives the response type `spec q` of each query `q : ι`.
A specification is the data of a polynomial functor, and programs are its `PFunctor.FreeM`, so they
use ordinary `do` notation, and a program lives in the universe of its queries, responses, and
result.

Randomness is not a separate effect. `unifSpec` is the interface answering `n` with a uniform
element of `Fin (n + 1)`, and `ProbComp` is `OracleComp unifSpec`. Any other distribution is
reached by interpreting an interface with that distribution, so the base language has no
primitive beyond uniform choice from a finite range.

`OracleComp.eval` interprets a program with a memoryless oracle into `PMF`, `OracleComp.runState`
threads a hidden state through calls, and `OracleComp.simulate` replaces each call by a program
over another interface, as needed for reductions. All three are `PFunctor.FreeM.liftM`, so they
preserve sequencing.

Neither termination nor a bound on the number of queries asserts computational efficiency.
Computational efficiency requires a separate machine-realizability predicate. Unbounded loops and
nontermination are outside this language; bounded iteration uses Lean recursion.

## References

This is the design of Devon Tuma, Quang Dao, and collaborators'
[VCVio](https://github.com/Verified-zkEVM/VCVio): `OracleSpec`, `OracleComp`, and `unifSpec`
are their definitions.
-/

@[expose] public section

namespace Cslib

open Probability

universe u v

/-- An oracle specification: the response type of each query in `ι`. -/
abbrev OracleSpec (ι : Type u) := ι → Type v

/-- Terminating programs with typed oracle calls described by `spec`. -/
abbrev OracleComp {ι : Type u} (spec : OracleSpec.{u, v} ι) (α : Type v) :=
  (PFunctor.mk ι spec).FreeM α

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec.{u, v} ι} {α β State : Type v}

/-- Make one oracle call. Later queries may depend on the answer. -/
def query (q : ι) : OracleComp spec (spec q) := PFunctor.FreeM.lift (P := ⟨ι, spec⟩) q

/-- The output distribution of a program with a memoryless probabilistic oracle. -/
noncomputable def eval (oracle : (q : ι) → PMF (spec q)) (program : OracleComp spec α) :
    PMF α :=
  program.liftM oracle

@[simp] theorem eval_pure (oracle : (q : ι) → PMF (spec q)) (a : α) :
    eval oracle (pure a) = PMF.pure a := rfl

@[simp] theorem eval_bind (oracle : (q : ι) → PMF (spec q))
    (program : OracleComp spec α) (next : α → OracleComp spec β) :
    eval oracle (program >>= next) = (eval oracle program).bind (fun a => eval oracle (next a)) :=
  PFunctor.FreeM.liftM_bind _ _ _

@[simp] theorem eval_query (oracle : (q : ι) → PMF (spec q)) (q : ι) :
    eval oracle (query q) = oracle q :=
  PFunctor.FreeM.liftM_lift _ _

@[simp] theorem eval_map (oracle : (q : ι) → PMF (spec q)) (f : α → β)
    (program : OracleComp spec α) :
    eval oracle (f <$> program) = (eval oracle program).map f :=
  PFunctor.FreeM.liftM_map _ _ _

/-- Run a program against a stateful oracle, returning its result and the final oracle state. -/
noncomputable def runState (oracle : (q : ι) → StateT State PMF (spec q))
    (program : OracleComp spec α) : StateT State PMF α :=
  program.liftM oracle

@[simp] theorem runState_pure (oracle : (q : ι) → StateT State PMF (spec q))
    (a : α) (s : State) : runState oracle (pure a) s = PMF.pure (a, s) := rfl

@[simp] theorem runState_bind (oracle : (q : ι) → StateT State PMF (spec q))
    (program : OracleComp spec α) (next : α → OracleComp spec β) (s : State) :
    runState oracle (program >>= next) s =
      (runState oracle program s).bind (fun (a, s') => runState oracle (next a) s') := by
  unfold runState
  rw [PFunctor.FreeM.liftM_bind]
  rfl

@[simp] theorem runState_query (oracle : (q : ι) → StateT State PMF (spec q))
    (q : ι) (s : State) : runState oracle (query q) s = oracle q s := by
  rw [runState, query, PFunctor.FreeM.liftM_lift]

@[simp] theorem runState_map (oracle : (q : ι) → StateT State PMF (spec q))
    (f : α → β) (program : OracleComp spec α) (s : State) :
    runState oracle (f <$> program) s =
      (runState oracle program s).map (fun (a, s') => (f a, s')) := by
  unfold runState
  rw [PFunctor.FreeM.liftM_map]
  rfl

/-- An oracle may consult a fixed private environment without changing it. Its stateful execution
agrees with evaluating the program against that environment. -/
theorem runState_readOnly (oracle : (q : ι) → State → PMF (spec q))
    (program : OracleComp spec α) (s : State) :
    runState (fun q s => (oracle q s).map (fun a => (a, s))) program s =
      (eval (fun q => oracle q s) program).map (fun a => (a, s)) := by
  induction program using PFunctor.FreeM.induction generalizing s with
  | pure a => simp [PMF.pure_map]
  | lift_bind q cont ih =>
    change runState _ (query q >>= cont) s = (eval _ (query q >>= cont)).map _
    simp only [runState_bind, runState_query, eval_bind, eval_query, PMF.bind_map, PMF.map_bind,
      Function.comp_def]
    congr 1
    funext a
    exact ih a s

/-- Adding an untouched private state to a memoryless oracle preserves the output distribution. -/
theorem runState_stateless (oracle : (q : ι) → PMF (spec q))
    (program : OracleComp spec α) (s : State) :
    runState (fun q s => (oracle q).map (fun a => (a, s))) program s =
      (eval oracle program).map (fun a => (a, s)) :=
  runState_readOnly (fun q _ => oracle q) program s

section Simulate

variable {ι' ι'' : Type u} {spec' : OracleSpec.{u, v} ι'} {spec'' : OracleSpec.{u, v} ι''}

/-- Replace each oracle call with a program over another interface. -/
def simulate (handler : (q : ι) → OracleComp spec' (spec q))
    (program : OracleComp spec α) : OracleComp spec' α :=
  program.liftM handler

@[simp] theorem simulate_pure (handler : (q : ι) → OracleComp spec' (spec q)) (a : α) :
    simulate handler (pure a) = pure a := rfl

@[simp] theorem simulate_bind (handler : (q : ι) → OracleComp spec' (spec q))
    (program : OracleComp spec α) (next : α → OracleComp spec β) :
    simulate handler (program >>= next) =
      (simulate handler program >>= fun a => simulate handler (next a)) :=
  PFunctor.FreeM.liftM_bind _ _ _

@[simp] theorem simulate_query (handler : (q : ι) → OracleComp spec' (spec q))
    (q : ι) : simulate handler (query q) = handler q :=
  PFunctor.FreeM.liftM_lift _ _

@[simp] theorem simulate_map (handler : (q : ι) → OracleComp spec' (spec q))
    (f : α → β) (program : OracleComp spec α) :
    simulate handler (f <$> program) = f <$> simulate handler program :=
  PFunctor.FreeM.liftM_map _ _ _

/-- Replacing each call by itself leaves the program unchanged. -/
@[simp] theorem simulate_id (program : OracleComp spec α) : simulate query program = program :=
  PFunctor.FreeM.liftM_lift_eq_self program

/-- Oracle substitutions compose without introducing fresh state between calls. -/
theorem simulate_simulate (first : (q : ι) → OracleComp spec' (spec q))
    (second : (q : ι') → OracleComp spec'' (spec' q)) (program : OracleComp spec α) :
    simulate second (simulate first program) =
      simulate (fun q => simulate second (first q)) program :=
  PFunctor.FreeM.liftM_comp _ _ _

/-- Simulating calls and then evaluating agrees with evaluating with the simulated oracle. -/
theorem eval_simulate (handler : (q : ι) → OracleComp spec' (spec q))
    (oracle : (q : ι') → PMF (spec' q)) (program : OracleComp spec α) :
    eval oracle (simulate handler program) = eval (fun q => eval oracle (handler q)) program :=
  PFunctor.FreeM.liftM_comp _ _ _

/-- Oracle substitution also preserves interactions with a stateful handler, including its final
private state. The state is shared across all simulated calls. -/
theorem runState_simulate (handler : (q : ι) → OracleComp spec' (spec q))
    (oracle : (q : ι') → StateT State PMF (spec' q))
    (program : OracleComp spec α) (s : State) :
    runState oracle (simulate handler program) s =
      runState (fun q => runState oracle (handler q)) program s :=
  congrFun (PFunctor.FreeM.liftM_comp _ _ _) s

end Simulate

end OracleComp

/-- The uniform sampling interface: the query `n` is answered by a uniform element of
`Fin (n + 1)`. -/
abbrev unifSpec : OracleSpec ℕ := fun n => Fin (n + 1)

/-- Probabilistic programs whose only randomness is uniform choice from a finite range. -/
abbrev ProbComp (α : Type) := OracleComp unifSpec α

namespace ProbComp

variable {α β : Type}

/-- Draw a uniform element of `Fin (n + 1)`. -/
def unifFin (n : ℕ) : ProbComp (Fin (n + 1)) := OracleComp.query (spec := unifSpec) n

/-- Uniform sampling from a nonempty finite type, through an enumeration of it. -/
noncomputable def uniform (α : Type) [Fintype α] [Nonempty α] : ProbComp α :=
  (fun i => (Fintype.equivFin α).symm (Fin.cast (Nat.sub_add_cancel Fintype.card_pos) i)) <$>
    unifFin (Fintype.card α - 1)

/-- The oracle answering each query uniformly. -/
noncomputable def unifOracle (n : ℕ) : PMF (Fin (n + 1)) := PMF.uniformOfFintype (Fin (n + 1))

/-- The distribution denoted by a closed probabilistic program. -/
noncomputable def eval (program : ProbComp α) : PMF α :=
  OracleComp.eval unifOracle program

@[simp] theorem eval_pure (a : α) : eval (pure a) = PMF.pure a := rfl

@[simp] theorem eval_bind (program : ProbComp α) (next : α → ProbComp β) :
    eval (program >>= next) = (eval program).bind (fun a => eval (next a)) :=
  OracleComp.eval_bind _ _ _

@[simp] theorem eval_map (f : α → β) (program : ProbComp α) :
    eval (f <$> program) = (eval program).map f := OracleComp.eval_map _ _ _

@[simp] theorem eval_unifFin (n : ℕ) :
    eval (unifFin n) = PMF.uniformOfFintype (Fin (n + 1)) := by
  rw [eval, unifFin, OracleComp.eval_query, unifOracle]

/-- Sampling through an enumeration is uniform on the type. -/
@[simp] theorem eval_uniform (α : Type) [Fintype α] [Nonempty α] :
    eval (uniform α) = PMF.uniformOfFintype α := by
  rw [uniform, eval_map, eval_unifFin]
  exact PMF.uniformOfFintype_map_equiv
    ((finCongr (Nat.sub_add_cancel Fintype.card_pos)).trans (Fintype.equivFin α).symm)

end ProbComp

end Cslib
