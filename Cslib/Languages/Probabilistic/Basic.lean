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

`OracleComp Query Response α` is a terminating probabilistic program with typed oracle calls.
It reuses `PFunctor.FreeM`, so programs use ordinary `do` notation. An oracle can return a different
type for each query; sum types describe multiple interfaces. `ProbComp` has no oracle calls.

`OracleComp.eval` interprets a program using a memoryless oracle, while `OracleComp.runState`
threads a hidden state through calls. `OracleComp.simulate` replaces each call by another program,
as needed for reductions. These interpreters preserve sequencing.

Sampling arbitrary PMFs and computing arbitrary Lean functions is allowed at the specification
level. Neither termination nor a bound on the number of queries asserts computational efficiency.
Computational efficiency requires a separate machine-realizability predicate.
Unbounded loops and nontermination are outside this language; bounded iteration uses Lean recursion.

## References

The separation of oracle syntax and interpretation is also used in Devon Tuma, Quang Dao, and
collaborators' [VCVio](https://github.com/Verified-zkEVM/VCVio), whose oracle computations likewise
use a polynomial free monad.
-/

@[expose] public section

namespace Cslib

open Probability

universe u

/-- The effects of a probabilistic program: sampling and an external query. -/
inductive ProbEffect (Query : Type u) : Type (u + 1) where
  /-- Draw a value from a specified distribution. -/
  | sample {α : Type u} (distribution : PMF α) : ProbEffect Query
  /-- Ask the external oracle a question. -/
  | query (q : Query) : ProbEffect Query

/-- The answer type of a sampling operation or external query. -/
abbrev ProbEffect.response {Query : Type u} (Response : Query → Type u) : ProbEffect Query → Type u
  | .sample (α := α) _ => α
  | .query q => Response q

/-- The polynomial signature of sampling operations and external queries. -/
abbrev ProbEffect.signature (Query : Type u) (Response : Query → Type u) : PFunctor where
  A := ProbEffect Query
  B := ProbEffect.response Response

/-- Terminating probabilistic programs with a typed oracle interface.
Queries, responses, sampled values, and results share one universe. Sampling arbitrary types in
that universe places the program type in the next universe. -/
abbrev OracleComp (Query : Type u) (Response : Query → Type u) (α : Type u) :=
  PFunctor.FreeM (ProbEffect.signature Query Response) α

/-- Probabilistic programs with no external oracle. -/
abbrev ProbComp (α : Type u) := OracleComp PEmpty (fun _ => PEmpty) α

namespace OracleComp

variable {Query : Type u} {Response : Query → Type u} {α β State : Type u}

/-- Sample from a distribution. This operation alone carries no efficiency guarantee. -/
def sample (p : PMF α) : OracleComp Query Response α :=
  PFunctor.FreeM.lift (P := ProbEffect.signature Query Response) (.sample p)

/-- Uniform sampling from a nonempty finite type. -/
noncomputable def uniform (α : Type u) [Fintype α] [Nonempty α] :
    OracleComp Query Response α := sample (PMF.uniformOfFintype α)

/-- Make one oracle call. Later queries may depend on the answer. -/
def query (q : Query) : OracleComp Query Response (Response q) :=
  PFunctor.FreeM.lift (P := ProbEffect.signature Query Response) (.query q)

/-- Interpret individual effects using a memoryless oracle. -/
noncomputable def evalEffect (oracle : (q : Query) → PMF (Response q)) :
    (op : ProbEffect Query) → PMF (op.response Response)
  | .sample p => p
  | .query q => oracle q

/-- The output distribution of a program with a memoryless probabilistic oracle. -/
noncomputable def eval (oracle : (q : Query) → PMF (Response q))
    (program : OracleComp Query Response α) : PMF α :=
  program.liftM (evalEffect oracle)

@[simp] theorem eval_pure (oracle : (q : Query) → PMF (Response q)) (a : α) :
    eval oracle (pure a) = PMF.pure a := rfl

@[simp] theorem eval_bind (oracle : (q : Query) → PMF (Response q))
    (program : OracleComp Query Response α) (next : α → OracleComp Query Response β) :
    eval oracle (program >>= next) = (eval oracle program).bind (fun a => eval oracle (next a)) :=
  PFunctor.FreeM.liftM_bind _ _ _

@[simp] theorem eval_sample (oracle : (q : Query) → PMF (Response q)) (p : PMF α) :
    eval oracle (sample p) = p := by
  rw [eval, sample, PFunctor.FreeM.liftM_lift]
  rfl

@[simp] theorem eval_query (oracle : (q : Query) → PMF (Response q)) (q : Query) :
    eval oracle (query q) = oracle q := by
  rw [eval, query, PFunctor.FreeM.liftM_lift]
  rfl

@[simp] theorem eval_map (oracle : (q : Query) → PMF (Response q)) (f : α → β)
    (program : OracleComp Query Response α) :
    eval oracle (f <$> program) = (eval oracle program).map f :=
  PFunctor.FreeM.liftM_map _ _ _

/-- Handle effects while keeping the oracle's private state. Sampling does not change that state. -/
noncomputable def stateEffect (oracle : (q : Query) → StateT State PMF (Response q)) :
    (op : ProbEffect Query) → StateT State PMF (op.response Response)
  | .sample p => fun s => p.map (fun a => (a, s))
  | .query q => oracle q

/-- Run a program against a stateful oracle, returning its result and the final oracle state. -/
noncomputable def runState (oracle : (q : Query) → StateT State PMF (Response q))
    (program : OracleComp Query Response α) : StateT State PMF α :=
  program.liftM (stateEffect oracle)

@[simp] theorem runState_pure (oracle : (q : Query) → StateT State PMF (Response q))
    (a : α) (s : State) : runState oracle (pure a) s = PMF.pure (a, s) := rfl

@[simp] theorem runState_bind (oracle : (q : Query) → StateT State PMF (Response q))
    (program : OracleComp Query Response α) (next : α → OracleComp Query Response β) (s : State) :
    runState oracle (program >>= next) s =
      (runState oracle program s).bind (fun (a, s') => runState oracle (next a) s') := by
  unfold runState
  rw [PFunctor.FreeM.liftM_bind]
  rfl

@[simp] theorem runState_sample (oracle : (q : Query) → StateT State PMF (Response q))
    (p : PMF α) (s : State) :
    runState oracle (sample p) s = p.map (fun a => (a, s)) := by
  rw [runState, sample, PFunctor.FreeM.liftM_lift]
  rfl

@[simp] theorem runState_query (oracle : (q : Query) → StateT State PMF (Response q))
    (q : Query) (s : State) : runState oracle (query q) s = oracle q s := by
  rw [runState, query, PFunctor.FreeM.liftM_lift]
  rfl

theorem runState_sample_bind (oracle : (q : Query) → StateT State PMF (Response q))
    (p : PMF α) (next : α → OracleComp Query Response β) (s : State) :
    runState oracle (sample p >>= next) s = p.bind (fun a => runState oracle (next a) s) := by
  simp [PMF.bind_map, Function.comp_def]

@[simp] theorem runState_map (oracle : (q : Query) → StateT State PMF (Response q))
    (f : α → β) (program : OracleComp Query Response α) (s : State) :
    runState oracle (f <$> program) s =
      (runState oracle program s).map (fun (a, s') => (f a, s')) := by
  unfold runState
  rw [PFunctor.FreeM.liftM_map]
  rfl

/-- An oracle may consult a fixed private environment without changing it. Its stateful execution
agrees with evaluating the program against that environment. -/
theorem runState_readOnly (oracle : (q : Query) → State → PMF (Response q))
    (program : OracleComp Query Response α) (s : State) :
    runState (fun q s => (oracle q s).map (fun a => (a, s))) program s =
      (eval (fun q => oracle q s) program).map (fun a => (a, s)) := by
  induction program using PFunctor.FreeM.induction generalizing s with
  | pure a => simp [PMF.pure_map]
  | lift_bind op cont ih =>
    cases op with
    | sample p =>
      change runState _ (sample p >>= cont) s = (eval _ (sample p >>= cont)).map _
      simp only [runState_sample_bind, eval_bind, eval_sample, PMF.map_bind]
      congr 1
      funext a
      exact ih a s
    | query q =>
      change runState _ (query q >>= cont) s = (eval _ (query q >>= cont)).map _
      simp only [runState_bind, runState_query, eval_bind, eval_query,
        PMF.bind_map, PMF.map_bind, Function.comp_def]
      congr 1
      funext a
      exact ih a s

/-- Adding an untouched private state to a memoryless oracle preserves the output distribution. -/
theorem runState_stateless (oracle : (q : Query) → PMF (Response q))
    (program : OracleComp Query Response α) (s : State) :
    runState (fun q s => (oracle q).map (fun a => (a, s))) program s =
      (eval oracle program).map (fun a => (a, s)) :=
  runState_readOnly (fun q _ => oracle q) program s

/-- Replace each oracle call with a program over another interface. -/
def simulate {Query' : Type u} {Response' : Query' → Type u}
    (handler : (q : Query) → OracleComp Query' Response' (Response q))
    (program : OracleComp Query Response α) : OracleComp Query' Response' α :=
  PFunctor.FreeM.liftM (P := ProbEffect.signature Query Response) (fun op => match op with
    | .sample p => sample p
    | .query q => handler q) program

@[simp] theorem simulate_pure {Query' : Type u} {Response' : Query' → Type u}
    (handler : (q : Query) → OracleComp Query' Response' (Response q)) (a : α) :
    simulate handler (pure a) = pure a := rfl

@[simp] theorem simulate_bind {Query' : Type u} {Response' : Query' → Type u}
    (handler : (q : Query) → OracleComp Query' Response' (Response q))
    (program : OracleComp Query Response α) (next : α → OracleComp Query Response β) :
    simulate handler (program >>= next) =
      (simulate handler program >>= fun a => simulate handler (next a)) :=
  PFunctor.FreeM.liftM_bind _ _ _

@[simp] theorem simulate_sample {Query' : Type u} {Response' : Query' → Type u}
    (handler : (q : Query) → OracleComp Query' Response' (Response q)) (p : PMF α) :
    simulate handler (sample p) = sample p := by
  rw [simulate, sample, PFunctor.FreeM.liftM_lift]

@[simp] theorem simulate_query {Query' : Type u} {Response' : Query' → Type u}
    (handler : (q : Query) → OracleComp Query' Response' (Response q)) (q : Query) :
    simulate handler (query q) = handler q := by
  rw [simulate, query, PFunctor.FreeM.liftM_lift]

@[simp] theorem simulate_map {Query' : Type u} {Response' : Query' → Type u}
    (handler : (q : Query) → OracleComp Query' Response' (Response q)) (f : α → β)
    (program : OracleComp Query Response α) :
    simulate handler (f <$> program) = f <$> simulate handler program :=
  PFunctor.FreeM.liftM_map _ _ _

/-- Replacing each call by itself leaves the program unchanged. -/
@[simp] theorem simulate_id (program : OracleComp Query Response α) :
    simulate query program = program := by
  unfold simulate
  convert PFunctor.FreeM.liftM_lift_eq_self program using 1
  congr 1
  funext op
  cases op <;> rfl

/-- Oracle substitutions compose without introducing fresh state between calls. -/
theorem simulate_simulate {Query' Query'' : Type u} {Response' : Query' → Type u}
    {Response'' : Query'' → Type u}
    (first : (q : Query) → OracleComp Query' Response' (Response q))
    (second : (q : Query') → OracleComp Query'' Response'' (Response' q))
    (program : OracleComp Query Response α) :
    simulate second (simulate first program) =
      simulate (fun q => simulate second (first q)) program := by
  unfold simulate
  rw [PFunctor.FreeM.liftM_comp]
  congr 1
  funext op
  cases op with
  | sample p => exact simulate_sample second p
  | query q => rfl

/-- Simulating calls and then evaluating agrees with evaluating with the simulated oracle. -/
theorem eval_simulate {Query' : Type u} {Response' : Query' → Type u}
    (handler : (q : Query) → OracleComp Query' Response' (Response q))
    (oracle : (q : Query') → PMF (Response' q)) (program : OracleComp Query Response α) :
    eval oracle (simulate handler program) = eval (fun q => eval oracle (handler q)) program := by
  unfold simulate eval
  rw [PFunctor.FreeM.liftM_comp]
  congr 1
  funext op
  cases op with
  | sample p => exact eval_sample oracle p
  | query q => rfl

/-- Oracle substitution also preserves interactions with a stateful handler, including its final
private state. The state is shared across all simulated calls. -/
theorem runState_simulate {Query' : Type u} {Response' : Query' → Type u}
    (handler : (q : Query) → OracleComp Query' Response' (Response q))
    (oracle : (q : Query') → StateT State PMF (Response' q))
    (program : OracleComp Query Response α) (s : State) :
    runState oracle (simulate handler program) s =
      runState (fun q => runState oracle (handler q)) program s := by
  unfold simulate runState
  rw [PFunctor.FreeM.liftM_comp]
  apply congrFun
  congr 1
  funext op
  cases op with
  | sample p => funext s; exact runState_sample oracle p s
  | query q => rfl

end OracleComp

namespace ProbComp

variable {α β : Type u}

/-- The distribution denoted by a closed probabilistic program. -/
noncomputable def eval (program : ProbComp α) : PMF α :=
  OracleComp.eval (fun q => q.elim) program

@[simp] theorem eval_pure (a : α) : eval (pure a) = PMF.pure a := rfl

@[simp] theorem eval_bind (program : ProbComp α) (next : α → ProbComp β) :
    eval (program >>= next) = (eval program).bind (fun a => eval (next a)) :=
  OracleComp.eval_bind _ _ _

@[simp] theorem eval_sample (p : PMF α) : eval (OracleComp.sample p) = p :=
  OracleComp.eval_sample _ _

@[simp] theorem eval_map (f : α → β) (program : ProbComp α) :
    eval (f <$> program) = (eval program).map f := OracleComp.eval_map _ _ _

end ProbComp

end Cslib
