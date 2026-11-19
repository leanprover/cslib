/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Devon Tuma
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

`OracleComp.interpret` runs a program in any monad by answering each call with a handler in that
monad. Into `PMF` it gives the output distribution of a program with a memoryless probabilistic
oracle; into `StateT State m` it threads a hidden oracle state through the calls; into another
`OracleComp` it replaces each call by a program over another interface, as needed for reductions;
and into a writer monad it logs the queries. It is `PFunctor.FreeM.liftM`, so it preserves
sequencing, and interpretations compose.

Neither termination nor a bound on the number of queries asserts computational efficiency.
Computational efficiency requires a separate machine-realizability predicate. Unbounded loops and
nontermination are outside this language; bounded iteration uses Lean recursion.

## References

This is the design of Devon Tuma, Quang Dao, and collaborators'
[VCVio](https://github.com/Verified-zkEVM/VCVio): `OracleSpec`, `OracleComp`, and `unifSpec`
are their definitions, and `OracleComp.interpret` is their `simulateQ`.
-/

@[expose] public section

namespace Cslib

open Probability

universe u v w

/-- An oracle specification: the response type of each query in `ι`. -/
abbrev OracleSpec (ι : Type u) := ι → Type v

/-- Terminating programs with typed oracle calls described by `spec`. -/
abbrev OracleComp {ι : Type u} (spec : OracleSpec.{u, v} ι) (α : Type v) :=
  (PFunctor.mk ι spec).FreeM α

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec.{u, v} ι} {α β State : Type v}

/-- Make one oracle call. Later queries may depend on the answer. -/
def query (q : ι) : OracleComp spec (spec q) := PFunctor.FreeM.lift (P := ⟨ι, spec⟩) q

section Interpret

variable {m : Type v → Type w} [Monad m]

/-- Run a program in the monad `m`, answering each oracle call with `oracle`. -/
def interpret (oracle : (q : ι) → m (spec q)) (program : OracleComp spec α) : m α :=
  program.liftM oracle

@[simp] theorem interpret_pure (oracle : (q : ι) → m (spec q)) (a : α) :
    interpret oracle (pure a) = pure a := rfl

variable [LawfulMonad m]

@[simp] theorem interpret_bind (oracle : (q : ι) → m (spec q))
    (program : OracleComp spec α) (next : α → OracleComp spec β) :
    interpret oracle (program >>= next) =
      interpret oracle program >>= fun a => interpret oracle (next a) :=
  PFunctor.FreeM.liftM_bind _ _ _

@[simp] theorem interpret_query (oracle : (q : ι) → m (spec q)) (q : ι) :
    interpret oracle (query q) = oracle q :=
  PFunctor.FreeM.liftM_lift _ _

@[simp] theorem interpret_map (oracle : (q : ι) → m (spec q)) (f : α → β)
    (program : OracleComp spec α) :
    interpret oracle (f <$> program) = f <$> interpret oracle program :=
  PFunctor.FreeM.liftM_map _ _ _

/-- Answering each call by itself leaves the program unchanged. -/
@[simp] theorem interpret_query_eq_self (program : OracleComp spec α) :
    interpret query program = program :=
  PFunctor.FreeM.liftM_lift_eq_self program

/-- Interpretations compose: interpreting a program whose calls were replaced by programs over
another interface is interpreting the original calls through the replacements. No fresh state is
introduced between calls. -/
theorem interpret_interpret {ι' : Type u} {spec' : OracleSpec.{u, v} ι'}
    (handler : (q : ι) → OracleComp spec' (spec q)) (oracle : (q : ι') → m (spec' q))
    (program : OracleComp spec α) :
    interpret oracle (interpret handler program) =
      interpret (fun q => interpret oracle (handler q)) program :=
  PFunctor.FreeM.liftM_comp _ _ _

/-- An oracle may consult a fixed private environment without changing it. Its stateful execution
agrees with interpreting the program against that environment. -/
theorem run_interpret_readOnly (oracle : (q : ι) → State → m (spec q))
    (program : OracleComp spec α) (s : State) :
    (interpret (m := StateT State m) (fun q s => (fun a => (a, s)) <$> oracle q s) program).run s =
      (fun a => (a, s)) <$> interpret (fun q => oracle q s) program := by
  induction program using PFunctor.FreeM.induction generalizing s with
  | pure a => simp
  | lift_bind q cont ih =>
    change (interpret (m := StateT State m) _ (query q >>= cont)).run s =
      (fun a => (a, s)) <$> interpret _ (query q >>= cont)
    simp only [interpret_bind, interpret_query, StateT.run_bind]
    simp only [StateT.run, bind_map_left, map_bind]
    exact bind_congr fun a => ih a s

/-- Adding an untouched private state to a memoryless oracle does not change the result. -/
theorem run_interpret_stateless (oracle : (q : ι) → m (spec q))
    (program : OracleComp spec α) (s : State) :
    (interpret (m := StateT State m) (fun q s => (fun a => (a, s)) <$> oracle q) program).run s =
      (fun a => (a, s)) <$> interpret oracle program :=
  run_interpret_readOnly (fun q _ => oracle q) program s

end Interpret

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
  OracleComp.interpret unifOracle program

@[simp] theorem eval_pure (a : α) : eval (pure a) = PMF.pure a := rfl

@[simp] theorem eval_bind (program : ProbComp α) (next : α → ProbComp β) :
    eval (program >>= next) = (eval program).bind (fun a => eval (next a)) :=
  OracleComp.interpret_bind _ _ _

@[simp] theorem eval_map (f : α → β) (program : ProbComp α) :
    eval (f <$> program) = (eval program).map f := OracleComp.interpret_map _ _ _

@[simp] theorem eval_unifFin (n : ℕ) :
    eval (unifFin n) = PMF.uniformOfFintype (Fin (n + 1)) := by
  rw [eval, unifFin, OracleComp.interpret_query, unifOracle]

/-- Sampling through an enumeration is uniform on the type. -/
@[simp] theorem eval_uniform (α : Type) [Fintype α] [Nonempty α] :
    eval (uniform α) = PMF.uniformOfFintype α := by
  rw [uniform, eval_map, eval_unifFin]
  exact PMF.uniformOfFintype_map_equiv
    ((finCongr (Nat.sub_add_cancel Fintype.card_pos)).trans (Fintype.equivFin α).symm)

end ProbComp

end Cslib
