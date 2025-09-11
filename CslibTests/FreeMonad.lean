/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/
import Cslib.Foundations.Control.Monad.Free
import Mathlib.Tactic.Cases
import Cslib.Foundations.Control.Monad.Free.Fold
import Cslib.Languages.LambdaCalculus.LocallyNameless.Context
/-!
# Verified Interpreter using Free Monads

This file demonstrates building a verified interpreter for a simple effectful expression language
using free monads. The language supports arithmetic, variables, and three effects: state, errors,
and tracing.

## Key Ideas

**Separation of Syntax and Semantics**: Free monads let us separate *what* we want to do
(syntactic description of effectful computation) from *how* we want to do it (interpreting
and executing effects semantically).

**Effect Composability**: Multiple effects (state, errors, tracing) can be combined
cleanly using sum types without monad transformer complexity.

**Formal Verification**: The separation enables proving correctness by relating
the catamorphic interpreter to an operational semantics.

## Components

1. **Expression Language**: Simple arithmetic with variables
2. **Effect Definitions**: State, errors, and tracing as separate effect types
3. **Effect Combination**: Sum types to compose multiple effects
4. **Syntax Tree Construction**: Helper functions to build `FreeM` programs
5. **Interpreter**: Fold-based interpreter into a concrete monad
6. **Operational Semantics**: Big-step semantics as an inductive relation
7. **Correctness Proof**: Formal verification that interpreter matches semantics

This demonstrates how free monads enable building domain-specific languages with
clean separation between syntax and semantics, enabling multiple interpretations
(execution, analysis, verification) of the same programs.

## References

Based on "[Tutorial: A Verified Interpreter with Side Effects](https://tannerduve.github.io/blog/freer-monad/part4/)" demonstrating practical
applications of the mathematical theory developed in the core Free monad files.
-/

open FreeM

/-- Simple arithmetic expression language with integer values, variables, addition, and division.

Expressions can contain literal integers, variable references, binary addition, and binary division
(which may fail with division by zero). -/
inductive Expr where
  | val : Int → Expr
  | var : String → Expr
  | add : Expr → Expr → Expr
  | div : Expr → Expr → Expr

/-- Variable environment mapping variable names to integer values.
Uses the Context API for consistency with other language implementations in the library. -/
abbrev Env := LambdaCalculus.LocallyNameless.Context String Int

/-- State effect signature for environment manipulation.

Provides operations to get the current environment and put a new environment.
This demonstrates how to encode stateful computations as effect signatures. -/
inductive StateEff : Type → Type where
  | Get : StateEff Env
  | Put : Env → StateEff Unit

/-- Error effect signature for failure with string messages.

Allows computations to signal failure with descriptive error messages.
Useful for variable lookup failures and division by zero errors. -/
inductive ErrorEff : Type → Type where
  | Fail : String → ErrorEff Unit

/-- Trace effect signature for logging string messages.

Enables computations to emit log messages for debugging or audit purposes
without affecting the main computation result. -/
inductive TraceEff : Type → Type where
  | Log : String → TraceEff Unit

/-- Binary sum of effect signatures.

Combines two effect signatures `F` and `G` into a single signature `F ⊕ G`.
This enables composing multiple effects in a single computation without
monad transformer complexity. -/
inductive FSum (F G : Type → Type) (α : Type) where
  | inl : F α → FSum F G α
  | inr : G α → FSum F G α

infixl:50 "⊕" => FSum

/-- Combined effect signature supporting state, errors, and tracing.

Demonstrates how multiple effect signatures can be composed using sum types.
Computations of type `FreeM Eff α` can perform all three kinds of effects. -/
abbrev Eff := StateEff ⊕ (ErrorEff ⊕ TraceEff)

/-- Get the current environment from state. -/
def getEnv : FreeM Eff Env :=
  lift (FSum.inl StateEff.Get)

/-- Set the environment state to the given value. -/
def putEnv (e : Env) : FreeM Eff Unit :=
  lift (FSum.inl (StateEff.Put e))

/-- Signal computation failure with the given error message. -/
def fail (msg : String) : FreeM Eff Unit :=
  lift (FSum.inr (FSum.inl (ErrorEff.Fail msg)))

/-- Emit a log message to the trace. -/
def log (msg : String) : FreeM Eff Unit :=
  lift (FSum.inr (FSum.inr (TraceEff.Log msg)))

/-- Example program demonstrating effect composition.

This program logs a start message, sets up an environment with variable `x`,
retrieves the environment, looks up `x`, and returns its value plus one.
If the lookup fails, it signals an error. The program combines all three
effect types in a single computation. -/
def exampleProgram : FreeM Eff Int := do
  log "Starting computation"
  putEnv [⟨"x", 10⟩]
  let env ← getEnv
  match env.find? (·.1 = "x") with
  | some ⟨_, x⟩ => pure (x + 1)
  | none => do
      fail "x not found"
      pure 0

/-- Trace log represented as a list of string messages. -/
abbrev Trace := List String

/-- Semantic domain for effectful computations.

Represents computations that:
- Take an initial environment and trace
- May fail with a string error message
- If successful, produce a result value along with updated environment and trace

This is the target domain for interpreting `FreeM Eff` programs. -/
abbrev EffAction (α : Type) := Env → Trace → Except String (α × Env × Trace)

/-- Algebra component for pure values.

Maps pure values to effectful actions that return the value unchanged
without modifying the environment or trace. -/
def effPure {α} (a : α) : EffAction α :=
  fun env tr => .ok (a, env, tr)

/-- Algebra component for effect operations.

Interprets each effect constructor into the target semantic domain:
- `Get`: returns current environment as result
- `Put`: updates environment state
- `Fail`: signals error with message
- `Log`: appends message to trace

This defines the concrete semantics of each abstract effect. -/
def effStep {α} :
    {ι : Type} → Eff ι → (ι → EffAction α) → EffAction α
  | _, .inl StateEff.Get, k => fun env tr => k env env tr
  | _, .inl (StateEff.Put σ), k => fun _ tr => k () σ tr
  | _, .inr (.inl (ErrorEff.Fail msg)), _ => fun _ _ => .error msg
  | _, .inr (.inr (TraceEff.Log msg)), k => fun env tr => k () env (tr ++ [msg])

/-- Catamorphic interpreter for effectful computations.

Transforms a `FreeM Eff` program into a concrete effectful computation
by folding the syntax tree using the algebra defined by `effPure` and `effStep`.

This is the main interpreter that gives operational meaning to effect programs. -/
def runEff {α} : FreeM Eff α → EffAction α :=
  foldFreeM effPure effStep

/-- Big-step operational semantics for expression evaluation.

Defines a relation `EvalRel e env trace result` stating that expression `e`
evaluates to `result` when started with environment `env` and trace `trace`.

This provides the "reference semantics" against which we prove our
free monad interpreter correct -/
inductive EvalRel : Expr → Env → Trace → Except String (Int × Env × Trace) → Prop where
| val :
    ∀ n env trace,
    EvalRel (.val n) env trace (.ok (n, env, trace))
| var_found :
    ∀ x env trace v,
    env.find? (·.1 = x) = some ⟨x, v⟩ →
    EvalRel (.var x) env trace (.ok (v, env, trace))
| var_missing :
    ∀ x env trace,
    env.find? (·.1 = x) = none →
    EvalRel (.var x) env trace (.error s!"unbound variable {x}")
| add :
    ∀ e1 e2 env trace₁ trace₂ trace₃ v1 v2 env₂ env₃,
    EvalRel e1 env trace₁ (.ok (v1, env₂, trace₂)) →
    EvalRel e2 env₂ trace₂ (.ok (v2, env₃, trace₃)) →
    EvalRel (.add e1 e2) env trace₁ (.ok (v1 + v2, env₃, trace₃))
| div_ok :
    ∀ e1 e2 env trace₁ trace₂ trace₃ v1 v2 env₂ env₃,
    v2 ≠ 0 →
    EvalRel e1 env trace₁ (.ok (v1, env₂, trace₂)) →
    EvalRel e2 env₂ trace₂ (.ok (v2, env₃, trace₃)) →
    EvalRel (.div e1 e2) env trace₁ (.ok (v1 / v2, env₃, trace₃))
| div_zero :
    ∀ e1 e2 env trace₁ trace₂ trace₃ v1 v2 env₂ env₃,
    v2 = 0 →
    EvalRel e1 env trace₁ (.ok (v1, env₂, trace₂)) →
    EvalRel e2 env₂ trace₂ (.ok (v2, env₃, trace₃)) →
    EvalRel (.div e1 e2) env trace₁ (.error "divide by zero")

/-- Expression evaluator that constructs free monad syntax trees.

Transforms abstract syntax expressions into effectful computations
represented as `FreeM` trees. This separates the program structure
from its interpretation, enabling multiple ways to "run" the same program.

The evaluator handles:
- Variable lookup (with potential failure)
- Arithmetic operations
- Division by zero checking -/
def eval : Expr → FreeM Eff Int
  | .val n => pure n
  | .var x => do
      let env ← getEnv
      match env.find? (·.1 = x) with
      | some ⟨_, v⟩ => pure v
      | none => do
          fail s!"unbound variable {x}"
          pure 0
  | .add e1 e2 => do
      let v1 ← eval e1
      let v2 ← eval e2
      pure (v1 + v2)
  | .div e1 e2 => do
      let v1 ← eval e1
      let v2 ← eval e2
      if v2 = 0 then do
        fail "divide by zero"
        pure 0
      else
        pure (v1 / v2)

/-- Lemma: bind behavior when the first computation succeeds.

If running program `p` succeeds with result `v`, environment `env'`, and trace `tr'`,
then running `p >>= k` is equivalent to running `k v` with the updated state.

This captures the expected sequential composition behavior of effectful computations. -/
theorem runEff_bind_ok {α β}
    {p : FreeM Eff α} {k : α → FreeM Eff β}
    {env env' : Env} {tr tr' : Trace} {v : α}
    (h : runEff p env tr = .ok (v, env', tr')) :
    runEff (p >>= k) env tr = runEff (k v) env' tr' := by
  revert h
  induction p generalizing env env' tr tr' v <;> simp only [runEff, bind, foldFreeM] <;> intro h
  · case pure => cases h; rfl
  · case liftBind _ op _ ih =>
    cases op
    · case inl s => cases s <;> exact ih _ h
    · case inr s =>
      cases s
      case inl s => cases s; simp_all [effStep]
      case inr s => cases s; exact ih _ h

/-- Lemma: bind behavior when the first computation fails.

If running program `p` fails with error message `msg`, then running `p >>= k`
also fails with the same error message, short-circuiting the continuation `k`.

This captures the expected error propagation behavior in effectful computations. -/
theorem runEff_bind_err {α β}
    {p : FreeM Eff α} {k : α → FreeM Eff β}
    {env : Env} {tr : Trace} {msg : String} :
  runEff p env tr = .error msg →
  runEff (p >>= k) env tr = .error msg := by
  induction p generalizing env tr msg <;> simp only [runEff, bind, foldFreeM] <;> intro h
  · case pure => simp [effPure] at h
  · case liftBind _ op _ ih =>
    cases op
    · case inl s => cases s <;> exact ih _ h
    · case inr s =>
      cases s
      case inl s => cases s; cases h; rfl
      case inr s => cases s; exact ih _ h

/-- Main correctness theorem: interpreter soundness.

If the operational semantics says that expression `e` evaluates to result `res`
under environment `env` and trace `trace`, then running the free monad program
`eval e` with our interpreter produces the same result.

This establishes that our free monad interpreter is sound with respect to
the reference operational semantics. -/
theorem runEff_eval_correct (e : Expr) (env : Env) (trace : Trace)
    (res : Except String (Int × Env × Trace))
    (h : EvalRel e env trace res) :
    runEff (eval e) env trace = res := by
    induction' h
    · case val z env trace =>
      simp [eval, pure_eq_pure, runEff, effPure]
    · case var_found x env trace v h =>
      simp [runEff, eval, getEnv, lift_def, effStep, h, effPure]
    · case var_missing x env trace h =>
      simp [runEff, eval, bind, getEnv, fail, lift_def, effStep, h]
    · case add e₁ e₂ env trace₁ trace₂ trace₃ v1 v2 env₂ env₃ h₁ h₂ ih₁ ih₂ =>
      simp [eval, bind]
      have step₁ := runEff_bind_ok (p := eval e₁ ) (k := fun v1 => do
        let v2 ← eval e₂
        pure (v1 + v2)) ih₁
      simp [bind] at step₁; simp [step₁]
      have step₂ := runEff_bind_ok (p := eval e₂) (k := fun v2 => pure (v1 + v2)) ih₂
      simp [bind] at step₂; simp [step₂]; rfl
    · case div_ok e₁ e₂ env trace₁ trace₂ trace₃ v₁ v₂ env₂ env₃ v₂_ne_0 h₁ h₂ ih₁ ih₂  =>
      simp [eval, bind]
      have step₁ := runEff_bind_ok (p := eval e₁) (k := fun v1 => do
        let v2 ← eval e₂
        if v2 = 0 then do fail "divide by zero"; pure 0 else pure (v1 / v2)) ih₁
      simp [bind] at step₁; simp [step₁]
      have step₂ := runEff_bind_ok (p := eval e₂) (k := fun v₂ =>
        if v₂ = 0 then do fail "divide by zero"; pure 0 else pure (v₁ / v₂)) ih₂
      simp [bind] at step₂; simp [step₂, v₂_ne_0]
      rfl
    · case div_zero e₁ e₂ env' trace₁ trace₂ trace₃ v₁ v₂ env₂ env₃ v₂_eq_0 h₁ h₂ ih₁ ih₂ =>
      simp [eval, bind]
      have step₁ := runEff_bind_ok (p := eval e₁) (k := fun v₁ => do
        let v₂ ← eval e₂
        if v₂ = 0 then fail "divide by zero"; pure 0 else pure (v₁ / v₂)) ih₁
      simp [bind] at step₁; simp [step₁]
      have step₂ := runEff_bind_ok (p := eval e₂) (k := fun v₂ =>
        if v₂ = 0 then (do fail "divide by zero"; pure 0) else pure (v₁ / v₂)) ih₂
      simp [bind] at step₂; simp [step₂, v₂_eq_0]
      simp [fail, lift, runEff]
      rfl
