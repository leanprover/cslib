/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Cslib.Foundations.Control.Monad.Free
public import Mathlib.Control.Monad.Cont

@[expose] public section

/-!
# Free Monad

This file defines several canonical instances on the free monad.

## Main definitions

- `FreeState`, `FreeWriter`, `FreeCont`, `FreeReader`: Specific effect monads

## Implementation

To execute or interpret these computations, we provide two approaches:
1. **Hand-written interpreters** (`FreeState.run`, `FreeWriter.run`, `FreeCont.run`,
  `FreeReader.run`) that directly
  pattern-match on the tree structure
2. **Canonical interpreters** (`FreeState.toStateM`, `FreeWriter.toWriterT`, `FreeCont.toContT`,
  `FreeReader.toReaderM`)
  derived from the universal property via `liftM`

We prove that these approaches are equivalent, demonstrating that the implementation aligns with
the theory. We also provide uniqueness theorems for the canonical interpreters, which follow from
the universal property.

## Tags

Free monad, state monad, writer monad, continuation monad
-/

namespace Cslib

namespace FreeM

universe u v w w' w''

/-! ### State Monad via `FreeM` -/

/-- Type constructor for state operations. -/
inductive StateF (σ : Type u) : Type u → Type u where
  /-- Get the current state. -/
  | get : StateF σ σ
  /-- Set the state. -/
  | set : σ → StateF σ PUnit

/-- State monad via the `FreeM` monad. -/
abbrev FreeState (σ : Type u) := FreeM (StateF σ)

namespace FreeState
variable {σ : Type u} {α : Type v}

instance : MonadStateOf σ (FreeState σ) where
  get := .lift .get
  set newState := .liftBind (.set newState) (fun _ => .pure PUnit.unit)
  modifyGet f :=
    .liftBind .get (fun s =>
      let (a, s') := f s
      .liftBind (.set s') (fun _ => .pure a))

@[simp]
lemma get_def : (get : FreeState σ σ) = .lift .get := rfl

@[simp]
lemma set_def (s : σ) : (set s : FreeState σ PUnit) = .lift (.set s) := rfl

/-- Interpret `StateF` operations into `StateM`. -/
def stateInterp {α : Type u} : StateF σ α → StateM σ α
  | .get => MonadStateOf.get
  | .set s => MonadStateOf.set s

/-- Convert a `FreeState` computation into a `StateM` computation. This is the canonical
interpreter derived from `liftM`. -/
def toStateM {α : Type u} (comp : FreeState σ α) : StateM σ α :=
  comp.liftM stateInterp

/-- `toStateM` is the unique interpreter extending `stateInterp`. -/
theorem toStateM_unique {α : Type u} (g : FreeState σ α → StateM σ α)
    (h : Interprets stateInterp g) : g = toStateM := h.eq

/-- Run a state computation, returning both the result and final state. -/
def run (comp : FreeState σ α) (s₀ : σ) : α × σ :=
  match comp with
  | .pure a => (a, s₀)
  | .liftBind StateF.get k => run (k s₀) s₀
  | .liftBind (StateF.set s') k => run (k PUnit.unit) s'

/--
The canonical interpreter `toStateM` derived from `liftM` agrees with the hand-written
recursive interpreter `run` for `FreeState`.
-/
@[simp]
theorem run_toStateM {α : Type u} (comp : FreeState σ α) (s₀ : σ) :
    (toStateM comp).run s₀ = pure (run comp s₀) := by
  induction comp generalizing s₀ with
  | pure a => rfl
  | liftBind op cont ih =>
    cases op <;> apply ih

@[simp]
lemma run_pure (a : α) (s₀ : σ) :
    run (.pure a : FreeState σ α) s₀ = (a, s₀) := rfl

@[simp]
lemma run_get (k : σ → FreeState σ α) (s₀ : σ) :
    run (liftBind .get k) s₀ = run (k s₀) s₀ := rfl

@[simp]
lemma run_set (s' : σ) (k : PUnit → FreeState σ α) (s₀ : σ) :
    run (liftBind (.set s') k) s₀ = run (k .unit) s' := rfl

/-- Run a state computation, returning only the result. -/
def run' (c : FreeState σ α) (s₀ : σ) : α := (run c s₀).1

@[simp]
theorem run'_toStateM {α : Type u} (comp : FreeState σ α) (s₀ : σ) :
    (toStateM comp).run' s₀ = pure (run' comp s₀) := by
  rw [run', StateT.run'_eq, run_toStateM]
  rfl

@[simp]
lemma run'_pure (a : α) (s₀ : σ) :
    run' (.pure a : FreeState σ α) s₀ = a := rfl

@[simp]
lemma run'_get (k : σ → FreeState σ α) (s₀ : σ) :
    run' (liftBind .get k) s₀ = run' (k s₀) s₀ := rfl

@[simp]
lemma run'_set (s' : σ) (k : PUnit → FreeState σ α) (s₀ : σ) :
    run' (liftBind (.set s') k) s₀ = run' (k .unit) s' := rfl

end FreeState

/-! ### Writer Monad via `FreeM` -/

/--
Type constructor for writer operations. Writer has a single effect, so the definition has just one
constructor.
-/
inductive WriterF (ω : Type u) : Type v → Type u
  /-- Write a value to the log. -/
  | tell : ω → WriterF ω PUnit

/-- Writer monad implemented via the `FreeM` monad construction. This provides a more efficient
implementation than the traditional `WriterT` transformer, as it avoids buffering the log. -/
abbrev FreeWriter (ω : Type u) := FreeM (WriterF ω)

namespace FreeWriter

open WriterF
variable {ω : Type u} {α : Type u}

/-- Interpret `WriterF` operations into `WriterT`. -/
def writerInterp {α : Type u} : WriterF ω α → WriterT ω Id α
  | .tell w => MonadWriter.tell w

/-- Convert a `FreeWriter` computation into a `WriterT` computation. This is the canonical
interpreter derived from `liftM`. -/
def toWriterT {α : Type u} [Monoid ω] (comp : FreeWriter ω α) : WriterT ω Id α :=
  comp.liftM writerInterp

/-- `toWriterT` is the unique interpreter extending `writerInterp`. -/
theorem toWriterT_unique {α : Type u} [Monoid ω] (g : FreeWriter ω α → WriterT ω Id α)
    (h : Interprets writerInterp g) : g = toWriterT := h.eq

/--
Writes a log entry. This creates an effectful node in the computation tree.
-/
abbrev tell (w : ω) : FreeWriter ω PUnit :=
  lift (.tell w)

@[simp]
lemma tell_def (w : ω) :
    tell w = .lift (.tell w) := rfl

/--
Interprets a `FreeWriter` computation by recursively traversing the tree, accumulating
log entries with the monoid operation, and returns the final value paired with the accumulated log.
-/
def run [Monoid ω] : FreeWriter ω α → α × ω
  | .pure a => (a, 1)
  | .liftBind (.tell w) k =>
      let (a, w') := run (k .unit)
      (a, w * w')

@[simp]
lemma run_pure [Monoid ω] (a : α) :
    run (.pure a : FreeWriter ω α) = (a, 1) := rfl

@[simp]
lemma run_liftBind_tell [Monoid ω] (w : ω) (k : PUnit → FreeWriter ω α) :
    run (liftBind (.tell w) k) = (let (a, w') := run (k .unit); (a, w * w')) := rfl


-- https://github.com/leanprover-community/mathlib4/pull/36497
section missing_from_mathlib

@[simp]
theorem _root_.WriterT.run_pure [Monoid ω] [Monad M] (a : α) :
    WriterT.run (pure a : WriterT ω M α) = pure (a, 1) := rfl

@[simp]
theorem _root_.WriterT.run_bind [Monoid ω] [Monad M] (x : WriterT ω M α) (f : α → WriterT ω M β) :
    WriterT.run (x >>= f) = x.run >>= fun (a, w₁) => (fun (b, w₂) => (b, w₁ * w₂)) <$> (f a).run :=
  rfl

@[simp]
theorem _root_.WriterT.run_tell [Monad M] (w : ω) :
    WriterT.run (MonadWriter.tell w : WriterT ω M PUnit) = pure (.unit, w) := rfl

end missing_from_mathlib

/--
The canonical interpreter `toWriterT` derived from `liftM` agrees with the hand-written
recursive interpreter `run` for `FreeWriter`.
-/
@[simp]
theorem run_toWriterT {α : Type u} [Monoid ω] (comp : FreeWriter ω α) :
    (toWriterT comp).run = pure (run comp) := by
  ext : 1
  induction comp with
  | pure _ => simp only [toWriterT, liftM_pure, run_pure, pure, WriterT.run]
  | liftBind op cont ih =>
    cases op
    simp only [toWriterT, liftM_liftBind, run_liftBind_tell, Id.run_pure] at *
    rw [ ← ih]
    simp [WriterT.run_bind, writerInterp]

/--
`listen` captures the log produced by a subcomputation incrementally. It traverses the computation,
emitting log entries as encountered, and returns the accumulated log as a result.
-/
def listen [Monoid ω] : FreeWriter ω α → FreeWriter ω (α × ω)
  | .pure a => .pure (a, 1)
  | .liftBind (.tell w) k =>
      liftBind (.tell w) fun _ =>
        listen (k .unit) >>= fun (a, w') =>
          pure (a, w * w')

@[simp]
lemma listen_pure [Monoid ω] (a : α) :
    listen (.pure a : FreeWriter ω α) = .pure (a, 1) := rfl

@[simp]
lemma listen_liftBind_tell [Monoid ω] (w : ω)
    (k : PUnit → FreeWriter ω α) :
    listen (liftBind (.tell w) k) =
      liftBind (.tell w) (fun _ =>
        listen (k .unit) >>= fun (a, w') =>
          pure (a, w * w')) := by
  rfl

/--
`pass` allows a subcomputation to modify its own log. After traversing the computation and
accumulating its log, the resulting function is applied to rewrite the accumulated log
before re-emission.
-/
def pass [Monoid ω] (m : FreeWriter ω (α × (ω → ω))) : FreeWriter ω α :=
  let ((a, f), w) := run m
  liftBind (.tell (f w)) (fun _ => .pure a)

@[simp]
lemma pass_def [Monoid ω] (m : FreeWriter ω (α × (ω → ω))) :
    pass m = let ((a, f), w) := run m; liftBind (.tell (f w)) fun _ => .pure a := rfl

instance [Monoid ω] : MonadWriter ω (FreeWriter ω) where
  tell := tell
  listen := listen
  pass := pass

end FreeWriter

/-! ### Continuation Monad via `FreeM` -/

/-- Type constructor for continuation operations. -/
inductive ContF (r : Type u) (α : Type v) where
  /-- Call with current continuation: provides access to the current continuation. -/
  | callCC : ((α → r) → r) → ContF r α

instance {r : Type u} : Functor (ContF r) where
  map f
  | .callCC g => .callCC fun k => g (k ∘ f)

/-- Continuation monad via the `FreeM` monad. -/
abbrev FreeCont (r : Type u) := FreeM (ContF r)

namespace FreeCont
variable {r : Type u} {α : Type v} {β : Type w}

/-- Interpret `ContF r` operations into `ContT r Id`. -/
def contInterp : ContF r α → ContT r Id α
  | .callCC g => g

/-- Convert a `FreeCont` computation into a `ContT` computation. This is the canonical
interpreter derived from `liftM`. -/
def toContT {α : Type u} (comp : FreeCont r α) : ContT r Id α :=
  comp.liftM contInterp

/-- `toContT` is the unique interpreter extending `contInterp`. -/
theorem toContT_unique {α : Type u} (g : FreeCont r α → ContT r Id α)
    (h : Interprets contInterp g) : g = toContT := h.eq

/-- Run a continuation computation with the given continuation. -/
def run : FreeCont r α → (α → r) → r
  | .pure a, k => k a
  | .liftBind (.callCC g) cont, k => g (fun a => run (cont a) k)

/--
The canonical interpreter `toContT` derived from `liftM` agrees with the hand-written
recursive interpreter `run` for `FreeCont`.
-/
@[simp]
theorem run_toContT {α : Type u} (comp : FreeCont r α) (k : α → r) :
    (toContT comp).run k = pure (run comp k) := by
  induction comp with
  | pure a => rfl
  | liftBind op cont ih =>
    simp only [toContT, FreeM.liftM]
    cases op
    simp only [run, bind, ContT.run, id]
    congr with x
    apply ih

@[simp]
lemma run_pure (a : α) (k : α → r) :
    run (.pure a : FreeCont r α) k = k a := rfl

@[simp]
lemma run_liftBind_callCC (g : (α → r) → r)
    (cont : α → FreeCont r β) (k : β → r) :
    run (liftBind (.callCC g) cont) k = g (fun a => run (cont a) k) := rfl

/-- Call with current continuation for the Free continuation monad. -/
def callCC (f : MonadCont.Label α (FreeCont r) β → FreeCont r α) :
    FreeCont r α :=
  liftBind (.callCC fun k => run (f ⟨fun x => liftBind (.callCC fun _ => k x) pure⟩) k) pure

@[simp]
lemma callCC_def (f : MonadCont.Label α (FreeCont r) β → FreeCont r α) :
    callCC f =
      liftBind (.callCC fun k => run (f ⟨fun x => liftBind (.callCC fun _ => k x) pure⟩) k) pure :=
  rfl

instance : MonadCont (FreeCont r) where
  callCC := .callCC

/-- `run` of a `callCC` node simplifies to running the handler with the current continuation. -/
@[simp]
lemma run_callCC (f : MonadCont.Label α (FreeCont r) β → FreeCont r α) (k : α → r) :
    run (callCC f) k = run (f ⟨fun x => liftBind (.callCC fun _ => k x) pure⟩) k := by
  simp [callCC, run_liftBind_callCC]

end FreeCont

/-- Type constructor for reader operations. -/
inductive ReaderF (σ : Type u) : Type u → Type u where
  | read : ReaderF σ σ

/-- Reader monad via the `FreeM` monad -/
abbrev FreeReader (σ) := FreeM (ReaderF σ)

namespace FreeReader

variable {σ : Type u} {α : Type u}

instance : MonadReaderOf σ (FreeReader σ) where
  read := .lift .read

@[simp]
lemma read_def : (read : FreeReader σ σ) = .lift .read := rfl

instance : MonadReader σ (FreeReader σ) := inferInstance

/-- Interpret `ReaderF` operations into `ReaderM`. -/
def readInterp {α : Type u} : ReaderF σ α → ReaderM σ α
  | .read => MonadReaderOf.read

/-- Convert a `FreeReader` computation into a `ReaderM` computation. This is the canonical
interpreter derived from `liftM`. -/
def toReaderM {α : Type u} (comp : FreeReader σ α) : ReaderM σ α :=
  comp.liftM readInterp

/-- `toReaderM` is the unique interpreter extending `readInterp`. -/
theorem toReaderM_unique {α : Type u} (g : FreeReader σ α → ReaderM σ α)
    (h : Interprets readInterp g) : g = toReaderM := h.eq

/-- Run a reader computation -/
def run (comp : FreeReader σ α) (s₀ : σ) : α :=
  match comp with
  | .pure a => a
  | .liftBind ReaderF.read a => run (a s₀) s₀

/--
The canonical interpreter `toReaderM` derived from `liftM` agrees with the hand-written
recursive interpreter `run` for `FreeReader` -/
@[simp]
theorem run_toReaderM {α : Type u} (comp : FreeReader σ α) (s : σ) :
    (toReaderM comp).run s = pure (run comp s) := by
  induction comp generalizing s with
  | pure a => rfl
  | liftBind op cont ih =>
    cases op; apply ih

@[simp]
lemma run_pure (a : α) (s₀ : σ) :
    run (.pure a : FreeReader σ α) s₀ = a := rfl

@[simp]
lemma run_read (k : σ → FreeReader σ α) (s₀ : σ) :
    run (liftBind .read k) s₀ = run (k s₀) s₀ := rfl

instance instMonadWithReaderOf : MonadWithReaderOf σ (FreeReader σ) where
  withReader {α} f m :=
    let rec go : FreeReader σ α → FreeReader σ α
      | .pure a => .pure a
      | .liftBind .read cont =>
          .liftBind .read fun s => go (cont (f s))
    go m

@[simp] theorem run_withReader (f : σ → σ) (m : FreeReader σ α) (s : σ) :
    run (withTheReader σ f m) s = run m (f s) := by
  induction m generalizing s with
  | pure a => rfl
  | liftBind op cont ih =>
    cases op
    simpa [withTheReader, instMonadWithReaderOf, run] using (ih (f s) s)

end FreeReader

end FreeM

end Cslib
