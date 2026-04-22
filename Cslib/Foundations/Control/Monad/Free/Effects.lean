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
    run (pure a : FreeState σ α) s₀ = (a, s₀) := rfl

@[simp]
lemma run_get (s₀ : σ) :
    run (lift .get) s₀ = (s₀, s₀) := rfl

@[simp]
lemma run_set (s' : σ) (s₀ : σ) :
    run (lift (.set s')) s₀ = (.unit, s') := rfl

@[simp]
lemma run_bind (x : FreeState σ α) (f : α → FreeState σ β) (s₀ : σ) :
    run (x.bind f) s₀ = let p := x.run s₀; (f p.1).run p.2 := by
  induction x using FreeM.induction generalizing f s₀ with
  | pure => simp
  | lift_bind op cont ih =>
    simp_rw [FreeM.bind_assoc]
    cases op <;> simp [← liftBind_eq, run, ih]

/-- Run a state computation, returning only the result. -/
def run' (c : FreeState σ α) (s₀ : σ) : α := (run c s₀).1

-- not `simp` since `StateT.run'` is unfolded by `simp`
theorem run'_toStateM {α : Type u} (comp : FreeState σ α) (s₀ : σ) :
    (toStateM comp).run' s₀ = pure (run' comp s₀) := by
  rw [run', StateT.run'_eq, run_toStateM]
  rfl

@[simp]
lemma run'_pure (a : α) (s₀ : σ) :
    run' (pure a : FreeState σ α) s₀ = a := rfl

@[simp]
lemma run'_get (s₀ : σ) :
    run' (lift .get) s₀ = s₀ := rfl

@[simp]
lemma run'_set (s' : σ) (s₀ : σ) :
    run' (lift (.set s')) s₀ = .unit := rfl

@[simp]
lemma run'_bind (x : FreeState σ α) (f : α → FreeState σ β) (s₀ : σ) :
    run' (x.bind f) s₀ = let p := x.run s₀; (f p.1).run' p.2 :=
  congr_arg Prod.fst <| run_bind _ _ _

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
variable {ω : Type u} {α β : Type*}

/-- Interpret `WriterF` operations into `WriterT`. -/
@[simp]
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
    run (pure a : FreeWriter ω α) = (a, 1) := rfl

@[simp]
lemma run_lift_tell [Monoid ω] (w : ω) :
    run (lift (.tell w)) = (.unit, w) := Prod.ext rfl <| mul_one _

@[simp]
lemma run_bind [Monoid ω] (x : FreeWriter ω α) (f : α → FreeWriter ω β) :
    run (x.bind f) = let p := run x; ((f p.1).run.1, p.2 * (f p.1).run.2) := by
  induction x using FreeM.induction generalizing f with
  | pure => simp
  | lift_bind op cont ih =>
    simp_rw [FreeM.bind_assoc]
    cases op
    simp [← liftBind_eq, run, ih, mul_assoc]

/--
The canonical interpreter `toWriterT` derived from `liftM` agrees with the hand-written
recursive interpreter `run` for `FreeWriter`.
-/
@[simp]
theorem run_toWriterT {α : Type u} [Monoid ω] (comp : FreeWriter ω α) :
    (toWriterT comp).run = pure (run comp) := by
  induction comp using FreeM.induction with
  | pure _ => simp [toWriterT]
  | lift_bind op cont ih =>
    simp only [toWriterT, run_bind] at *
    ext : 1
    cases op
    simp [ih]

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
    listen (pure a : FreeWriter ω α) = .pure (a, 1) := rfl

@[simp]
lemma listen_lift_tell_bind [Monoid ω] (w : ω)
    (k : PUnit → FreeWriter ω α) :
    listen (lift (.tell w) >>= k) =
      lift (.tell w) >>= (fun _ =>
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

section ForMathlib

/-- Constructor for `ContT`. -/
def _root_.ContT.mk (f : (α → m r) → m r) : ContT r m α := f

@[simp]
theorem _root_.ContT.run_mk (f : (α → m r) → m r) :
    ContT.run (.mk f : ContT r m α) k = f k := rfl

@[simp]
theorem _root_.ContT.run_pure (a : α) :
    ContT.run (pure a : ContT r m α) k = k a := rfl

@[simp]
theorem _root_.ContT.run_bind (x : ContT r m α) (f : α → ContT r m β) :
    ContT.run (x >>= f) k = ContT.run x fun x => (f x).run k := rfl

end ForMathlib

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
@[simp]
def contInterp : ContF r α → ContT r Id α
  | .callCC g => .mk fun k => pure <| g fun a => (k a).run

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

@[simp]
lemma run_pure (a : α) (k : α → r) :
    run (pure a : FreeCont r α) k = k a := rfl

@[simp]
lemma run_lift_callCC (g : (α → r) → r) (k : α → r) :
    run (lift (.callCC g)) k = g k := rfl

@[simp]
lemma run_bind (x : FreeCont r α) (f : α → FreeCont r β) (k : β → r) :
    run (x.bind f) k = run x (fun i => run (f i) k) := by
  induction x using FreeM.induction generalizing k with
  | pure a => rfl
  | lift_bind op cont ih =>
    rw [FreeM.bind_assoc]
    cases op
    simp [← liftBind_eq, run, ih]

/--
The canonical interpreter `toContT` derived from `liftM` agrees with the hand-written
recursive interpreter `run` for `FreeCont`.
-/
@[simp]
theorem run_toContT {α : Type u} (comp : FreeCont r α) (k : α → r) :
    (toContT comp).run k = pure (run comp k) := by
  simp only [toContT]
  induction comp using FreeM.induction with
  | pure a => rfl
  | lift_bind op cont ih =>
    cases op
    simp_rw [run_bind]
    simp [ih]

/-- Call with current continuation for the Free continuation monad. -/
def callCC (f : MonadCont.Label α (FreeCont r) β → FreeCont r α) :
    FreeCont r α :=
  lift (.callCC fun k => run (f ⟨fun x => lift (.callCC fun _ => k x)⟩) k)

instance : MonadCont (FreeCont r) where
  callCC := .callCC

/-- `run` of a `callCC` node simplifies to running the handler with the current continuation. -/
@[simp]
lemma run_callCC (f : MonadCont.Label α (FreeCont r) β → FreeCont r α) (k : α → r) :
    run (callCC f) k = run (f ⟨fun x => lift (.callCC fun _ => k x)⟩) k := by
  simp [callCC]

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
abbrev toReaderM {α : Type u} (comp : FreeReader σ α) : ReaderM σ α :=
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
    run (pure a : FreeReader σ α) s₀ = a := rfl

@[simp]
lemma run_read (s₀ : σ) :
    run read s₀ = s₀ := rfl

@[simp]
lemma run_bind (x : FreeReader σ α) (f : α → FreeReader σ β) (s₀ : σ) :
    run (x >>= f) s₀ = run (f <| run x s₀) s₀ := by
  rw [← Id.run_pure (run _ _), ← run_toReaderM, toReaderM, liftM_bind, ReaderT.run_bind,
    Id.run_bind, run_toReaderM, run_toReaderM, Id.run_pure, Id.run_pure]

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
