/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free.Fold
public import Mathlib.Data.Set.Countable
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.Set.Functor

/-!
# Possible outputs of polynomial free programs

`x.possibleOutputs responses` is the set of results `x` can return when each operation `op` may
answer with any response in `responses op`. It is the fold of `x` into Mathlib's set monad
(`possibleOutputs_eq_liftM`), stated as a fold so that the response and result universes stay
independent.

Allowing every response gives the lawful `MonadAttach` instance on `P.FreeM`: `CanReturn x a`
means `a` is reachable along some branch of `x`, and `attach` labels every leaf with a proof of
this without changing the program. Interpreting a program by a handler can only remove possible
results (`canReturn_of_liftM`).

This construction is ported from the [PolyFun](https://github.com/Verified-zkEVM/PolyFun) library.
-/

@[expose] public section

universe uA uB v w

namespace PFunctor.FreeM

variable {P : PFunctor.{uA, uB}} {α : Type v} {β : Type w}

/-- The results `x` can return when each operation `op` answers with a response in
`responses op`. -/
def possibleOutputs (x : P.FreeM α) (responses : (op : P.A) → Set (P.B op)) : Set α :=
  x.foldFreeM (fun a => {a}) fun op cont => ⋃ b ∈ responses op, cont b

section possibleOutputs

variable (responses : (op : P.A) → Set (P.B op))

@[simp]
theorem possibleOutputs_pure (a : α) : (pure a : P.FreeM α).possibleOutputs responses = {a} := rfl

theorem possibleOutputs_lift_bind (op : P.A) (cont : P.B op → P.FreeM α) :
    ((lift op).bind cont).possibleOutputs responses =
      ⋃ b ∈ responses op, (cont b).possibleOutputs responses := rfl

@[simp]
theorem possibleOutputs_lift (op : P.A) :
    possibleOutputs (α := no_index (P.B op)) (lift op) responses = responses op :=
  Set.biUnion_of_singleton _

@[simp]
theorem possibleOutputs_bind (x : P.FreeM α) (f : α → P.FreeM β) :
    (x.bind f).possibleOutputs responses =
      ⋃ a ∈ x.possibleOutputs responses, (f a).possibleOutputs responses := by
  induction x with
  | pure a => simp
  | lift_bind op cont ih => simp [possibleOutputs_lift_bind, ih]

@[simp]
theorem possibleOutputs_map (f : α → β) (x : P.FreeM α) :
    (x.map f).possibleOutputs responses = f '' x.possibleOutputs responses := by
  simp [← bind_pure_comp, Set.image_eq_iUnion]

@[simp]
theorem possibleOutputs_bind' {α β : Type v} (x : P.FreeM α) (f : α → P.FreeM β) :
    (x >>= f).possibleOutputs responses =
      ⋃ a ∈ x.possibleOutputs responses, (f a).possibleOutputs responses :=
  possibleOutputs_bind responses x f

@[simp]
theorem possibleOutputs_map' {α β : Type v} (f : α → β) (x : P.FreeM α) :
    (f <$> x).possibleOutputs responses = f '' x.possibleOutputs responses :=
  possibleOutputs_map responses f x

/-- `possibleOutputs` is the interpretation into the set monad. -/
theorem possibleOutputs_eq_liftM {α : Type uB} (x : P.FreeM α) :
    x.possibleOutputs responses = (x.liftM (m := SetM) responses).run :=
  (congrFun (liftM_eq_foldFreeM (m := SetM) responses) x).symm

/-- Allowing more responses can only add possible results. -/
theorem possibleOutputs_mono {responses' : (op : P.A) → Set (P.B op)}
    (h : ∀ op, responses op ⊆ responses' op) (x : P.FreeM α) :
    x.possibleOutputs responses ⊆ x.possibleOutputs responses' := by
  induction x with
  | pure a => rfl
  | lift_bind op cont ih => exact Set.biUnion_mono (h op) fun b _ => ih b

theorem possibleOutputs_countable (h : ∀ op, (responses op).Countable) (x : P.FreeM α) :
    (x.possibleOutputs responses).Countable := by
  induction x with
  | pure a => exact Set.countable_singleton a
  | lift_bind op cont ih => exact (h op).biUnion fun b _ => ih b

theorem possibleOutputs_finite (h : ∀ op, (responses op).Finite) (x : P.FreeM α) :
    (x.possibleOutputs responses).Finite := by
  induction x with
  | pure a => exact Set.finite_singleton a
  | lift_bind op cont ih => exact (h op).biUnion fun b _ => ih b

end possibleOutputs

/-- Label each result with a proof that it is reachable, keeping every branch of the program. -/
def attach : (x : P.FreeM α) → P.FreeM {a // a ∈ x.possibleOutputs fun _ => Set.univ}
  | .pure a => pure ⟨a, rfl⟩
  | .liftBind op cont => .liftBind op fun b =>
      (attach (cont b)).map fun a => ⟨a.1, Set.mem_biUnion (Set.mem_univ b) a.2⟩

theorem map_attach (x : P.FreeM α) : (attach x).map Subtype.val = x := by
  induction x with
  | pure a => rfl
  | lift_bind op cont ih => exact congrArg (liftBind op) (funext fun b => by simpa using ih b)

instance : MonadAttach P.FreeM where
  CanReturn x a := a ∈ x.possibleOutputs fun _ => Set.univ
  attach := attach

theorem canReturn_iff (x : P.FreeM α) (a : α) :
    MonadAttach.CanReturn x a ↔ a ∈ x.possibleOutputs fun _ => Set.univ := Iff.rfl

@[simp]
theorem canReturn_pure (a b : α) : MonadAttach.CanReturn (pure a : P.FreeM α) b ↔ b = a :=
  Iff.rfl

@[simp]
theorem canReturn_lift (op : P.A) (b : P.B op) :
    MonadAttach.CanReturn (α := no_index (P.B op)) (lift (P := P) op) b := by
  simp [canReturn_iff]

theorem canReturn_lift_bind (op : P.A) (cont : P.B op → P.FreeM α) (a : α) :
    MonadAttach.CanReturn ((lift op).bind cont) a ↔ ∃ b, MonadAttach.CanReturn (cont b) a := by
  simp [canReturn_iff]

@[simp]
theorem canReturn_bind (x : P.FreeM α) (f : α → P.FreeM β) (b : β) :
    MonadAttach.CanReturn (x.bind f) b ↔
      ∃ a, MonadAttach.CanReturn x a ∧ MonadAttach.CanReturn (f a) b := by
  simp [canReturn_iff]

@[simp]
theorem canReturn_map (f : α → β) (x : P.FreeM α) (b : β) :
    MonadAttach.CanReturn (x.map f) b ↔ ∃ a, MonadAttach.CanReturn x a ∧ f a = b := by
  simp [canReturn_iff]

@[simp]
theorem canReturn_bind' {α β : Type v} (x : P.FreeM α) (f : α → P.FreeM β) (b : β) :
    MonadAttach.CanReturn (x >>= f) b ↔
      ∃ a, MonadAttach.CanReturn x a ∧ MonadAttach.CanReturn (f a) b :=
  canReturn_bind x f b

@[simp]
theorem canReturn_map' {α β : Type v} (f : α → β) (x : P.FreeM α) (b : β) :
    MonadAttach.CanReturn (f <$> x) b ↔ ∃ a, MonadAttach.CanReturn x a ∧ f a = b :=
  canReturn_map f x b

instance : LawfulMonadAttach P.FreeM where
  map_attach := map_attach _
  canReturn_map_imp h := by obtain ⟨b, _, rfl⟩ := (canReturn_map _ _ _).mp h; exact b.2

/-- Binds agree when their continuations agree at every reachable result. -/
theorem bind_congr_of_canReturn (x : P.FreeM α) {f g : α → P.FreeM β}
    (h : ∀ a, MonadAttach.CanReturn x a → f a = g a) : x.bind f = x.bind g := by
  induction x with
  | pure a => exact h a rfl
  | lift_bind op cont ih =>
    exact congrArg (liftBind op)
      (funext fun b => ih b fun a ha => h a (Set.mem_biUnion (Set.mem_univ b) ha))

/-- If a handler only returns responses in `responses`, every result of the interpreted program
is a possible output for `responses`. -/
theorem mem_possibleOutputs_of_canReturn_liftM {m : Type uB → Type w}
    [Monad m] [LawfulMonad m] [MonadAttach m] [LawfulMonadAttach m] {α : Type uB}
    (responses : (op : P.A) → Set (P.B op)) (interp : (op : P.A) → m (P.B op))
    (hinterp : ∀ op b, MonadAttach.CanReturn (interp op) b → b ∈ responses op)
    (x : P.FreeM α) {a : α} (h : MonadAttach.CanReturn (x.liftM interp) a) :
    a ∈ x.possibleOutputs responses := by
  induction x with
  | pure b => exact (LawfulMonadAttach.eq_of_canReturn_pure h).symm
  | lift_bind op cont ih =>
    obtain ⟨b, hb, h⟩ := LawfulMonadAttach.canReturn_bind_imp' h
    exact Set.mem_biUnion (hinterp op b hb) (ih b h)

/-- Interpreting a program by a handler can only remove possible results. -/
theorem canReturn_of_liftM {m : Type uB → Type w}
    [Monad m] [LawfulMonad m] [MonadAttach m] [LawfulMonadAttach m] {α : Type uB}
    (interp : (op : P.A) → m (P.B op)) (x : P.FreeM α) {a : α}
    (h : MonadAttach.CanReturn (x.liftM interp) a) : MonadAttach.CanReturn x a :=
  mem_possibleOutputs_of_canReturn_liftM _ interp (fun _ _ _ => trivial) x h

section attachWith

variable {m : Type uB → Type w} [Monad m] {α : Type uB} (responses : (op : P.A) → Set (P.B op))
  (interp : (op : P.A) → m {b // b ∈ responses op})

/-- Interpret `x` by a handler whose responses carry proofs of membership in `responses`, labelling
the result with a proof that it is a possible output. -/
def attachWith : (x : P.FreeM α) → m {a // a ∈ x.possibleOutputs responses}
  | .pure a => pure ⟨a, rfl⟩
  | .liftBind op cont => do
    let b ← interp op
    let a ← attachWith (cont b.1)
    pure ⟨a.1, Set.mem_biUnion b.2 a.2⟩

@[simp]
theorem attachWith_pure (a : α) :
    (pure a : P.FreeM α).attachWith responses interp = pure ⟨a, rfl⟩ := rfl

@[simp]
theorem attachWith_lift_bind (op : P.A) (cont : P.B op → P.FreeM α) :
    (lift op >>= cont).attachWith responses interp = (do
      let b ← interp op
      let a ← (cont b.1).attachWith responses interp
      pure ⟨a.1, Set.mem_biUnion b.2 a.2⟩) := rfl

/-- Erasing the attached proofs recovers interpretation by the underlying handler. -/
theorem map_attachWith [LawfulMonad m] (x : P.FreeM α) :
    Subtype.val <$> x.attachWith responses interp = x.liftM (Subtype.val <$> interp ·) := by
  induction x <;> simp [*]

end attachWith

/-- A program has a possible result when every operation has a response. -/
theorem exists_canReturn [∀ op, Nonempty (P.B op)] (x : P.FreeM α) :
    ∃ a, MonadAttach.CanReturn x a := by
  induction x with
  | pure a => exact ⟨a, rfl⟩
  | lift_bind op cont ih => exact (ih (Classical.arbitrary _)).imp fun _ => Set.mem_biUnion trivial

end PFunctor.FreeM
