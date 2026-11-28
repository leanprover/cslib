/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Languages.Mech.Common.LocalStore

/-! # Local expressions -/

@[expose] public section

namespace Cslib.Mech

namespace LocalSig

/-- A local expression. -/
inductive Expr (L : LocalSig.{u, v}) : Type v → Type (max u (v + 1))
  /-- A value. -/
  | val {α} (v : α) : L.Expr α
  /-- Read a local variable. -/
  | var {α} (x : L.Var α) : L.Expr α
  /-- Evaluate two expressions as a pair. -/
  | pair {α β} (left : L.Expr α) (right : L.Expr β) : L.Expr (α × β)
  /-- Perform the computation `r` (modelled as a relation, in order to allow for nondeterminism) on
    the value of expression `arg`: the result may be any `b` with `r a b`, where `a` is the value of
    `arg`. -/
  | call {α β} (r : α → β → Prop) (arg : L.Expr α) : L.Expr β

/-- Any variable is an expression. -/
instance {L : LocalSig} {α} : Coe (L.Var α) (L.Expr α) := ⟨Expr.var⟩

/-- Apply a Lean function to an expression: the call of its graph. -/
def Expr.map {L : LocalSig} {α β} (f : α → β) (e : L.Expr α) : L.Expr β :=
  .call (fun a b => b = f a) e

/-- Apply a binary Lean function to two expressions. -/
def Expr.map₂ {L : LocalSig} {α β γ} (f : α → β → γ) (a : L.Expr α) (b : L.Expr β) : L.Expr γ :=
  .map (fun p => f p.1 p.2) (.pair a b)

instance {L : LocalSig} : Functor (L.Expr) where
  map := Expr.map

instance {L : LocalSig} : Seq (L.Expr) where
  seq f a := Expr.map₂ (fun g x => g x) f (a ())

/-- The names of the variables read by an expression. -/
def Expr.varNames {L : LocalSig} {α} : L.Expr α → Finset L.VarName
  | .val _ => ∅
  | .var x => {x.name}
  | .pair left right => left.varNames ∪ right.varNames
  | .call _ arg => arg.varNames

@[simp, grind =]
theorem Expr.varNames_val {L : LocalSig} {α} (v : α) : (Expr.val (L := L) v).varNames = ∅ := rfl

@[simp, grind =]
theorem Expr.varNames_var {L : LocalSig} {α} (x : L.Var α) : (Expr.var x).varNames = {x.name} :=
  rfl

@[simp, grind =]
theorem Expr.varNames_pair {L : LocalSig} {α β} (left : L.Expr α) (right : L.Expr β) :
    (Expr.pair left right).varNames = left.varNames ∪ right.varNames := rfl

@[simp, grind =]
theorem Expr.varNames_call {L : LocalSig} {α β} (r : α → β → Prop) (arg : L.Expr α) :
    (Expr.call r arg).varNames = arg.varNames := rfl

@[simp, grind =]
theorem Expr.varNames_map {L : LocalSig} {α β} (f : α → β) (e : L.Expr α) :
    (e.map f).varNames = e.varNames := rfl

/-- Evaluation of expressions relative to a local store: `e.Eval σ v` states that `e` may evaluate
to `v`. -/
inductive Expr.Eval.{u, v} {L : LocalSig.{u, v}} (σ : L.Store) : {α : Type v} → L.Expr α → α → Prop
  /-- A value evaluates to itself. -/
  | val {α} (v : α) : Eval σ (.val v) v
  /-- A variable evaluates to its value in the local store. -/
  | var {α} (x : L.Var α) : Eval σ (.var x) σ[x]
  /-- Two components of a pair evaluate independently. -/
  | pair {α β} {left : L.Expr α} {right : L.Expr β} {a : α} {b : β}
      (hl : Eval σ left a) (hr : Eval σ right b) : Eval σ (.pair left right) (a, b)
  /-- A call evaluates its argument and returns any result related to it. -/
  | call {α β} {r : α → β → Prop} {arg : L.Expr α} {a : α} {b : β}
      (harg : Eval σ arg a) (hr : r a b) : Eval σ (.call r arg) b

/-- A variable has the value stored at its name. -/
@[simp, grind =]
theorem Expr.Eval.var_iff {L : LocalSig} (σ : L.Store) {α} (x : L.Var α) (v : α) :
    Expr.Eval σ (.var x) v ↔ v = σ[x] := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .var x

/-- A call evaluates exactly to the results related to a value of its argument. -/
theorem Expr.Eval.call_iff {L : LocalSig} (σ : L.Store) {α β} (r : α → β → Prop)
    (arg : L.Expr α) (b : β) : Expr.Eval σ (.call r arg) b ↔ ∃ a, arg.Eval σ a ∧ r a b := by
  constructor
  · intro h
    cases h with
    | call harg hr => exact ⟨_, harg, hr⟩
  · rintro ⟨_, harg, hr⟩
    exact .call harg hr

/-- Applying a Lean function evaluates to its value on a value of the argument. -/
@[simp]
theorem Expr.Eval.map_iff {L : LocalSig} (σ : L.Store) {α β} (f : α → β)
    (arg : L.Expr α) (b : β) : (arg.map f).Eval σ b ↔ ∃ a, arg.Eval σ a ∧ b = f a :=
  call_iff σ _ arg b

/-- The values of an expression depend only on the variables it reads. -/
theorem Expr.Eval.of_agreeOn {L : LocalSig} {σ₁ σ₂ : L.Store} {α} {e : L.Expr α} {v : α}
    (h : σ₁.AgreeOn σ₂ e.varNames) (he : e.Eval σ₁ v) : e.Eval σ₂ v := by
  induction he with
  | val v => exact .val v
  | var x => rw [h x (by simp)]; exact .var x
  | pair _ _ ihl ihr =>
    exact .pair (ihl (h.mono Finset.subset_union_left)) (ihr (h.mono Finset.subset_union_right))
  | call _ hr ih => exact .call (ih h) hr

/-- Stores that agree on the variables read by an expression give it the same values. -/
theorem Expr.Eval.congr {L : LocalSig} {σ₁ σ₂ : L.Store} {α} {e : L.Expr α} {v : α}
    (h : σ₁.AgreeOn σ₂ e.varNames) : e.Eval σ₁ v ↔ e.Eval σ₂ v :=
  ⟨of_agreeOn h, of_agreeOn h.symm⟩

end LocalSig

namespace Sig

/-- A local expression of type `α` of process `p`. -/
abbrev Expr {Pid} (S : Sig Pid) (p : Pid) (α : Type*) := (S p).Expr α

end Sig

end Cslib.Mech
