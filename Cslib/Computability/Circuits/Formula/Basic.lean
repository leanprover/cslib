/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Circuits.Basis

@[expose] public section

/-! # Boolean Formulas

A Boolean formula is a tree-structured expression built from variables and gates drawn
from a `Basis`. Unlike circuits, formulas require every gate output to feed into exactly
one parent — there is no fan-out sharing. This means every formula is a tree (not a DAG),
and its size is an upper bound on the number of distinct sub-computations.

## Design notes

The `Formula` type itself is basis-agnostic — it is parameterized by an arbitrary operation
type `Op` without requiring a `Basis` instance. This keeps the structural operations (`map`,
`size`, `depth`, etc.) independent of evaluation semantics.

Arity enforcement happens at evaluation time: `Formula.eval` uses the `Decidable` instance
on `Arity.admits` to check whether each gate's children count matches its declared arity.
Gates with mismatched arity evaluate to `none`. For well-formed formulas (e.g., those built
via the smart constructors in `Formula.Std`), evaluation always returns `some`.

## Main definitions

- `Formula` — inductive type of Boolean formulas over variables `Var` and gates `Op`
- `Formula.eval` — evaluate a formula under a variable assignment (requires `[Basis Op]`),
  returning `Option Bool` (`none` for malformed, `some b` for genuine computation)
- `Formula.WellFormed` — predicate ensuring every gate has the correct arity
- `Formula.WellFormed.eval_isSome` — well-formed formulas always evaluate to `some`
- `Formula.map` — rename variables by applying a function to every leaf
- `Formula.ind` — custom induction principle with membership-based hypothesis

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraB2009]
-/

namespace Cslib.Circuits

/-- Collect a list of `Option α` into an `Option (List α)`.
Returns `some` of the collected values if all entries are `some`,
or `none` if any entry is `none`. -/
def optionAll : List (Option α) → Option (List α)
  | [] => some []
  | (some a) :: rest => (optionAll rest).map (a :: ·)
  | none :: _ => none

@[simp]
theorem optionAll_nil : (optionAll ([] : List (Option α))) = some [] := rfl

@[simp]
theorem optionAll_cons_some (a : α) (rest : List (Option α)) :
    optionAll (some a :: rest) = (optionAll rest).map (a :: ·) := rfl

@[simp]
theorem optionAll_cons_none (rest : List (Option α)) :
    optionAll (none :: rest) = none := rfl

@[simp]
theorem optionAll_map_some (xs : List α) :
    optionAll (xs.map some) = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- If every element of a list is `some`, then `optionAll` succeeds and preserves length. -/
theorem optionAll_of_forall_isSome {xs : List (Option α)}
    (h : ∀ x ∈ xs, x.isSome = true) :
    ∃ ys, optionAll xs = some ys ∧ ys.length = xs.length := by
  induction xs with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons x xs ih =>
    have hx := h x (by simp)
    rw [Option.isSome_iff_exists] at hx
    obtain ⟨a, ha⟩ := hx
    obtain ⟨ys, hys, hlen⟩ := ih (fun x' hx' => h x' (by simp [hx']))
    exact ⟨a :: ys, by simp [ha, hys], by simp [hlen]⟩

/-- A Boolean formula over variables of type `Var` and gate operations of type `Op`.

Formulas are trees: each gate takes a list of sub-formulas as children. The type
does not enforce arity constraints — any operation can be applied to any number of
children. Arity is checked dynamically during `eval`. -/
inductive Formula (Var : Type*) (Op : Type*) where
  /-- A variable leaf. -/
  | var : Var → Formula Var Op
  /-- A gate applied to a list of sub-formula children. -/
  | gate : Op → List (Formula Var Op) → Formula Var Op

namespace Formula

variable {Var Var' : Type*} {Op : Type*}

/-- Evaluate a formula under a variable assignment.

Variables return `some` of the assignment. At each gate, children are evaluated
recursively; if any child returns `none`, the gate returns `none`. Otherwise, the
resulting list is passed to `Basis.eval` if the arity check succeeds. If the children
count does not match the operation's declared arity, the gate returns `none`. -/
@[simp, scoped grind =]
def eval [Basis Op] (assignment : Var → Bool) : Formula Var Op → Option Bool
  | .var v => some (assignment v)
  | .gate op children =>
    (optionAll (children.map (eval assignment))).bind fun bs =>
      if h : (Basis.arity op).admits bs.length then
        some (Basis.eval op bs h)
      else
        none

/-- A formula is **well-formed** if every gate's children count matches its declared arity,
and all children are themselves well-formed. Variables are always well-formed. -/
def WellFormed [Basis Op] : Formula Var Op → Prop
  | .var _ => True
  | .gate op children =>
    (Basis.arity op).admits children.length ∧ ∀ c ∈ children, WellFormed c

/-- Rename variables in a formula by applying `f` to every variable leaf.
Gate structure and operations are preserved; only the `var` nodes change. -/
@[scoped grind =]
def map (f : Var → Var') : Formula Var Op → Formula Var' Op
  | .var v => .var (f v)
  | .gate op children => .gate op (children.map (Formula.map f))

/-- Custom induction principle for `Formula` that provides `∀ c ∈ children, motive c`
as the induction hypothesis for the `gate` case, rather than Lean's default structural
induction on the nested `List`. Use with `induction f using Formula.ind`. -/
@[elab_as_elim]
def ind {motive : Formula Var Op → Prop}
    (hvar : ∀ v, motive (.var v))
    (hgate : ∀ op children, (∀ c ∈ children, motive c) → motive (.gate op children))
    : ∀ f, motive f
  | .var v => hvar v
  | .gate op children => hgate op children fun c hc =>
      have : sizeOf c < 1 + sizeOf op + sizeOf children :=
        Nat.lt_of_lt_of_le (List.sizeOf_lt_of_mem hc) (Nat.le_add_left _ _)
      ind hvar hgate c
termination_by f => sizeOf f

/-- Well-formed formulas always evaluate to `some`. -/
theorem WellFormed.eval_isSome [Basis Op] {f : Formula Var Op}
    (hf : f.WellFormed) (v : Var → Bool) : (f.eval v).isSome = true := by
  induction f using Formula.ind with
  | hvar _ => simp [eval]
  | hgate op children ih =>
    unfold WellFormed at hf
    obtain ⟨harity, hchildren⟩ := hf
    have h_all : ∀ x ∈ children.map (eval v), x.isSome = true := by
      simp only [List.mem_map]
      rintro _ ⟨c, hc, rfl⟩
      exact ih c hc (hchildren c hc)
    obtain ⟨bs, hbs, hlen⟩ := optionAll_of_forall_isSome h_all
    have hadmits : (Basis.arity op).admits bs.length := by
      rw [hlen, List.length_map]; exact harity
    simp only [eval, hbs, Option.bind_some, dif_pos hadmits, Option.isSome_some]

/-- Well-formedness is preserved by variable renaming. -/
theorem WellFormed_map [Basis Op] {f : Formula Var Op} (g : Var → Var')
    (hf : f.WellFormed) : (f.map g).WellFormed := by
  induction f using Formula.ind with
  | hvar _ =>
    unfold map WellFormed
    trivial
  | hgate op children ih =>
    unfold WellFormed at hf
    obtain ⟨harity, hchildren⟩ := hf
    unfold map
    unfold WellFormed
    exact ⟨by rw [List.length_map]; exact harity,
           fun c hc => by
             simp only [List.mem_map] at hc
             obtain ⟨c', hc'_mem, rfl⟩ := hc
             exact ih c' hc'_mem (hchildren c' hc'_mem)⟩

end Formula

end Cslib.Circuits
