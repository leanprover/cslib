/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Circuits.Formula.Measures

@[expose] public section

/-! # Standard-Basis Boolean Formulas

Convenience constructors and evaluation/measure lemmas for formulas over the standard
bounded fan-in basis (`NCOp`): binary AND, binary OR, and unary NOT.

The smart constructors `Formula.and`, `Formula.or`, and `Formula.not` build formulas
with the correct number of children for each operation, so `Formula.eval` always
returns `some` for formulas built this way.

## Main definitions

- `Formula.and`, `Formula.or`, `Formula.not` — smart constructors that guarantee
  correct arity
- `eval_and`, `eval_or`, `eval_not` — evaluation reduces to `Option.bind`/`Option.map`
  of native Boolean operations
- `WellFormed_and`, `WellFormed_or`, `WellFormed_not`, `WellFormed_var` — smart
  constructors produce well-formed formulas
- `eval_not_not` — double negation elimination
- `deMorgan_and`, `deMorgan_or` — De Morgan's laws at the formula level
- `size_and`, `size_or`, `size_not` — size of standard constructs
- `depth_and`, `depth_or`, `depth_not` — depth of standard constructs

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraB2009]
-/

namespace Cslib.Circuits

namespace Formula

variable {Var : Type*}

/-- Binary AND of two formulas over the standard basis.
Constructs `.gate .and [a, b]`, which has exactly 2 children matching `NCOp.and`'s arity. -/
@[scoped grind =]
def and (a b : Formula Var NCOp) : Formula Var NCOp := .gate .and [a, b]

/-- Binary OR of two formulas over the standard basis.
Constructs `.gate .or [a, b]`, which has exactly 2 children matching `NCOp.or`'s arity. -/
@[scoped grind =]
def or (a b : Formula Var NCOp) : Formula Var NCOp := .gate .or [a, b]

/-- Negation of a formula over the standard basis.
Constructs `.gate .not [a]`, which has exactly 1 child matching `NCOp.not`'s arity. -/
@[scoped grind =]
def not (a : Formula Var NCOp) : Formula Var NCOp := .gate .not [a]

/-! ### Well-formedness lemmas -/

@[simp]
theorem WellFormed_var : (Formula.var v : Formula Var NCOp).WellFormed := by
  unfold WellFormed; trivial

@[simp]
theorem WellFormed_and {a b : Formula Var NCOp}
    (ha : a.WellFormed) (hb : b.WellFormed) : (Formula.and a b).WellFormed := by
  unfold Formula.and WellFormed
  exact ⟨by simp [Arity.admits], fun c hc => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> assumption⟩

@[simp]
theorem WellFormed_or {a b : Formula Var NCOp}
    (ha : a.WellFormed) (hb : b.WellFormed) : (Formula.or a b).WellFormed := by
  unfold Formula.or WellFormed
  exact ⟨by simp [Arity.admits], fun c hc => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> assumption⟩

@[simp]
theorem WellFormed_not {a : Formula Var NCOp}
    (ha : a.WellFormed) : (Formula.not a).WellFormed := by
  unfold Formula.not WellFormed
  exact ⟨by simp [Arity.admits], fun c hc => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc; rw [hc]; exact ha⟩

/-! ### Evaluation lemmas -/

@[simp, scoped grind =]
theorem eval_and (v : Var → Bool) (a b : Formula Var NCOp) :
    (Formula.and a b).eval v =
      (a.eval v).bind fun a' => (b.eval v).map (a' && ·) := by
  simp only [Formula.and, eval]
  cases ha : eval v a with
  | none => simp [ha]
  | some a' =>
    cases hb : eval v b with
    | none => simp [ha, hb]
    | some b' => simp [ha, hb, Basis.eval, Arity.admits]

@[simp, scoped grind =]
theorem eval_or (v : Var → Bool) (a b : Formula Var NCOp) :
    (Formula.or a b).eval v =
      (a.eval v).bind fun a' => (b.eval v).map (a' || ·) := by
  simp only [Formula.or, eval]
  cases ha : eval v a with
  | none => simp [ha]
  | some a' =>
    cases hb : eval v b with
    | none => simp [ha, hb]
    | some b' => simp [ha, hb, Basis.eval, Arity.admits]

@[simp, scoped grind =]
theorem eval_not (v : Var → Bool) (a : Formula Var NCOp) :
    (Formula.not a).eval v = (a.eval v).map (!·) := by
  simp only [Formula.not, eval]
  cases ha : eval v a with
  | none => simp [ha]
  | some a' => simp [ha, Basis.eval, Arity.admits]

/-! ### Double negation -/

@[simp, scoped grind =]
theorem eval_not_not (v : Var → Bool) (a : Formula Var NCOp) :
    (Formula.not (Formula.not a)).eval v = a.eval v := by
  simp only [eval_not, Option.map_map, Function.comp_def, Bool.not_not, Option.map_id']

/-! ### De Morgan's laws -/

@[scoped grind =]
theorem deMorgan_and (v : Var → Bool) (a b : Formula Var NCOp) :
    (Formula.not (Formula.and a b)).eval v =
    (Formula.or (Formula.not a) (Formula.not b)).eval v := by
  simp only [eval_not, eval_and, eval_or]
  cases a.eval v <;> cases b.eval v <;>
    simp [Option.bind, Option.map, Bool.not_and]

@[scoped grind =]
theorem deMorgan_or (v : Var → Bool) (a b : Formula Var NCOp) :
    (Formula.not (Formula.or a b)).eval v =
    (Formula.and (Formula.not a) (Formula.not b)).eval v := by
  simp only [eval_not, eval_and, eval_or]
  cases a.eval v <;> cases b.eval v <;>
    simp [Option.bind, Option.map, Bool.not_or]

/-! ### Measure lemmas for standard constructors -/

@[simp, scoped grind =]
theorem size_and (a b : Formula Var NCOp) :
    (Formula.and a b).size = 1 + a.size + b.size := by
  simp [Formula.and, size, List.map, List.sum]; omega

@[simp, scoped grind =]
theorem size_or (a b : Formula Var NCOp) :
    (Formula.or a b).size = 1 + a.size + b.size := by
  simp [Formula.or, size, List.map, List.sum]; omega

@[simp, scoped grind =]
theorem size_not (a : Formula Var NCOp) :
    (Formula.not a).size = 1 + a.size := by
  simp [Formula.not, size, List.map, List.sum]

@[simp, scoped grind =]
theorem depth_and (a b : Formula Var NCOp) :
    (Formula.and a b).depth = 1 + max a.depth b.depth := by
  simp [Formula.and, depth, List.map, List.foldl, Nat.max_def]

@[simp, scoped grind =]
theorem depth_or (a b : Formula Var NCOp) :
    (Formula.or a b).depth = 1 + max a.depth b.depth := by
  simp [Formula.or, depth, List.map, List.foldl, Nat.max_def]

@[simp, scoped grind =]
theorem depth_not (a : Formula Var NCOp) :
    (Formula.not a).depth = 1 + a.depth := by
  simp [Formula.not, depth, List.map, List.foldl]

end Formula

end Cslib.Circuits
