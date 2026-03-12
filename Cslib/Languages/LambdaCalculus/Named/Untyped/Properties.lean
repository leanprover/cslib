/-
Copyright (c) 2026 Haoxuan Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haoxuan Yin
-/

module

public import Cslib.Languages.LambdaCalculus.Named.Untyped.Basic

public section

namespace Cslib

universe u

variable {Var : Type u}

namespace LambdaCalculus.Named

open Term

/-- A variable in a term is either free or bound. -/
lemma Term.vars_either_fv_or_bv [DecidableEq Var] {m : Term Var} :
    m.vars = m.fv ∪ m.bv := by
  induction m <;> grind [fv, bv, vars]

/-- Renaming an unused variable has no effect. -/
@[simp]
lemma Term.rename_unused [DecidableEq Var] {m : Term Var} {x y : Var} :
  x ∉ m.vars → m.rename x y = m := by
  induction m <;> grind [vars, rename]

/-- Renaming a variable to itself has no effect. -/
@[simp]
lemma Term.rename_same [DecidableEq Var] {m : Term Var} {x : Var} :
  m.rename x x = m := by
  induction m <;> grind [vars, rename]

/-- Renaming a used variable changes the set of variables. -/
@[simp]
lemma Term.rename_vars_used [DecidableEq Var] {m : Term Var} {x y : Var} :
  x ∈ m.vars → (m.rename x y).vars = m.vars.erase x ∪ {y} := by
  induction m with
  | var z => grind [vars, rename]
  | abs z m ih =>
    intro hx
    by_cases hxm : x ∈ m.vars <;> grind [vars, rename, rename_unused]
  | app m n ihm ihn =>
    intro hx
    by_cases hxm : x ∈ m.vars
    · by_cases hxn : x ∈ n.vars
      · grind [vars, rename]
      · grind [vars, rename, rename_unused]
    · have hxn : x ∈ n.vars := by
        grind [vars]
      grind [vars, rename, rename_unused]

/-- Renaming removes the variable. -/
lemma Term.rename_remove [DecidableEq Var] {m : Term Var} {x y : Var} :
  x ≠ y → x ∉ (m.rename x y).vars := by
  intro hxy
  by_cases hx : x ∈ m.vars <;> grind [rename_vars_used, rename_unused]

/-- Renaming changes set of variables. -/
lemma Term.rename_vars [DecidableEq Var] {m : Term Var} {x y : Var} :
  (m.rename x y).vars ⊆ m.vars \ {x} ∪ {y} := by
  by_cases x ∈ m.vars <;> grind [vars, rename, rename_unused, rename_vars_used]

/-- Concatenation of renaming. -/
@[simp]
lemma Term.rename_concat [DecidableEq Var] {m : Term Var} {x y z : Var} :
  y ∉ m.vars → (m.rename x y).rename y z = m.rename x z := by
  induction m <;> grind [vars, rename]

/-- Commutativity of renaming. -/
@[simp]
lemma Term.rename_comm [DecidableEq Var] {m : Term Var} {x y z w : Var} :
  x ≠ z → y ∉ m.vars ∪ {x, z} → w ∉ m.vars ∪ {x, z} →
  (m.rename x y).rename z w = (m.rename z w).rename x y := by
  induction m <;> grind [vars, rename]

/-- α-equivalent terms have the same size. -/
lemma AlphaEquiv.eq_sizeOf [DecidableEq Var] {m n : Term Var} :
  m =α n → sizeOf m = sizeOf n := by
  intro h
  induction h with
  | @var x => rfl
  | @abs y x1 x2 m1 m2 hy h ih =>
    simpa using ih
  | @app m1 n1 m2 n2 _ hm hn =>
    grind [app.sizeOf_spec]

/-- Reflexivity of α-equivalence. -/
lemma AlphaEquiv.refl [DecidableEq Var] [HasFresh Var] (m : Term Var) : m =α m := by
  refine WellFounded.induction (C := fun m => m =α m) sizeOfWFRel.wf m ?_
  simp only; intro m ih
  cases m with
  | var x => apply AlphaEquiv.var
  | abs x m =>
    obtain ⟨z, hz⟩ := HasFresh.fresh_exists (m.vars ∪ {x})
    apply AlphaEquiv.abs (y := z) (x1 := x) (x2 := x) (m1 := m) (m2 := m)
    <;> try grind [rename_unused, rename_vars, rename_concat]
    · apply ih
      change sizeOf (m.rename x z) < sizeOf (abs x m)
      grind [rename.eq_sizeOf, abs.sizeOf_spec]
  | app m n =>
    apply AlphaEquiv.app
    · apply ih
      change sizeOf m < sizeOf (app m n)
      grind [rename.eq_sizeOf, app.sizeOf_spec]
    · apply ih
      change sizeOf n < sizeOf (app m n)
      grind [rename.eq_sizeOf, app.sizeOf_spec]

/-- Symmetry of α-equivalence. -/
lemma AlphaEquiv.symm [DecidableEq Var] [HasFresh Var] {m n : Term Var} :
  m =α n → n =α m := by
  intro h
  induction h with
  | @var x => apply AlphaEquiv.var
  | @abs y x1 x2 m1 m2 hy h ih =>
    apply AlphaEquiv.abs (y := y) (x1 := x2) (x2 := x1) (m1 := m2) (m2 := m1)
    <;> try grind [rename_unused, rename_vars, rename_concat]
    · apply ih
  | @app m1 n1 m2 n2 hwm1 hwn1 hwm2 hwn2 =>
    apply AlphaEquiv.app <;> assumption

/-- Renaming under an abstraction body can be reordered against the outer renaming.
    This lemma is used for the lemma below. -/
lemma Term.rename_abs_body_comm [DecidableEq Var] {m : Term Var} {x y z w : Var} :
  y ∉ m.vars ∪ {x, z} → w ∉ m.vars ∪ {x, y, z} →
  (m.rename x y).rename (if z = x then y else z) w = (m.rename z w).rename x y := by
  intro hy hw
  by_cases hzx : z = x
  · grind [rename_same, rename_unused, rename_concat, rename_vars]
  · grind [rename_comm]

/-- Renaming α-equivalent terms produces α-equivalent terms. -/
lemma AlphaEquiv.rename_preserve [DecidableEq Var] [HasFresh Var]
  (m n : Term Var) (x y : Var) :
  y ∉ m.vars ∪ n.vars → m =α n → (m.rename x y) =α (n.rename x y) := by
  refine (WellFounded.induction sizeOfWFRel.wf m
    (C := fun m => ∀ (n : Term Var) (x y : Var), y ∉ m.vars ∪ n.vars →
      m =α n → (m.rename x y) =α (n.rename x y)) ?_) n x y
  intro m ih n x y hy h
  by_cases hxy : y = x
  · grind [rename_same]
  cases h with
  | @var z => apply AlphaEquiv.refl
  | @abs z x1 x2 m1 m2 hz hbody =>
    obtain ⟨w, hw⟩ := HasFresh.fresh_exists (m1.vars ∪ m2.vars ∪ {x1, x2, x, y, z})
    apply AlphaEquiv.abs (y := w) <;> try grind [rename_vars]
    rw [rename_abs_body_comm, rename_abs_body_comm] <;> try grind [vars]
    apply ih <;> try grind [vars, rename_vars]
    · change sizeOf (m1.rename x1 w) < sizeOf (abs x1 m1)
      grind [rename.eq_sizeOf, abs.sizeOf_spec]
    · have hxzw : ((m1.rename x1 z).rename z w) =α ((m2.rename x2 z).rename z w) := by
        apply ih <;> try grind [vars, rename_vars]
        · change sizeOf (m1.rename x1 z) < sizeOf (abs x1 m1)
          grind [rename.eq_sizeOf, abs.sizeOf_spec]
        · assumption
      grind [rename_concat]
  | @app m1 n1 m2 n2 hm hn =>
    apply AlphaEquiv.app
    · apply ih m1 <;> try grind [vars]
      · change sizeOf m1 < sizeOf (app m1 m2)
        grind [app.sizeOf_spec]
      · assumption
    · apply ih m2 <;> try grind [vars]
      · change sizeOf m2 < sizeOf (app m1 m2)
        grind [app.sizeOf_spec]
      · assumption

/-- Elimination rule for α-equivalence of abstractions.
    It states that if two abstractions are α-equivalent,
    then their bodies can be renamed to ``any'' fresh variable y and remain α-equivalent.
    This is sometimes easier to use than using by_cases on the equivalence,
    which can only produce the claim for ``some'' fresh y. -/
lemma AlphaEquiv.abs_elim [DecidableEq Var] [HasFresh Var] {m1 m2 : Term Var} {x1 x2 y : Var} :
  y ∉ m1.vars ∪ m2.vars ∪ {x1, x2} → (abs x1 m1) =α (abs x2 m2) →
  (m1.rename x1 y) =α (m2.rename x2 y) := by
  intro hy h
  cases h with
  | @abs z _ _ _ _ hz h1 =>
    by_cases hzy : z = y
    · subst z
      assumption
    · have hxzy : ((m1.rename x1 z).rename z y) =α ((m2.rename x2 z).rename z y) := by
        apply AlphaEquiv.rename_preserve <;> try grind [AlphaEquiv.rename_preserve, rename_vars]
        assumption
      grind [rename_concat, rename_vars]

/-- Transitivity of α-equivalence. -/
lemma AlphaEquiv.trans [DecidableEq Var] [HasFresh Var] {m n p : Term Var} :
  m =α n → n =α p → m =α p := by
  refine (WellFounded.induction sizeOfWFRel.wf m
    (C := fun m => ∀ (n p : Term Var),
      m =α n → n =α p → m =α p) ?_) n p
  intro m ih n p hmn hnp
  cases m with
  | var x =>
    cases hmn with
    | @var x => assumption
  | abs x1 m1 =>
    obtain ⟨w, hw⟩ := HasFresh.fresh_exists (m1.vars ∪ {x1} ∪ n.vars ∪ p.vars)
    have hmn' := hmn
    cases hmn' with
    | @abs y x1 x2 m1 m2 hy h1 =>
      have hnp' := hnp
      cases hnp' with
      | @abs z x2 x3 m2 m3 hz h2 =>
        apply AlphaEquiv.abs (y := w)
        <;> try grind [vars, rename_unused, rename_vars, rename_concat]
        · apply ih _ ?_ (m2.rename x2 w) <;> try grind [AlphaEquiv.abs_elim, vars, rename_vars]
          change sizeOf (m1.rename x1 w) < sizeOf (abs x1 m1)
          grind [rename.eq_sizeOf, abs.sizeOf_spec]
  | app m1 m2 =>
    cases hmn with
    | @app m1 n1 m2 n2 hmn1 hmn2 =>
      cases hnp with
      | @app n1 p1 n2 p2 hnp1 hnp2 =>
        apply AlphaEquiv.app
        · apply ih _ ?_ n1 <;> try assumption; try grind [vars, rename_vars]
          change sizeOf m1 < sizeOf (app m1 m2)
          grind [app.sizeOf_spec]
        · apply ih _ ?_ n2 <;> try assumption; try grind [vars, rename_vars]
          change sizeOf m2 < sizeOf (app m1 m2)
          grind [app.sizeOf_spec]

/-- Renaming a non-free variable result in an α-equivalent term. -/
lemma AlphaEquiv.rename_non_fv [DecidableEq Var] [HasFresh Var] (m : Term Var) (x y : Var)
  (hxm : x ∉ m.fv) (hym : y ∉ m.vars) : m =α (m.rename x y) := by
  induction m with
  | var z =>
    have hzx : z ≠ x := by
      grind [fv]
    simpa [rename, hzx] using AlphaEquiv.var
  | abs z m ih =>
    by_cases hzx : z = x
    · subst z
      simp only [rename, ↓reduceIte]
      obtain ⟨w, hw⟩ := HasFresh.fresh_exists (m.vars ∪ {x, y})
      apply AlphaEquiv.abs (y := w)<;> try grind [rename_unused, rename_vars]
      rw [rename_concat] <;> try grind [vars]
      apply AlphaEquiv.refl
    · simp only [rename, hzx, ↓reduceIte]
      obtain ⟨w, hw⟩ := HasFresh.fresh_exists (m.vars ∪ {x, y, z})
      apply AlphaEquiv.abs (y := w) <;> try grind [rename_unused, rename_vars]
      apply AlphaEquiv.rename_preserve <;> grind [vars, rename_vars, fv]
  | app m1 m2 ih1 ih2 =>
    apply AlphaEquiv.app
    · apply ih1 <;> grind [vars, fv]
    · apply ih2 <;> grind [vars, fv]

/-- Any `Term` can be obtained by filling a `Context` with a variable. This proves that `Context`
completely captures the syntax of terms. -/
theorem Context.complete (m : Term Var) :
    ∃ (c : Context Var) (x : Var), m = (c.fill (Term.var x)) := by
  induction m with
  | var x => exists hole, x
  | abs x n ih =>
    obtain ⟨c', y, ih⟩ := ih
    exists Context.abs x c', y
    rw [ih, fill]
  | app n₁ n₂ ih₁ ih₂ =>
    obtain ⟨c₁, x₁, ih₁⟩ := ih₁
    exists Context.appL c₁ n₂, x₁
    rw [ih₁, fill]


end LambdaCalculus.Named

end Cslib
