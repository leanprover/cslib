/-
Copyright (c) 2026 Haoxuan Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haoxuan Yin, Fabrizio Montesi
-/

module

public import Cslib.Languages.LambdaCalculus.Named.Untyped.Basic

public section

namespace Cslib

universe u

variable {Var : Type u} [DecidableEq Var]

namespace LambdaCalculus.Named.Untyped.Term

/-- A variable in a term is either free or bound. -/
theorem vars_either_fv_or_bv {m : Term Var} :
    m.vars = m.fv ∪ m.bv := by
  induction m <;> grind [fv, bv, vars]

/-- Renaming an unused variable has no effect. -/
@[simp]
theorem rename_unused {m : Term Var} {x y : Var} :
  x ∉ m.vars → m.rename x y = m := by
  induction m <;> grind [vars, rename]

/-- Renaming a variable to itself has no effect. -/
@[simp]
theorem rename_same {m : Term Var} {x : Var} :
  m.rename x x = m := by
  induction m <;> grind [vars, rename]

/-- Renaming a used variable changes the set of variables. -/
@[simp]
theorem rename_vars_used {m : Term Var} {x y : Var} :
  x ∈ m.vars → (m.rename x y).vars = m.vars.erase x ∪ {y} := by
  induction m with
  | var z => grind [vars, rename]
  | abs z m ih =>
    intro hx
    by_cases hxm : x ∈ m.vars <;> grind [vars, rename, rename_unused]
  | app m n ihm ihn =>
    intro hx
    by_cases hxm : x ∈ m.vars
    · by_cases hxn : x ∈ n.vars <;> grind [vars, rename, rename_unused]
    · have hxn : x ∈ n.vars := by grind [vars]
      grind [vars, rename, rename_unused]

/-- Renaming removes the variable. -/
theorem rename_remove {m : Term Var} {x y : Var} :
  x ≠ y → x ∉ (m.rename x y).vars := by
  intro hxy
  by_cases hx : x ∈ m.vars <;> grind [rename_vars_used, rename_unused]

/-- The set of variables after renaming. -/
theorem rename_vars {m : Term Var} {x y : Var} :
  (m.rename x y).vars = m.vars \ {x} ∪ (if x ∈ m.vars then {y} else ∅) := by
  by_cases x ∈ m.vars <;> grind [vars, rename, rename_unused, rename_vars_used]

/-- The set of free variables after renaming. -/
theorem rename_fv {m : Term Var} {x y : Var} :
  y ∉ m.vars → (m.rename x y).fv = m.fv \ {x} ∪ (if x ∈ m.fv then {y} else ∅) := by
  induction m <;> grind [fv, vars, rename, vars_either_fv_or_bv]

/-- Concatenation of renaming. -/
@[simp]
theorem rename_concat {m : Term Var} {x y z : Var} :
  y ∉ m.vars → (m.rename x y).rename y z = m.rename x z := by
  induction m <;> grind [vars, rename]

/-- Commutativity of renaming, simpler version. -/
theorem rename_comm {m : Term Var} {x y z w : Var} :
  x ≠ z → y ∉ m.vars ∪ {x, z} → w ∉ m.vars ∪ {x, z} →
  (m.rename x y).rename z w = (m.rename z w).rename x y := by
  induction m <;> grind [vars, rename]

/-- Commutativity of renaming, more general version. -/
theorem rename_comm2 {m : Term Var} {x y z w : Var} :
    y ∉ m.vars ∪ {x, z} → w ∉ m.vars ∪ {x, y, z} →
    (m.rename x y).rename (if z = x then y else z) w = (m.rename z w).rename x y := by
  intro hy hw
  by_cases hzx : z = x
  · grind [rename_same, rename_unused, rename_concat, rename_vars]
  · grind [rename_comm]

omit [DecidableEq Var] in
@[grind norm↓← ]
lemma induction_by_sizeOf {m n : Term Var} : sizeOf m < sizeOf n ↔ WellFoundedRelation.rel m n := by
  rfl

/-- α-equivalent terms have the same size. -/
theorem AlphaEquiv.eq_sizeOf {m n : Term Var} : m =α n → sizeOf m = sizeOf n := by
  intro h
  induction h with
  | @var x => rfl
  | @abs y x1 x2 m1 m2 hy h ih =>
    simpa using ih
  | @app m1 n1 m2 n2 _ hm hn =>
    grind

/-- α-equivalent terms have the same free variables. -/
theorem AlphaEquiv.same_fv {m n : Term Var} : m =α n → m.fv = n.fv := by
  intro h
  induction h with
  | @var x => rfl
  | @abs y x1 x2 m1 m2 hy h ih =>
    rw [Term.fv, Term.fv]
    have h1 : m1.fv \ {x1} = (m1.rename x1 y).fv \ {y} := by
      grind [rename_fv, vars_either_fv_or_bv]
    have h2 : (m2.rename x2 y).fv \ {y} = m2.fv \ {x2} := by
      grind [rename_fv, vars_either_fv_or_bv]
    grind
  | @app m1 n1 m2 n2 h1 h2 ih1 ih2 => grind [Term.fv]

variable [HasFresh Var]

/-- Reflexivity of α-equivalence. -/
theorem AlphaEquiv.refl (m : Term Var) : m =α m := by
  refine WellFounded.induction (C := fun m => m =α m) sizeOfWFRel.wf m ?_
  simp only; intro m ih
  cases m with
  | var x => apply AlphaEquiv.var
  | abs x m =>
    obtain ⟨z, hz⟩ := HasFresh.fresh_exists (m.vars ∪ {x})
    apply AlphaEquiv.abs (y := z)
    · grind [rename_vars]
    apply ih
    -- rw [← induction_by_sizeOf]
    grind [rename_eq_sizeOf]
  | app m n =>
    apply AlphaEquiv.app <;> apply ih <;> grind

omit [HasFresh Var] in
/-- Symmetry of α-equivalence. -/
theorem AlphaEquiv.symm {m n : Term Var} : m =α n → n =α m := by
  intro h
  induction h with
  | @var x => apply AlphaEquiv.var
  | @abs y x1 x2 m1 m2 hy h ih =>
    apply AlphaEquiv.abs (y := y) <;> grind [rename_unused, rename_vars, rename_concat]
  | @app m1 n1 m2 n2 hwm1 hwn1 hwm2 hwn2 =>
    apply AlphaEquiv.app <;> assumption

/-- Renaming α-equivalent terms produces α-equivalent terms. -/
theorem AlphaEquiv.rename_preserve (m n : Term Var) (x y : Var) :
    y ∉ m.vars ∪ n.vars → m =α n → (m.rename x y) =α (n.rename x y) := by
  refine (WellFounded.induction sizeOfWFRel.wf m
    (C := fun m => ∀ (n : Term Var) (x y : Var), y ∉ m.vars ∪ n.vars →
      m =α n → (m.rename x y) =α (n.rename x y)) ?_) n x y
  intro m ih n x y hy h
  by_cases hyx : y = x
  · grind [rename_same]
  cases h with
  | @var z => apply AlphaEquiv.refl
  | @abs z x1 x2 m1 m2 hz hbody =>
    obtain ⟨w, hw⟩ := HasFresh.fresh_exists (m1.vars ∪ m2.vars ∪ {x1, x2, x, y, z})
    apply AlphaEquiv.abs (y := w)
    · grind [rename_vars]
    rw [rename_comm2, rename_comm2]
    case neg.abs.a =>
      apply ih
      · grind [rename_eq_sizeOf]
      · grind [vars, rename_vars]
      · have hxzw : ((m1.rename x1 z).rename z w) =α ((m2.rename x2 z).rename z w) := by
          apply ih <;> grind [vars, rename_vars, rename_eq_sizeOf]
        grind [rename_concat]
    all_goals grind [vars]
  | @app m1 n1 m2 n2 hm hn =>
    apply AlphaEquiv.app <;> apply ih <;> grind [vars]

/-- Elimination rule for α-equivalence of abstractions.
    It states that if two abstractions are α-equivalent,
    then their bodies can be renamed to ``any'' fresh variable y and remain α-equivalent.
    This is sometimes easier to use than using by_cases on the equivalence,
    which can only produce the claim for ``some'' fresh y. -/
theorem AlphaEquiv.abs_elim {m1 m2 : Term Var} {x1 x2 y : Var} :
    y ∉ m1.vars ∪ m2.vars ∪ {x1, x2} → (Term.abs x1 m1) =α (Term.abs x2 m2) →
    (m1.rename x1 y) =α (m2.rename x2 y) := by
  intro hy h
  cases h with
  | @abs z _ _ _ _ hz h1 =>
    by_cases hzy : z = y
    · grind
    · have hxzy : ((m1.rename x1 z).rename z y) =α ((m2.rename x2 z).rename z y) := by
        apply AlphaEquiv.rename_preserve <;> grind [AlphaEquiv.rename_preserve, rename_vars]
      grind [rename_concat, rename_vars]

/-- Transitivity of α-equivalence. -/
theorem AlphaEquiv.trans {m n p : Term Var} :
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
        · grind [vars, rename_unused, rename_vars, rename_concat]
        apply ih _ ?_ (m2.rename x2 w) <;>
        grind [AlphaEquiv.abs_elim, vars, rename_vars, rename_eq_sizeOf]
  | app m1 m2 =>
    cases hmn with
    | @app m1 n1 m2 n2 hmn1 hmn2 =>
      cases hnp with
      | @app n1 p1 n2 p2 hnp1 hnp2 =>
        apply AlphaEquiv.app
        · apply ih _ ?_ n1 <;> grind [vars, rename_vars]
        · apply ih _ ?_ n2 <;> grind [vars, rename_vars]

/-- Renaming a non-free variable results in an α-equivalent term -/
theorem AlphaEquiv.rename_non_fv {m : Term Var} {x y : Var} :
    x ∉ m.fv → y ∉ m.vars → m =α (m.rename x y) := by
  intro hx hy
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
      apply AlphaEquiv.abs (y := w)
      · grind [rename_unused, rename_vars]
      rw [rename_concat] <;> grind [vars, AlphaEquiv.refl]
    · simp only [rename, hzx, ↓reduceIte]
      obtain ⟨w, hw⟩ := HasFresh.fresh_exists (m.vars ∪ {x, y, z})
      apply AlphaEquiv.abs (y := w)
      · grind [rename_unused, rename_vars]
      apply AlphaEquiv.rename_preserve <;> grind [vars, rename_vars, fv]
  | app m1 m2 ih1 ih2 =>
    apply AlphaEquiv.app
    · apply ih1 <;> grind [vars, fv]
    · apply ih2 <;> grind [vars, fv]

/-- Abstracting over an arbitrary non-free variable results in the same term,
    modulo α-equivalence. -/
theorem AlphaEquiv.abs_non_fv {m1 m2 : Term Var} {x1 x2 : Var} :
    m1 =α m2 → x1 ∉ m1.fv → x2 ∉ m2.fv → (Term.abs x1 m1) =α (Term.abs x2 m2) := by
  intro hm hx1 hx2
  obtain ⟨y, hy⟩ := HasFresh.fresh_exists (m1.vars ∪ m2.vars ∪ {x1, x2})
  apply AlphaEquiv.abs (y := y)
  · grind
  apply AlphaEquiv.trans (n := m1)
  · grind [rename_non_fv, AlphaEquiv.symm]
  apply AlphaEquiv.trans (n := m2) <;> grind [rename_non_fv]

/-- Renaming an abstraction leads to an α-equivalent term. -/
theorem AlphaEquiv.abs_rename {m : Term Var} {x y : Var} :
    y ∉ m.vars ∪ {x} → (Term.abs x m) =α (Term.abs y (m.rename x y)) := by
  intro hy
  obtain ⟨z, hz⟩ := HasFresh.fresh_exists (m.vars ∪ {x, y})
  apply AlphaEquiv.abs (y := z) <;> grind [vars, rename_vars, rename_concat, AlphaEquiv.refl]

omit [DecidableEq Var] [HasFresh Var] in
/-- Any `Term` can be obtained by filling a `Context` with a variable. This proves that `Context`
completely captures the syntax of terms. -/
theorem Context.complete (m : Term Var) :
    ∃ (c : Context Var) (x : Var), m = (c.fill (var x)) := by
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

omit [HasFresh Var] in
/-- The set of variables after filling a context. -/
theorem Context.fill_vars {c : Context Var} {m : Term Var} :
    (c.fill m).vars = c.vars ∪ m.vars := by
  induction c <;> grind [Context.fill, Context.vars, Term.vars]

/-- α-equivalence is preserved under context filling. -/
theorem AlphaEquiv.context {m n : Term Var} {c : Context Var} :
    m =α n → (c.fill m) =α (c.fill n) := by
  intro h
  induction c with
  | hole => assumption
  | abs x c ih =>
    simp only [Context.fill]
    obtain ⟨y, hy⟩ := HasFresh.fresh_exists (m.vars ∪ n.vars ∪ c.vars ∪ {x})
    apply AlphaEquiv.abs (y := y) <;> grind [Context.fill_vars, rename_preserve]
  | appL c m ih =>
    apply AlphaEquiv.app <;> grind [AlphaEquiv.app, AlphaEquiv.refl, vars]
  | appR m c ih =>
    apply AlphaEquiv.app <;> grind [AlphaEquiv.app, AlphaEquiv.refl, vars]

/-- The functional definition of substitution satisfies the relational definition of substitution.
-/
theorem Subst.function_to_relation {m r : Term Var} {x : Var} :
    m.Subst x r (m[x := r]) := by
  refine WellFounded.induction (C := fun m => m.Subst x r (m[x := r])) sizeOfWFRel.wf m ?_
  simp only; intro m ih
  cases m with
  | var y =>
    by_cases hyx : y = x
    · subst y
      simp only [← subst_def, subst.eq_1, ↓reduceIte]
      apply Subst.varHit
    · simp [hyx, ← subst_def]
      grind [Subst.varMiss]
  | abs y m =>
    by_cases hyx : y = x
    · subst y
      simp only [← subst_def, subst.eq_2, ↓reduceIte]
      apply Subst.absShadow
    · simp only [← subst_def, subst.eq_2, hyx, ↓reduceIte, Finset.union_insert]
      by_cases hyr : y ∈ r.fv
      · simp only [hyr]
        have hz := fresh_notMem (insert x (insert y (m.vars ∪ r.vars)))
        set z := fresh (insert x (insert y (m.vars ∪ r.vars)))
        apply Subst.alpha (m := abs z (m.rename y z)) (r := r) (n := abs z ((m.rename y z)[x := r]))
        · have h1 : abs z (m.rename y z) = (abs y m).rename y z := by
            simp [rename]
          grind [AlphaEquiv.symm, AlphaEquiv.rename_non_fv, vars, fv]
        · grind [AlphaEquiv.refl]
        · grind [AlphaEquiv.refl]
        · apply Subst.absIn
          · grind [vars, fv, vars_either_fv_or_bv]
          apply ih
          grind [rename_eq_sizeOf]
      · simp only [hyr]
        apply Subst.absIn
        · grind [vars, fv, vars_either_fv_or_bv]
        apply ih
        grind
  | app m1 m2 =>
    simp only [← subst_def, subst.eq_3]
    apply Subst.app <;> apply ih <;> grind

/-- Substituting a non-free variable has no effect. -/
theorem subst.non_free {m r : Term Var} {x : Var} :
    x ∉ m.fv → (m[x := r]) =α m := by
  refine WellFounded.induction (C := fun m => x ∉ m.fv → (m[x := r]) =α m) sizeOfWFRel.wf m ?_
  simp only; intro m ih hx
  cases m with
  | var y =>
    have hyx : y ≠ x := by
      grind [fv]
    simp only [← subst_def, subst.eq_1, hyx, ↓reduceIte]
    apply AlphaEquiv.var
  | abs y m =>
    by_cases hyx : y = x
    · subst y
      simp only [← subst_def, subst.eq_2, ↓reduceIte]
      apply AlphaEquiv.refl
    · by_cases hyr : y ∈ r.fv
      · simp only [← subst_def, subst.eq_2, hyx, ↓reduceIte, hyr, not_true_eq_false,
          Finset.union_insert, Finset.union_singleton]
        have hz := fresh_notMem (insert x (insert y (m.vars ∪ r.vars)))
        set z := fresh (insert x (insert y (m.vars ∪ r.vars)))
        obtain ⟨w, hw⟩ := HasFresh.fresh_exists (m.vars ∪ r.vars ∪ ((m.rename y z).subst x r).vars
          ∪ {x, y, z})
        apply AlphaEquiv.abs (y := w)
        · grind [vars, rename_unused, rename_vars]
        apply AlphaEquiv.trans (n := ((m.rename y z).rename z w))
        · apply AlphaEquiv.rename_preserve
          · grind [vars, rename_vars, fv]
          apply ih <;> grind [fv, rename_fv, rename_eq_sizeOf]
        · grind [rename_concat, AlphaEquiv.refl]
      · simp only [← subst_def, subst.eq_2, hyx, ↓reduceIte, hyr, not_false_eq_true]
        apply AlphaEquiv.context (c := Context.abs y Context.hole)
        apply ih <;> grind [fv]
  | app m1 m2 =>
    simp only [← subst_def, subst.eq_3]
    apply AlphaEquiv.app <;> apply ih <;> grind [fv]

lemma subst.abs_fresh_helper {m r : Term Var} {x y z : Var} :
    z ∉ m.vars ∪ r.vars ∪ {x, y} →
    ((Term.abs y m)[x := r]) =α (Term.abs z ((m.rename y z)[x := r]))
    ∧ (y ∉ r.fv ∪ {x} → (Term.abs y (m[x := r])) =α (Term.abs z ((m.rename y z)[x := r]))) := by
  refine (WellFounded.induction sizeOfWFRel.wf m
    (C := fun m => ∀ (r : Term Var) (x y z : Var),
    z ∉ m.vars ∪ r.vars ∪ {x, y} →
    ((Term.abs y m)[x := r]) =α (Term.abs z ((m.rename y z)[x := r]))
    ∧ (y ∉ r.fv ∪ {x} → (Term.abs y (m[x := r])) =α (Term.abs z ((m.rename y z)[x := r])))) ?_)
    r x y z
  intro m ih r x y z hz
  have hright : ∀ (m' : Term Var) (y' : Var), sizeOf m' = sizeOf m → z ∉ m'.vars ∪ r.vars ∪ {x, y'}
    → y' ∉ r.fv ∪ {x} → (Term.abs y' (m'[x:=r])) =α (Term.abs z ((m'.rename y' z)[x:=r])) := by
    intro m' y' hm' hz hy'
    cases m' with
    | var w =>
      by_cases hwx : w = x
      · subst w
        have hxy' : x ≠ y' := by grind
        rw [rename]
        simp only [← subst_def, subst.eq_1, ↓reduceIte, hxy']
        apply AlphaEquiv.abs_non_fv <;> grind [vars_either_fv_or_bv, AlphaEquiv.refl]
      · simp only [← subst_def, subst.eq_1, hwx, ↓reduceIte]
        rw [rename]
        by_cases hwy' : w = y'
        · subst w
          have hzx : z ≠ x := by grind
          simp only [↓reduceIte, subst.eq_1, hzx]
          obtain ⟨v, hv⟩ := HasFresh.fresh_exists ({y', z})
          apply AlphaEquiv.abs (y := v) <;> grind [vars, rename, AlphaEquiv.var]
        · simp only [hwy', ↓reduceIte, subst.eq_1, hwx]
          apply AlphaEquiv.abs_non_fv <;> grind [vars_either_fv_or_bv, AlphaEquiv.refl, Term.fv]
    | app m1 m2 =>
      obtain ⟨w, hw⟩ := HasFresh.fresh_exists
        ((m1.app m2)[x := r].vars ∪ (((m1.app m2).rename y' z)[x := r]).vars
        ∪ m1[x := r].vars ∪ m2[x := r].vars ∪ (m1.rename y' z)[x := r].vars
        ∪ (m2.rename y' z)[x := r].vars ∪ {y', z})
      apply AlphaEquiv.abs (y := w)
      · grind
      simp only [← subst_def, subst.eq_3, rename]
      apply AlphaEquiv.app <;> apply AlphaEquiv.abs_elim <;> grind [vars, rename_vars]
    | abs w m1 =>
      by_cases hwy' : w = y'
      · subst w
        rw [rename]
        have hy'x : y' ≠ x := by grind
        have hy'r : y' ∉ r.fv := by grind
        have hzx : z ≠ x := by grind
        have hzr : z ∉ r.fv := by grind [vars_either_fv_or_bv]
        simp only [← subst_def, subst.eq_2, hy'x, ↓reduceIte, hy'r, not_false_eq_true, hzx, hzr]
        apply AlphaEquiv.abs_non_fv
        · apply (ih _ _ _ _ _ _ _).right <;> grind [vars]
        · grind [fv]
        · grind [fv]
      · rw [rename]
        simp only [hwy', ↓reduceIte]
        by_cases hwx : w = x
        · subst w
          simp only [← subst_def, subst, ↓reduceIte]
          apply AlphaEquiv.trans (n := Term.abs z ((Term.abs x m1).rename y' z))
          · grind [AlphaEquiv.abs_rename]
          · grind [rename, AlphaEquiv.refl]
        · by_cases hwr : w ∈ r.fv
          · obtain ⟨v, hv⟩ := HasFresh.fresh_exists (m1.vars ∪ r.vars ∪ {x, y', z, w})
            have hl : (Term.abs y' (((Term.abs w m1)[x := r]))) =α
                (Term.abs y' (Term.abs v ((m1.rename w v)[x := r]))) := by
              apply AlphaEquiv.context (c := Context.abs y' Context.hole)
              apply (ih _ _ _ _ _ _ _).left <;> grind
            have hr : (Term.abs z (Term.abs v (((m1.rename y' z).rename w v)[x := r])))
              =α (Term.abs z ((Term.abs w (m1.rename y' z))[x := r])) := by
              apply AlphaEquiv.context (c := Context.abs z Context.hole)
              apply AlphaEquiv.symm
              apply (ih _ _ _ _ _ _ _).left <;> grind [rename_vars, rename_eq_sizeOf]
            have hmid : (Term.abs y' (Term.abs v ((m1.rename w v)[x := r]))) =α
                (Term.abs z (Term.abs v (((m1.rename y' z).rename w v)[x := r]))) := by
              obtain ⟨u, hu⟩ := HasFresh.fresh_exists
                ((Term.abs v ((m1.rename w v)[x := r])).vars ∪
                (Term.abs v (((m1.rename y' z).rename w v)[x := r])).vars ∪
                ((m1.rename w v).rename y' z)[x:=r].vars ∪ {y', z})
              apply AlphaEquiv.abs (y := u)
              · grind
              · have hvy' : v ≠ y' := by grind
                have hvz : v ≠ z := by grind
                simp only [rename, hvy', hvz, ↓reduceIte]
                apply AlphaEquiv.context (c := Context.abs v Context.hole)
                apply AlphaEquiv.trans (n := (((m1.rename w v).rename y' z)[x := r]).rename z u)
                · apply AlphaEquiv.abs_elim
                  · grind  [vars]
                  · apply (ih _ _ _ _ _ _ _).right <;> grind [vars, rename_vars, rename_eq_sizeOf]
                · apply AlphaEquiv.rename_preserve
                  · grind [vars]
                  · rw [rename_comm] <;> grind [vars, AlphaEquiv.refl]
            exact AlphaEquiv.trans hl <| AlphaEquiv.trans hmid hr
          · obtain ⟨v, hv⟩ := HasFresh.fresh_exists
              (m1[x:=r].vars ∪ (m1.rename y' z)[x:=r].vars ∪ ((Term.abs w m1)[x := r]).vars ∪
              ((Term.abs w (m1.rename y' z))[x := r]).vars ∪ {y', z})
            apply AlphaEquiv.abs (y := v)
            · grind [vars, rename_vars]
            · have hwz : w ≠ z := by grind [vars]
              simp only [← subst_def, subst, hwx, ↓reduceIte, hwr, not_false_eq_true, rename, hwy',
                hwz]
              apply AlphaEquiv.context (c := Context.abs w Context.hole)
              apply AlphaEquiv.abs_elim <;> grind [vars]
  have hleft : ((Term.abs y m)[x:=r]) =α (Term.abs z ((m.rename y z)[x:=r])) := by
    by_cases hyx : y = x
    · subst y
      simp only [← subst_def, subst.eq_2, ↓reduceIte]
      obtain ⟨w, hw⟩ := HasFresh.fresh_exists (m.vars ∪ r.vars ∪ ((m.rename x z).subst x r).vars ∪
        {x, z})
      apply AlphaEquiv.abs (y := w)
      · grind [vars, rename_unused, rename_vars]
      · apply AlphaEquiv.trans (n := ((m.rename x z).rename z w))
        · grind [AlphaEquiv.refl, rename_concat]
        · apply AlphaEquiv.rename_preserve
          · grind [rename_vars]
          · apply AlphaEquiv.symm
            apply subst.non_free
            grind [fv, rename_fv, rename_eq_sizeOf]
    · by_cases hyr : y ∈ r.fv
      · simp only [← subst_def, subst.eq_2, hyx, ↓reduceIte, hyr, not_true_eq_false,
          Finset.union_insert, Finset.union_singleton]
        have hw := fresh_notMem (insert x (insert y (m.vars ∪ r.vars)))
        set w := fresh (insert x (insert y (m.vars ∪ r.vars)))
        by_cases hzw' : z = w
        · subst z
          apply AlphaEquiv.refl
        · apply AlphaEquiv.trans (n := (Term.abs z (((m.rename y w).rename w z)[x := r])))
          · apply hright <;>
              grind [rename_eq_sizeOf, vars_either_fv_or_bv, rename_vars]
          · rw [rename_concat] <;> grind [AlphaEquiv.refl]
      · simp only [← subst_def, subst.eq_2, hyx, ↓reduceIte, hyr, not_false_eq_true]
        apply hright <;> grind
  exact ⟨hleft, hright m y (by rfl) (by grind)⟩

/-- Modulo α-equivalence, substituting an abstraction falls back to the fresh variable case only.
    With this lemma, the three cases in the definition of subst can be reduced to one.
-/
theorem subst.abs_fresh {m r : Term Var} {x y z : Var} :
    z ∉ m.vars ∪ r.vars ∪ {x, y} →
    ((Term.abs y m)[x := r]) =α (Term.abs z ((m.rename y z)[x := r])) := by
  grind [subst.abs_fresh_helper]

/-- Substituting α-equivalent terms produces α-equivalent terms. -/
theorem subst.preserve_AlphaEquiv {m m' r r' : Term Var} {x : Var} :
    m =α m' → r =α r' → (m[x := r]) =α (m'[x := r']) := by
  refine (WellFounded.induction sizeOfWFRel.wf m
    (C := fun m => ∀ (m' r r' : Term Var) (x : Var),
      m =α m' → r =α r' → (m[x := r]) =α (m'[x := r'])) ?_) m' r r' x
  intro m ih m' r r' x hmm' hrr'
  have hmm'' := hmm'
  cases hmm'' with
  | @var y =>
    by_cases hyx : y = x
    · simp only [← subst_def, subst, ↓reduceIte, hyx]
      assumption
    · simp only [← subst_def, subst, hyx]
      apply AlphaEquiv.refl
  | @abs z y y' m m' hz h1 =>
    obtain ⟨w, hw⟩ := HasFresh.fresh_exists (m.vars ∪ m'.vars ∪ r.vars ∪ r'.vars ∪ {x, y, y'})
    have h2 : ((Term.abs y m)[x := r]) =α (Term.abs w ((m.rename y w)[x := r])) := by
      grind [subst.abs_fresh]
    have h2' : ((Term.abs y' m')[x := r']) =α
        (Term.abs w ((m'.rename y' w)[x := r'])) := by
      grind [subst.abs_fresh]
    have hbody : (m.rename y w) =α (m'.rename y' w) := by
      apply AlphaEquiv.abs_elim <;> grind
    have h3 :
        (Term.abs w ((m.rename y w)[x := r])) =α (Term.abs w ((m'.rename y' w)[x := r'])) := by
      apply AlphaEquiv.context (c := Context.abs w Context.hole)
      apply ih <;> grind [rename_eq_sizeOf]
    apply AlphaEquiv.trans (n := (Term.abs w ((m.rename y w)[x := r]))) <;> try assumption
    apply AlphaEquiv.trans (n := (Term.abs w ((m'.rename y' w)[x := r']))) <;> try assumption
    apply AlphaEquiv.symm
    assumption
  | @app m m' n n' hm hn =>
    simp only [← subst_def, subst]
    apply AlphaEquiv.app <;> apply ih <;> grind

/-- The relational definition of substitution coincides with the functional definition of
    substitution, modulo α-equivalence. -/
theorem Subst.relation_iff_function {m n r : Term Var} {x : Var} :
    m.Subst x r n ↔ n =α (m[x := r]) := by
  constructor
  · intro h
    induction h with
    | @varHit x r =>
      simp only [← subst_def, subst, ↓reduceIte]
      apply AlphaEquiv.refl
    | @varMiss x y r hyx =>
      simp only [← subst_def, subst, hyx, ↓reduceIte]
      apply AlphaEquiv.refl
    | @absShadow x m r =>
      simp only [← subst_def, subst, ↓reduceIte]
      apply AlphaEquiv.refl
    | @absIn x y m r m' hy h ih =>
      have hyx : y ≠ x := by grind
      have hyr : y ∉ r.fv := by grind
      simp only [← subst_def, subst, hyx, ↓reduceIte, hyr, not_false_eq_true]
      apply AlphaEquiv.context (c := Context.abs y Context.hole)
      assumption
    | @app m n x r m' n' h1 h2 ih1 ih2 =>
      simp only [← subst_def, subst]
      apply AlphaEquiv.app <;> assumption
    | @alpha m m' r r' n n' x hm hr hn h ih =>
      apply AlphaEquiv.trans (n := n)
      · grind [AlphaEquiv.symm]
      apply AlphaEquiv.trans (n := m[x := r]) <;> grind [subst.preserve_AlphaEquiv]
  · intro h
    apply Subst.alpha (m := m) (r := r) (n := m[x := r]) <;> grind [AlphaEquiv.symm,
      AlphaEquiv.refl, Subst.function_to_relation]

/-- Commutativity of substitution (a.k.a. the substitution lemma) -/
theorem subst.commutativity {m r1 r2 : Term Var} {x y : Var} :
    x ∉ r2.fv ∪ {y} → ((m[x := r1])[y := r2]) =α ((m[y := r2])[x := (r1[y := r2])]) := by
  refine WellFounded.induction sizeOfWFRel.wf m
    (C := fun m => ∀ (r1 r2 : Term Var) (x y : Var),
      x ∉ r2.fv ∪ {y} →
      ((m[x := r1])[y := r2]) =α ((m[y := r2])[x := (r1[y := r2])])) ?_ r1 r2 x y
  intro m ih r1 r2 x y hxy
  cases m with
  | var z =>
    by_cases hzx : z = x
    · subst z
      have hxy' : x ≠ y := by grind
      simp only [← subst_def, subst.eq_1, ↓reduceIte, hxy']
      apply AlphaEquiv.refl
    · by_cases hzy : z = y
      · subst z
        simp only [← subst_def, subst.eq_1, hzx, ↓reduceIte]
        apply AlphaEquiv.symm
        apply subst.non_free
        grind
      · simp only [← subst_def, subst.eq_1, hzx, hzy, ↓reduceIte]
        apply AlphaEquiv.refl
  | abs z m =>
    obtain ⟨w, hw⟩ := HasFresh.fresh_exists
      (m.vars ∪ r1.vars ∪ r2.vars ∪ (r1[y := r2]).vars ∪ {x, y, z})
    have hl : (((Term.abs z m)[x := r1])[y := r2]) =α
      (Term.abs w (((m.rename z w)[x := r1])[y := r2])) := by
      apply AlphaEquiv.trans (n := (((Term.abs w ((m.rename z w)[x := r1]))[y := r2])))
      · apply subst.preserve_AlphaEquiv
        · apply subst.abs_fresh
          grind
        · apply AlphaEquiv.refl
      · have hwy : w ≠ y := by grind
        have hwr2 : w ∉ r2.fv := by grind [vars_either_fv_or_bv]
        simp only [← subst_def, subst.eq_2, hwy, ↓reduceIte, hwr2, not_false_eq_true]
        apply AlphaEquiv.refl
    have hr : (Term.abs w (((m.rename z w)[y := r2])[x := (r1[y := r2])]))
      =α (((Term.abs z m)[y := r2])[x := (r1[y := r2])]) := by
      apply AlphaEquiv.symm
      apply AlphaEquiv.trans (n := ((Term.abs w ((m.rename z w)[y := r2]))[x := (r1[y := r2])]))
      · apply subst.preserve_AlphaEquiv
        · apply subst.abs_fresh
          grind
        · apply AlphaEquiv.refl
      · have hwx : w ≠ x := by grind
        have hwr : w ∉ (r1.subst y r2).fv := by grind [vars_either_fv_or_bv]
        simp only [← subst_def, subst.eq_2, hwx, ↓reduceIte, hwr, not_false_eq_true]
        apply AlphaEquiv.refl
    have hmid : (Term.abs w (((m.rename z w)[x := r1])[y := r2])) =α
      (Term.abs w (((m.rename z w)[y := r2])[x := (r1[y := r2])])) := by
      apply AlphaEquiv.context (c := Context.abs w Context.hole)
      apply ih <;> grind [rename_eq_sizeOf]
    exact AlphaEquiv.trans hl <| AlphaEquiv.trans hmid hr
  | app m1 m2 =>
    simp only [← subst_def, subst.eq_3]
    apply AlphaEquiv.app <;> apply ih <;> grind

end LambdaCalculus.Named.Untyped.Term

end Cslib
