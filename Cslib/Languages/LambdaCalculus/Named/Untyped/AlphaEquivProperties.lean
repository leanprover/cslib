/-
Copyright (c) 2026 Haoxuan Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haoxuan Yin, Fabrizio Montesi, Chris Anto Fröschl
-/

module

public import Cslib.Languages.LambdaCalculus.Named.Untyped.Basic
public import Cslib.Languages.LambdaCalculus.Named.Untyped.RenameProperties

/-! # Properties of α-equivalence

The untyped λ-calculus, with a named representation of variables. This file contains properties of
α-equivalence and capture-avoiding substitution.

## Main results

- `AlphaEquiv.refl`: reflexivity of α-equivalence
- `AlphaEquiv.symm`: symmetry of α-equivalence
- `AlphaEquiv.trans`: transitivity of α-equivalence
- `AlphaEquiv.permute_preserve`: permutations preserve α-equivalence
- `AlphaEquiv.swap_preserve`: Lemma 6.1 of [Crole2012], swapping preserves α-equivalence
- `permute_alphaEquiv_of_eqOn_fv`: Lemma 6.2 part 2 of [Crole2012], permutations that agree on the
  free variables of a term act on it in the same way up to α-equivalence
- `Subst.relation_iff_function`: the relational and functional definition of capture-avoiding
  substitution are equivalent, modulo alpha-equivalence
- `subst.commutativity`: commutativity of substitution, more commonly known as the
  "substitution lemma" (e.g. in [Barendregt1984])
-/

public section

namespace Cslib

universe u

variable {Var : Type u} [DecidableEq Var]

namespace LambdaCalculus.Named.Untyped.Term

/-- α-equivalent terms have the same size. -/
theorem AlphaEquiv.eq_sizeOf {m n : Term Var} : m =α n → sizeOf m = sizeOf n := by
  intro h
  induction h with
  | @var x => rfl
  | @abs y x1 x2 m1 m2 hy h ih =>
    simp
    grind
  | @app m1 n1 m2 n2 _ hm hn =>
    grind

/-- α-equivalent terms have the same free variables. -/
theorem AlphaEquiv.same_fv {m n : Term Var} : m =α n → m.fv = n.fv := by
  intro h
  induction h with
  | var => rfl
  | app => grind
  | @abs y x1 x2 m1 m2 hy h ih =>
    grind =>
      instantiate [fv_rename, vars_eq_fv_union_bv]
      have : m1.fv.erase x1 = (m1.rename x1 y).fv.erase y
      have : (m2.rename x2 y).fv.erase y = m2.fv.erase x2

/-- Permutations preserve α-equivalence. -/
lemma AlphaEquiv.permute_preserve {m m' : Term Var} (h : m =α m') (π : Equiv.Perm Var) :
    (m.permute π) =α (m'.permute π) := by
  induction h with
  | var => exact .var
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | @abs z a b m m' hz _ ih =>
    apply AlphaEquiv.abs (y := π z)
    · grind [vars_permute, π.injective]
    · simpa only [permute_rename, AlphaEquiv_def] using ih

/-- Lemma 6.1 [Crole2012]: Swap (transposition) preserves α-equivalence. -/
lemma AlphaEquiv.swap_preserve {m m' : Term Var} {u v : Var} (h : m =α m') :
    (m.swap u v) =α (m'.swap u v) :=
  h.permute_preserve (Equiv.swap u v)

variable [HasFresh Var]

/-- Lemma 6.2 part 2 [Crole2012]: permutations that agree on the free variables of a term act on
it in the same way up to α-equivalence. The paper's hypothesis `free(E) ⊆ AS(π, π')` is
`Set.EqOn π π' m.fv`. -/
lemma permute_alphaEquiv_of_eqOn_fv (m : Term Var) (π π' : Equiv.Perm Var)
    (h : Set.EqOn π π' m.fv) : (m.permute π) =α (m.permute π') := by
  induction m generalizing π π' with
  | var x =>
    have hx : π x = π' x := by simpa using h
    simpa [permute, hx] using AlphaEquiv.var
  | app m n ihm ihn =>
    simp only [fv, Finset.coe_union, Set.eqOn_union] at h
    exact AlphaEquiv.app (ihm π π' h.1) (ihn π π' h.2)
  | abs a m ih =>
    obtain ⟨z, hz⟩ := fresh_exists ((m.permute π).vars ∪ (m.permute π').vars ∪ {π a, π' a})
    apply AlphaEquiv.abs (y := z) (by grind)
    rw [← swap_eq_rename_of_notMem_vars, ← swap_eq_rename_of_notMem_vars] <;>
    grind [swap, permute_permute, Set.EqOn, vars_eq_fv_union_bv, vars_permute, Equiv.injective]

/-- Lemma 6.2 part 2 [Crole2012] (specialized). -/
lemma swap_comp_alphaEquiv_of_notMem_fv {m : Term Var} {a u z : Var}
    (hu : u ∉ m.fv) (hz : z ∉ m.fv) :
    ((m.swap u a).swap z u) =α (m.swap z a) := by
  simp_rw [← permute_swap, permute_permute]
  apply permute_alphaEquiv_of_eqOn_fv
  grind [Set.EqOn]

/-- Renaming the bound variable of an abstraction to a fresh one, by swapping, gives an
α-equivalent term. -/
lemma AlphaEquiv.abs_swap {m : Term Var} {x y : Var} (hy : y ∉ m.fv) :
    (m.abs x) =α ((m.swap x y).abs y) := by
  have h := permute_alphaEquiv_of_eqOn_fv (.abs x m) (.refl Var) (.swap x y) (by grind [Set.EqOn])
  simpa [permute, swap] using h

/-- Reflexivity of α-equivalence. -/
theorem AlphaEquiv.refl (m : Term Var) : m =α m := by
  simpa using permute_alphaEquiv_of_eqOn_fv m (.refl Var) (.refl Var) fun _ _ => rfl

omit [HasFresh Var] in
/-- Symmetry of α-equivalence. -/
theorem AlphaEquiv.symm {m n : Term Var} : m =α n → n =α m := by
  intro h
  induction h with
  | @var x => grind [AlphaEquiv.var]
  | @abs y x1 x2 m1 m2 hy h ih =>
    apply AlphaEquiv.abs (y := y) <;> grind
  | @app m1 n1 m2 n2 hwm1 hwn1 hwm2 hwn2 => grind [AlphaEquiv.app]

omit [HasFresh Var] in
/-- Renaming α-equivalent terms produces α-equivalent terms. -/
theorem AlphaEquiv.rename_preserve (m n : Term Var) (x y : Var) :
    y ∉ m.vars ∪ n.vars → m =α n → (m.rename x y) =α (n.rename x y) := by
  intro hy h
  rw [← swap_eq_rename_of_notMem_vars (by grind),
    ← swap_eq_rename_of_notMem_vars (by grind)]
  exact h.swap_preserve

lemma AlphaEquiv.abs_congr {m m' : Term Var} {x : Var} (h : m =α m') :
    (Term.abs x m) =α (Term.abs x m') := by
  obtain ⟨y, hy⟩ := HasFresh.fresh_exists (m.vars ∪ m'.vars ∪ {x})
  apply AlphaEquiv.abs (y := y)
  · grind
  · apply AlphaEquiv.rename_preserve <;> grind

omit [HasFresh Var] in
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
        grind [AlphaEquiv.rename_preserve]
      grind

/-- Transitivity of α-equivalence. -/
theorem AlphaEquiv.trans {m n p : Term Var} : m =α n → n =α p → m =α p := by
  induction m using induction_by_sizeOf generalizing n p with
  | step m ih =>
    intro hmn hnp
    cases m with
    | var x =>
      cases hmn with
      | @var x => assumption
    | abs x1 m1 =>
      obtain ⟨w, hw⟩ := fresh_exists <| free_union [vars] Var
      have hmn' := hmn
      cases hmn' with
      | @abs y x1 x2 m1 m2 hy h1 =>
        have hnp' := hnp
        cases hnp' with
        | @abs z x2 x3 m2 m3 hz h2 =>
          apply AlphaEquiv.abs (y := w)
          · grind
          apply ih (n := m2.rename x2 w) <;> grind [AlphaEquiv.abs_elim]
    | app m1 m2 =>
      cases hmn with
      | @app m1 n1 m2 n2 hmn1 hmn2 =>
        cases hnp with
        | @app n1 p1 n2 p2 hnp1 hnp2 =>
          apply AlphaEquiv.app
          · apply ih (n := n1) <;> grind
          · apply ih (n := n2) <;> grind

/-- Chains of α-equivalences can be written with `calc` and `trans`. -/
instance : Trans (α := Term Var) (· =α ·) (· =α ·) (· =α ·) := ⟨AlphaEquiv.trans⟩

/-- Renaming a non-free variable results in an α-equivalent term -/
theorem AlphaEquiv.rename_non_fv {m : Term Var} {x y : Var} : x ∉ m.fv → y ∉ m.vars →
    m =α (m.rename x y) := by
  intro hx hy
  rw [← swap_eq_rename_of_notMem_vars hy]
  simpa [permute_swap] using permute_alphaEquiv_of_eqOn_fv m (.refl Var) (.swap x y)
    (by grind [Set.EqOn, vars_eq_fv_union_bv])

/-- Abstracting over an arbitrary non-free variable results in the same term,
    modulo α-equivalence. -/
theorem AlphaEquiv.abs_non_fv {m1 m2 : Term Var} {x1 x2 : Var} :
    m1 =α m2 → x1 ∉ m1.fv → x2 ∉ m2.fv → (Term.abs x1 m1) =α (Term.abs x2 m2) := by
  intro hm hx1 hx2
  obtain ⟨y, hy⟩ := fresh_exists <| free_union [vars] Var
  apply AlphaEquiv.abs (y := y)
  · grind
  grind [AlphaEquiv.abs, AlphaEquiv.trans, rename_non_fv, AlphaEquiv.symm]

/-- Renaming an abstraction leads to an α-equivalent term. -/
theorem AlphaEquiv.abs_rename {m : Term Var} {x y : Var} :
    y ∉ m.vars ∪ {x} → (Term.abs x m) =α (Term.abs y (m.rename x y)) := by
  intro hy
  obtain ⟨z, hz⟩ := fresh_exists <| free_union [vars] Var
  apply AlphaEquiv.abs (y := z) <;> grind [AlphaEquiv.refl]

omit [DecidableEq Var] [HasFresh Var] in
/-- Any `Term` can be obtained by filling a `Context` with a variable. This proves that `Context`
completely captures the syntax of terms. -/
theorem Context.complete (m : Term Var) : ∃ (c : Context Var) (x : Var), m = (c.fill (var x)) := by
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
theorem Context.fill_vars {c : Context Var} {m : Term Var} : (c.fill m).vars = c.vars ∪ m.vars := by
  induction c <;> grind [Context.fill, Context.vars]

/-- α-equivalence is preserved under context filling. -/
theorem AlphaEquiv.context {m n : Term Var} {c : Context Var} :
    m =α n → (c.fill m) =α (c.fill n) := by
  intro h
  induction c with
  | hole => exact h
  | abs x c ih => exact ih.abs_congr
  | appL c m ih => exact .app ih (.refl m)
  | appR m c ih => exact .app (.refl m) ih

/-- The functional definition of substitution satisfies the relational definition of substitution.
-/
theorem Subst.function_to_relation {m r : Term Var} {x : Var} : m.Subst x r (m[x := r]) := by
  induction m using induction_by_sizeOf with
  | step m ih =>
    cases m with
    | var y => grind [Subst.varHit, Subst.varMiss]
    | app m1 m2 => grind [Subst.app]
    | abs y m =>
      by_cases hyx : y = x
      · grind [Subst.absShadow]
      · by_cases hyr : y ∈ r.fv
        · let s := {x, y} ∪ m.vars ∪ r.vars
          have hz := fresh_notMem s
          set z := fresh s
          apply Subst.alpha (m := abs z (m.rename y z)) (r := r)
            (n := abs z ((m.rename y z)[x := r]))
          · have h1 : abs z (m.rename y z) = (abs y m).rename y z := by
              simp
            grind [AlphaEquiv.symm, AlphaEquiv.rename_non_fv]
          · grind [AlphaEquiv.refl]
          · grind [AlphaEquiv.refl]
          · grind [Subst.absIn, vars_eq_fv_union_bv]
        · grind [Subst.absIn]

/-- Substituting a non-free variable has no effect. -/
theorem subst.non_free {m r : Term Var} {x : Var} : x ∉ m.fv → (m[x := r]) =α m := by
  induction m using induction_by_sizeOf with
  | step m ih =>
    intro hx
    cases m with
    | var y => grind [AlphaEquiv.var]
    | app m1 m2 => grind [AlphaEquiv.app]
    | abs y m =>
      by_cases hyx : y = x
      · grind [AlphaEquiv.refl]
      · by_cases hyr : y ∉ r.fv
        · grind [AlphaEquiv.abs_congr]
        · let z := fresh (m.vars ∪ r.vars ∪ {x, y})
          have hz : z ∉ m.vars ∪ r.vars ∪ {x, y} := by grind
          have hm := ih (m.rename y z) (by grind) (by grind [fv_rename])
          have := hm.abs_congr.trans (AlphaEquiv.abs_rename (by grind)).symm
          grind

private lemma subst.abs_fresh_helper {m r : Term Var} {x y z : Var} :
    z ∉ m.vars ∪ r.vars ∪ {x, y} → ((Term.abs y m)[x := r]) =α (Term.abs z ((m.rename y z)[x := r]))
    ∧ (y ∉ r.fv ∪ {x} → (Term.abs y (m[x := r])) =α (Term.abs z ((m.rename y z)[x := r]))) := by
  induction m using induction_by_sizeOf generalizing r x y z with
  | step m ih =>
    intro hz
    have hright : ∀ (m' : Term Var) (y' : Var), sizeOf m' = sizeOf m →
        z ∉ m'.vars ∪ r.vars ∪ {x, y'} → y' ∉ r.fv ∪ {x} →
        (Term.abs y' (m'[x:=r])) =α (Term.abs z ((m'.rename y' z)[x:=r])) := by
      intro m' y' hm' hz hy'
      cases m' with
      | var w =>
        by_cases hwx : w = x
        · grind [vars_eq_fv_union_bv, AlphaEquiv.refl, AlphaEquiv.abs_non_fv]
        · by_cases hwy' : w = y'
          · obtain ⟨v, hv⟩ := fresh_exists <| free_union [vars] Var
            apply AlphaEquiv.abs (y := v) <;> grind [AlphaEquiv.var]
          · grind [vars_eq_fv_union_bv, AlphaEquiv.refl, AlphaEquiv.abs_non_fv]
      | app m1 m2 =>
        obtain ⟨w, hw⟩ := fresh_exists
          ((m1.app m2)[x := r].vars ∪ (((m1.app m2).rename y' z)[x := r]).vars
          ∪ m1[x := r].vars ∪ m2[x := r].vars ∪ (m1.rename y' z)[x := r].vars
          ∪ (m2.rename y' z)[x := r].vars ∪ {y', z})
        apply AlphaEquiv.abs (y := w) <;> grind [AlphaEquiv.app, AlphaEquiv.abs_elim]
      | abs w m1 =>
        by_cases hwy' : w = y'
        · grind [vars_eq_fv_union_bv, AlphaEquiv.abs_non_fv]
        · rw [rename]
          simp only [hwy', ↓reduceIte]
          by_cases hwx : w = x
          · grind [AlphaEquiv.trans, AlphaEquiv.abs_rename, AlphaEquiv.refl]
          · by_cases hwr : w ∈ r.fv
            · obtain ⟨v, hv⟩ := fresh_exists <| free_union [vars] Var
              simp at hv
              have hl : (Term.abs y' (((Term.abs w m1)[x := r]))) =α
                  (Term.abs y' (Term.abs v ((m1.rename w v)[x := r]))) := by
                apply AlphaEquiv.context (c := Context.abs y' Context.hole)
                grind
              have hr : (Term.abs z (Term.abs v (((m1.rename y' z).rename w v)[x := r])))
                =α (Term.abs z ((Term.abs w (m1.rename y' z))[x := r])) := by
                apply AlphaEquiv.context (c := Context.abs z Context.hole)
                grind [AlphaEquiv.symm]
              have hmid : (Term.abs y' (Term.abs v ((m1.rename w v)[x := r]))) =α
                  (Term.abs z (Term.abs v (((m1.rename y' z).rename w v)[x := r]))) := by
                obtain ⟨u, hu⟩ := fresh_exists
                  ((Term.abs v ((m1.rename w v)[x := r])).vars ∪
                  (Term.abs v (((m1.rename y' z).rename w v)[x := r])).vars ∪
                  ((m1.rename w v).rename y' z)[x:=r].vars ∪ {y', z})
                apply AlphaEquiv.abs (y := u)
                · grind
                · have hvy' : v ≠ y' := by grind
                  have hvz : v ≠ z := by grind
                  simp only [rename, hvy', hvz, ↓reduceIte]
                  apply AlphaEquiv.context (c := Context.abs v Context.hole)
                  grind [AlphaEquiv.trans, AlphaEquiv.abs_elim, AlphaEquiv.rename_preserve,
                    rename_comm_of_ne, AlphaEquiv.refl]
              grind [AlphaEquiv.trans]
            · obtain ⟨v, hv⟩ := fresh_exists
                (m1[x:=r].vars ∪ (m1.rename y' z)[x:=r].vars ∪ ((Term.abs w m1)[x := r]).vars ∪
                ((Term.abs w (m1.rename y' z))[x := r]).vars ∪ {y', z})
              apply AlphaEquiv.abs (y := v)
              · grind
              · have hwz : w ≠ z := by grind
                simp only [subst_def, eq_2, hwx, ↓reduceIte, hwr, not_false_eq_true, rename, hwy',
                  hwz]
                apply AlphaEquiv.context (c := Context.abs w Context.hole)
                grind [AlphaEquiv.abs_elim]
    have hleft : ((Term.abs y m)[x:=r]) =α (Term.abs z ((m.rename y z)[x:=r])) := by
      by_cases hyx : y = x
      · subst y
        simp only [subst_def, eq_2, ↓reduceIte, AlphaEquiv_def]
        obtain ⟨w, hw⟩ := fresh_exists (m.vars ∪ r.vars ∪ ((m.rename x z).subst x r).vars ∪
          {x, z})
        apply AlphaEquiv.abs (y := w)
        · grind
        · apply AlphaEquiv.trans (n := ((m.rename x z).rename z w))
          · grind [AlphaEquiv.refl]
          · grind [AlphaEquiv.rename_preserve, AlphaEquiv.symm, subst.non_free, fv_rename]
      · by_cases hyr : y ∈ r.fv
        · simp only [subst_def, eq_2, hyx, ↓reduceIte, hyr, not_true_eq_false, Finset.union_insert,
              Finset.union_singleton, AlphaEquiv_def]
          let s := (insert x (insert y (m.vars ∪ r.vars)))
          have hw := fresh_notMem s
          grind [AlphaEquiv.refl, AlphaEquiv.trans, vars_eq_fv_union_bv]
        · grind
    grind

/-- Modulo α-equivalence, substituting an abstraction falls back to the fresh variable case only.
    With this lemma, the three cases in the definition of subst can be reduced to one.
-/
theorem subst.abs_fresh {m r : Term Var} {x y z : Var} : z ∉ m.vars ∪ r.vars ∪ {x, y} →
    ((Term.abs y m)[x := r]) =α (Term.abs z ((m.rename y z)[x := r])) := by
  grind [subst.abs_fresh_helper]

/-- Substituting α-equivalent terms produces α-equivalent terms. -/
theorem subst.preserve_AlphaEquiv {m m' r r' : Term Var} {x : Var} :
    m =α m' → r =α r' → (m[x := r]) =α (m'[x := r']) := by
  induction m using induction_by_sizeOf generalizing m' r r' x with
  | step m ih =>
    intro hmm' hrr'
    have hmm'' := hmm'
    cases hmm'' with
    | @var y => grind [AlphaEquiv.refl]
    | @app m m' n n' hm hn => grind [AlphaEquiv.app]
    | @abs z y y' m m' hz h1 =>
      obtain ⟨w, hw⟩ := fresh_exists <| free_union [vars] Var
      refine (subst.abs_fresh (z := w) (by grind)).trans ?_
      refine AlphaEquiv.trans ?_ (subst.abs_fresh (z := w) (by grind)).symm
      apply AlphaEquiv.abs_congr
      apply ih <;> grind [AlphaEquiv.abs_elim]

/-- The relational definition of substitution coincides with the functional definition of
    substitution, modulo α-equivalence. -/
theorem Subst.relation_iff_function {m n r : Term Var} {x : Var} :
    m.Subst x r n ↔ n =α (m[x := r]) := by
  constructor
  · intro h
    induction h with
    | varHit => grind [AlphaEquiv.refl]
    | varMiss => grind [AlphaEquiv.refl]
    | absShadow => grind [AlphaEquiv.refl]
    | app => grind [AlphaEquiv.app]
    | @absIn x y m r m' hy h ih =>
      have hyx : y ≠ x := by grind
      have hyr : y ∉ r.fv := by grind
      simp only [subst_def, subst.eq_2, hyx, ↓reduceIte, hyr, not_false_eq_true, AlphaEquiv_def]
      apply AlphaEquiv.context (c := Context.abs y Context.hole)
      assumption
    | @alpha m m' r r' n n' x hm hr hn h ih =>
      grind [AlphaEquiv.symm, AlphaEquiv.trans, subst.preserve_AlphaEquiv]
  · intro h
    apply Subst.alpha (m := m) (r := r) (n := m[x := r]) <;> grind [AlphaEquiv.symm,
      AlphaEquiv.refl, Subst.function_to_relation]

/-- Commutativity of substitution (a.k.a. the substitution lemma) -/
theorem subst.commutativity {m r1 r2 : Term Var} {x y : Var} :
    x ∉ r2.fv ∪ {y} → ((m[x := r1])[y := r2]) =α ((m[y := r2])[x := (r1[y := r2])]) := by
  induction m using induction_by_sizeOf generalizing r1 r2 x y with
  | step m ih =>
    intro hx
    cases m with
    | var z => grind [AlphaEquiv.refl, AlphaEquiv.symm, subst.non_free]
    | app m1 m2 => grind [AlphaEquiv.app]
    | abs z m =>
      obtain ⟨w, hw⟩ := fresh_exists (m.vars ∪ r1.vars ∪ r2.vars ∪ (r1[y := r2]).vars ∪ {x, y, z})
      have hl : (((Term.abs z m)[x := r1])[y := r2]) =α
        (Term.abs w (((m.rename z w)[x := r1])[y := r2])) := by
        apply AlphaEquiv.trans (n := (((Term.abs w ((m.rename z w)[x := r1]))[y := r2])))
        · grind [subst.preserve_AlphaEquiv, subst.abs_fresh, AlphaEquiv.refl]
        · grind [vars_eq_fv_union_bv, AlphaEquiv.refl]
      have hr : (Term.abs w (((m.rename z w)[y := r2])[x := (r1[y := r2])]))
        =α (((Term.abs z m)[y := r2])[x := (r1[y := r2])]) := by
        apply AlphaEquiv.symm
        apply AlphaEquiv.trans (n := ((Term.abs w ((m.rename z w)[y := r2]))[x := (r1[y := r2])]))
        · grind [subst.preserve_AlphaEquiv, subst.abs_fresh, AlphaEquiv.refl]
        · grind [vars_eq_fv_union_bv, AlphaEquiv.refl]
      have hmid : (Term.abs w (((m.rename z w)[x := r1])[y := r2])) =α
        (Term.abs w (((m.rename z w)[y := r2])[x := (r1[y := r2])])) := by
        apply AlphaEquiv.context (c := Context.abs w Context.hole)
        grind
      grind [AlphaEquiv.trans]

end LambdaCalculus.Named.Untyped.Term

end Cslib
