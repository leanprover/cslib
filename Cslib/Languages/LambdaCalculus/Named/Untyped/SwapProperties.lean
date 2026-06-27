/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/

module

public import Cslib.Languages.LambdaCalculus.Named.Untyped.AlphaEquivDefs
public import Cslib.Languages.LambdaCalculus.Named.Untyped.Properties

/-! # Properties of the swap (transposition) operation on lambda terms

Helper lemmas for reasoning about `Term.swap` and its interaction with
`AlphaEquiv`, `rename`, `vars`, and `fv`.

The notion of *atom swapping* (transposition) as the basis for defining α-equivalence
originates from [Gabbay and Pitts, *A New Approach to Abstract Syntax with Variable
Binding*][Gabbay2002] (Section 2, page 3). The key observation is that α-equivalence can
be defined using the notion of atom swapping in lieu of the traditional
renaming/substitution approach.

## References

* [Roy L. Crole, *Alpha equivalence equalities*][Crole2012], Sections 2 and 6
* [M. Gabbay and A. Pitts, *A New Approach to Abstract Syntax with Variable
  Binding*][Gabbay2002], Section 2
-/

@[expose] public section

namespace Cslib

universe u

variable {Var : Type u} [DecidableEq Var]

namespace LambdaCalculus.Named.Untyped.Term

/-! ### Basic properties of swap

The swap (transposition) operation `m.swap x y` implements the permutation action
`(x y) · E` from [Crole2012] (Section 2). It simultaneously replaces all occurrences
of `x` with `y` and vice versa throughout a term.

The idea of using atom swapping as a primitive operation for reasoning about variable
binding was introduced in [Gabbay2002] (Section 2, page 3), and is central to the nominal
approach to abstract syntax.
-/

@[simp]
lemma swap_self {m : Term Var} {x : Var} : m.swap x x = m := by
  induction m <;> simp [swap] <;> grind

lemma swap_comm {m : Term Var} {x y : Var} : m.swap x y = m.swap y x := by
  induction m <;> simp [swap] <;> grind

@[simp]
lemma swap_involutive {m : Term Var} {x y : Var} :
    (m.swap x y).swap x y = m := by
  induction m <;> simp [swap] <;> grind

@[simp]
lemma swap_preserves_sizeOf {m : Term Var} {x y : Var} :
    sizeOf (m.swap x y) = sizeOf m := by
  induction m <;> simp [swap] <;> grind

@[simp]
lemma swap_unused {m : Term Var} {x y : Var} :
    x ∉ m.vars → y ∉ m.vars → m.swap x y = m := by
  induction m <;> grind [swap, vars]

/-- When `y ∉ m.vars`, `swap x y` and `rename x y` coincide.

This is because `rename x y` only changes `x` to `y` (not `y` to `x`), and when `y` does
not occur in `m`, swapping and renaming produce the same result. -/
lemma swap_eq_rename_of_not_mem_vars {m : Term Var} {x y : Var}
    (hy : y ∉ m.vars) : m.swap x y = m.rename x y := by
  induction m with
  | var z =>
    unfold swap rename
    grind [Term.vars]
  | abs z m ih =>
    simp_all +decide [Term.swap, Term.rename, Term.vars];
    grind
  | app n1 n2 ih1 ih2 =>
    simp_all +decide [Term.swap, Term.rename, Term.vars]

/-- The set of free variables after a swap. Corresponds to the fact that
`free(π · E) = π · free(E)` noted in the proof of Lemma 6.2 in [Crole2012]. -/
lemma swap_fv {m : Term Var} {x y : Var} :
  (m.swap x y).fv = m.fv.image fun z => if z = x then y else if z = y then x else z := by
    induction m with
    | var z =>
      unfold fv
      aesop
    | abs z m ih =>
      simp_all +decide only [Term.swap, Term.fv]
      simp [Finset.ext_iff, Finset.mem_image, Finset.mem_sdiff]
      grind
    | app m n ih1 ih2 =>
      simp_all +decide only [Term.swap, Term.fv]
      rw [Finset.image_union]

/-- Swapping preserves non-membership in `fv`. -/
lemma fresh_swap {m : Term Var} {x y z : Var}
    (hzx : z ≠ x) (hzy : z ≠ y) (hzm : z ∉ m.fv) :
    z ∉ (m.swap x y).fv := by
  rw [swap_fv]
  grind

/-- The set of vars after a swap. -/
lemma swap_vars {m : Term Var} {x y z : Var} (hzm : z ∉ m.vars) :
  (m.swap x y).vars =
    m.vars.image fun z => if z = x then y else if z = y then x else z := by
    induction m with
    | var w =>
      simp +decide [Term.swap, Term.vars]
    | abs w m ih => simp_all +decide [Term.swap, Term.vars]
    | app m n ih1 ih2 =>
      simp_all +decide only [Term.swap, Term.vars]
      rw [Finset.image_union]
      grind

/-- Swapping preserves non-membership in `vars`. -/
lemma not_mem_vars_swap {m : Term Var} {x y z : Var}
    (hzx : z ≠ x) (hzy : z ≠ y) (hzm : z ∉ m.vars) :
    z ∉ (m.swap x y).vars := by
  rw [swap_vars hzm]
  grind

/-! ### Swap-rename commutation -/

/-- Helper function: the action of the transposition `(u v)` on a single variable.
Corresponds to the permutation `(u v)` applied to an atom, as used throughout
[Crole2012]. -/
@[simp]
def swapVar (u v z : Var) : Var :=
  if z = u then v else if z = v then u else z

/-- `swapVar` is a fixed point for variables outside `{u, v}`. -/
@[simp]
lemma swapVar_fixed {u v z : Var} (hzu : z ≠ u) (hzv : z ≠ v) :
    swapVar u v z = z := by simp_all

/-- `swapVar` is injective (permutations are bijections). -/
lemma swapVar_injective (u v : Var) : Function.Injective (swapVar u v) := by
  unfold Function.Injective
  intro a b
  unfold swapVar
  aesop

/-- `swap` and `rename` commute (modulo the permutation action on the variable
arguments).

This is used in the proof of Lemma 6.1 [Crole2012] to handle the case analysis on
variable equalities in the `abs` case. -/
lemma swap_rename_comm {m : Term Var} {u v x y : Var} :
    (m.swap u v).rename (swapVar u v x) (swapVar u v y) =
      (m.rename x y).swap u v := by
  induction m with
  | var z =>
    simp_all +decide [Term.swap, Term.rename, swapVar]
    grind
  | abs z m ih =>
    simp_all +decide [Term.swap, Term.rename, swapVar]
    grind
  | app m n ih1 ih2 =>
    simp_all +decide [Term.swap, Term.rename, swapVar]

lemma swap_rename_comm' {m : Term Var} {u v x z : Var}
    (hzu : z ≠ u) (hzv : z ≠ v) :
    (m.swap u v).rename (swapVar u v x) z =
      (m.rename x z).swap u v := by
  rw [← @swap_rename_comm _ _ m u v x z]
  simp_all

def agreementSet (f g : Var → Var) : Set Var := { x | f x = g x }

def disagreementSet (f g : Var → Var) : Set Var := { x | f x ≠ g x }

/-- The composition `(z u) ∘ (u a)` agrees with `(z a)` on all variables outside
`{u, z}`.

This is the key agreement set computation used in the proof of Theorem 4.1 in
[Crole2012]: when `u, z ∉ free(E)`, we have
`free(E) ⊆ A − {u, z} = AS((z u) ∘ (u a), (z a))`. -/
lemma agreementSet_swap_comp {a u z : Var} (huz : u ≠ z) :
    {x : Var | x ≠ u ∧ x ≠ z} ⊆
      agreementSet (swapVar z u ∘ swapVar u a) (swapVar z a) := by
  intro x ⟨hxu, hxz⟩
  simp [agreementSet, Function.comp, swapVar]
  aesop

/-! ### Lemma 6.2: Agreement on free/occurring variables implies equivalence

**Lemma 6.2** [Crole2012]:

1. For any expression `E` and permutations `π`, `π'`:
   `occ(E) ⊆ AS(π, π')` implies `π · E = π' · E` (syntactic equality).

2. For any expression `E` and permutations `π`, `π'`:
   `free(E) ⊆ AS(π, π')` implies `π · E ∼p π' · E` (α-equivalence).

Part 1 says that permutations agreeing on all occurring variables produce syntactically
identical results. Part 2 weakens this to free variables, at the cost of getting only
α-equivalence instead of syntactic equality.

These lemmas are the workhorses behind the proofs of equivalence of α-equivalence
definitions in [Crole2012] (Section 4), particularly Theorems 4.1 and 4.2.
-/

/-- Helper: the composition `(z u) ∘ (u a)` agrees with `(z a)` on variables
outside `{u, z}`.

This is used in the agreement set arguments of Theorem 4.1 [Crole2012]:
`free(E) ⊆ A − {u, z} = AS((z u) ∘ (u a), (z a))`. -/
lemma swap_comp_eq_swap_of_not_eq {x a u z : Var}
    (hxu : x ≠ u) (hxz : x ≠ z) :
    swapVar z u (swapVar u a x) = swapVar z a x := by
  unfold swapVar; aesop;

/-- **Lemma 6.2 part 1** [Crole2012] (specialized): If two composed transpositions
agree on all occurring variables, their actions are syntactically equal.

Specialized form: if `u, z ∉ vars(m)`, then `(m.swap u a).swap z u = m.swap z a`.

This follows from the general statement of Lemma 6.2 part 1: since
`u, z ∉ occ(E)`, we have `occ(E) ⊆ AS((z u) ∘ (u a), (z a))`, and therefore
`(z u) · (u a) · E = (z a) · E`.

The general statement is: for any expression `E` and permutations `π`, `π'`,
`occ(E) ⊆ AS(π, π')` implies `π · E = π' · E`. -/
lemma swap_comp_eq_of_not_mem_vars {m : Term Var} {a u z : Var}
    (hu : u ∉ m.vars) (hz : z ∉ m.vars) :
    (m.swap u a).swap z u = m.swap z a := by
  induction m;
  · simp_all +decide [ Term.swap, Term.vars ];
    grind;
  · simp_all +decide [ Term.swap, Term.vars ];
    split_ifs <;> simp_all +decide [ eq_comm ];
  · simp_all +decide [ Term.swap, Term.vars ]

variable [HasFresh Var]

/-! ### Lemma 6.1: Swap preserves α-equivalence

**Lemma 6.1** [Crole2012]: For any atoms `u` and `v` and expressions `E` and `E'`,
`E ∼p E'` implies `(u v) · E ∼p (u v) · E'`.

The proof uses well-founded induction on the size of expressions, with a case analysis
on the possible equalities between atoms in the `abs` case. The key difficulty is that
for the abstraction case `B([a]E) ∼p B([b]E')`, one must handle 17 non-trivial
combinations of equalities between `a`, `b`, the witness `z`, and the swap atoms `u`,
`v`.

This approach via case analysis on atom equalities follows [Crole2012] (Section 6.1,
Lemma 6.1).
-/

/-- **Lemma 6.1** [Crole2012]: Swap (transposition) preserves α-equivalence.

This is the key equivariance property of the swapping action: α-equivalence is
preserved under atom transpositions.
-/
lemma AlphaEquiv.swap_preserve {m m' : Term Var} {u v : Var} :
  m =α m' → (m.swap u v) =α (m'.swap u v) := by
    by_contra h
    obtain ⟨m, m', h_eq, h_neq⟩ :
        ∃ m m' : Term Var, m =α m' ∧ ¬(m.swap u v) =α (m'.swap u v) := by grind
    obtain ⟨m, m', h_eq, h_neq, h_min⟩ :
        ∃ m m' : Term Var, m =α m' ∧
          ¬(m.swap u v) =α (m'.swap u v) ∧
          ∀ n n' : Term Var, n =α n' → sizeOf n < sizeOf m →
            (n.swap u v) =α (n'.swap u v) := by
      have h_wf : WellFounded (fun m n : ℕ => m < n) := by
        exact wellFounded_lt;
      have := h_wf.has_min
        { n : ℕ | ∃ m m' : Term Var, m =α m' ∧
          ¬ ( m.swap u v ) =α ( m'.swap u v ) ∧
          n = sizeOf m }
        ⟨ _, ⟨ m, m', h_eq, h_neq, rfl ⟩ ⟩;
      obtain ⟨ a, ⟨ m, m', h_eq, h_neq, rfl ⟩, ha ⟩ := this;
      exact ⟨ m, m', h_eq, h_neq, fun n n' h_eq' h_lt =>
        Classical.not_not.1 fun h_neq' =>
          ha _ ⟨ n, n', h_eq', h_neq', rfl ⟩ h_lt ⟩ ;
    obtain ⟨x1, x2, m1, m2, h_eq⟩ :
        ∃ x1 x2 : Var, ∃ m1 m2 : Term Var,
          m = Term.abs x1 m1 ∧
          m' = Term.abs x2 m2 ∧ ∃ y : Var,
            y ∉ m1.vars ∪ m2.vars ∪ {x1, x2} ∧
            (m1.rename x1 y) =α (m2.rename x2 y) := by
      all_goals rcases h_eq with ⟨ ⟩;
      · exact False.elim <| h_neq <| AlphaEquiv.refl _;
      · grind;
      · exact False.elim <| h_neq <| AlphaEquiv.app
          ( h_min _ _ ‹_› <| by simp +arith +decide )
          ( h_min _ _ ‹_› <| by simp +arith +decide );
    obtain ⟨y, hy₁, hy₂⟩ := h_eq.2.2;
    -- Pick z fresh for m1.vars ∪ m2.vars ∪ {x1, x2, u, v}.
    obtain ⟨z, hz⟩ :
        ∃ z : Var, z ∉ m1.vars ∪ m2.vars ∪ {x1, x2, u, v} := by
      exact Infinite.exists_notMem_finset (m1.vars ∪ m2.vars ∪ {x1, x2, u, v})
    have hz_eq : (m1.rename x1 z) =α (m2.rename x2 z) := by
      apply AlphaEquiv.abs_elim; all_goals grind;
    have hz_swap :
        ((m1.swap u v).rename (swapVar u v x1) z) =α
        ((m2.swap u v).rename (swapVar u v x2) z) := by
      have hz_swap :
          ((m1.swap u v).rename (swapVar u v x1) z) =
            ((m1.rename x1 z).swap u v) ∧
          ((m2.swap u v).rename (swapVar u v x2) z) =
            ((m2.rename x2 z).swap u v) := by
        exact ⟨swap_rename_comm' (by grind) (by grind),
              swap_rename_comm' (by grind) (by grind)⟩
      grind +suggestions;
    have hz_abs :
        (Term.abs (swapVar u v x1) (m1.swap u v)) =α
        (Term.abs (swapVar u v x2) (m2.swap u v)) := by
      apply AlphaEquiv.abs;
      any_goals assumption;
      simp_all +decide [ Finset.mem_union ];
      grind +suggestions;
    exact h_neq ( by simpa [ h_eq ] using hz_abs )

/-! ### Lemma 6.2 part 2 (α-equivalence version) -/

/-- Helper: if `y₁ ∉ fv(m)` and `y₂ ∉ fv(m)`, there exists `m'` α-equivalent to `m`
with both `y₁ ∉ vars(m')` and `y₂ ∉ vars(m')`. -/
lemma exists_alphaEquiv_not_mem_vars_pair {m : Term Var} {y₁ y₂ : Var}
    (h₁ : y₁ ∉ m.fv) (h₂ : y₂ ∉ m.fv) :
    ∃ m', m =α m' ∧ y₁ ∉ m'.vars ∧ y₂ ∉ m'.vars := by
  -- Step 1: Rename y₁ to a fresh variable, avoiding both y₁ and y₂.
  let f₁ := HasFresh.fresh (m.vars ∪ {y₁, y₂})
  have hf₁ : f₁ ∉ m.vars ∪ {y₁, y₂} := HasFresh.fresh_notMem _
  let m₁ := m.rename y₁ f₁
  have hf₁_ne_y₁ : f₁ ≠ y₁ := by intro h; exact hf₁ (by simp [h])
  have hf₁_ne_y₂ : f₁ ≠ y₂ := by intro h; exact hf₁ (by simp [h])
  have hf₁_vars : f₁ ∉ m.vars := by intro h; exact hf₁ (Finset.mem_union_left _ h)
  have hm₁_alpha : m =α m₁ := AlphaEquiv.rename_non_fv h₁ hf₁_vars
  have hy₁_m₁ : y₁ ∉ m₁.vars := rename_remove hf₁_ne_y₁.symm
  -- y₂ ∉ fv(m₁) since fv is preserved by α-equivalence.
  have hy₂_fv_m₁ : y₂ ∉ m₁.fv :=
    AlphaEquiv.same_fv hm₁_alpha ▸ h₂
  -- Step 2: Rename y₂ to a fresh variable, avoiding both y₁ and y₂.
  let f₂ := HasFresh.fresh (m₁.vars ∪ {y₁, y₂})
  have hf₂ : f₂ ∉ m₁.vars ∪ {y₁, y₂} := HasFresh.fresh_notMem _
  let m₂ := m₁.rename y₂ f₂
  have hf₂_ne_y₁ : f₂ ≠ y₁ := by intro h; exact hf₂ (by simp [h])
  have hf₂_ne_y₂ : f₂ ≠ y₂ := by intro h; exact hf₂ (by simp [h])
  have hf₂_vars : f₂ ∉ m₁.vars := by intro h; exact hf₂ (Finset.mem_union_left _ h)
  have hm₂_alpha : m₁ =α m₂ := AlphaEquiv.rename_non_fv hy₂_fv_m₁ hf₂_vars
  have hy₂_m₂ : y₂ ∉ m₂.vars := rename_remove hf₂_ne_y₂.symm
  -- y₁ ∉ vars(m₂): by rename_vars, vars(m₂) ⊆ (vars(m₁) \ {y₂}) ∪ {f₂}.
  -- Since y₁ ∉ vars(m₁) and f₂ ≠ y₁, we conclude y₁ ∉ vars(m₂).
  have hy₁_m₂ : y₁ ∉ m₂.vars := by
    simp only [m₂, rename_vars, Finset.mem_union, Finset.mem_sdiff,
      Finset.mem_singleton]
    intro h
    cases h with
    | inl h => exact hy₁_m₁ h.1
    | inr h => split_ifs at h <;> simp_all [Ne.symm hf₂_ne_y₁]
  exact ⟨m₂, AlphaEquiv.trans hm₁_alpha hm₂_alpha, hy₁_m₂, hy₂_m₂⟩

/-- **Lemma 6.2 part 2** [Crole2012] (specialized): If two composed transpositions
agree on all free variables, their actions are α-equivalent.

Specialized form: if `u, z ∉ fv(m)`, then `(m.swap u a).swap z u =α m.swap z a`.

This follows from the general statement of Lemma 6.2 part 2: since `u, z # E` (i.e.,
`u, z ∉ free(E)`), we have `free(E) ⊆ AS((z u) ∘ (u a), (z a))`, and therefore
`(z u) · (u a) · E ∼p (z a) · E`.

The agreement set computation is: for any `x ∈ free(E)`, since `x ≠ u` and `x ≠ z`,
we have `swapVar z u (swapVar u a x) = swapVar z a x`
(by `swap_comp_eq_swap_of_not_eq`).

The proof reduces to Lemma 6.2 part 1 via `exists_alphaEquiv_not_mem_vars_pair`
and `AlphaEquiv.swap_preserve`. -/
lemma swap_comp_alphaEquiv_of_not_mem_fv {m : Term Var} {a u z : Var}
    (hu : u ∉ m.fv) (hz : z ∉ m.fv) :
    ((m.swap u a).swap z u) =α (m.swap z a) := by
  -- By exists_alphaEquiv_not_mem_vars_pair, get m' with m =α m' and
  -- u, z ∉ vars(m').
  obtain ⟨m', hm', hm'u, hm'z⟩ := exists_alphaEquiv_not_mem_vars_pair hu hz
  -- By Lemma 6.2 part 1 (swap_comp_eq_of_not_mem_vars):
  -- (m'.swap u a).swap z u = m'.swap z a (syntactic equality!)
  have h_eq : (m'.swap u a).swap z u = m'.swap z a :=
    swap_comp_eq_of_not_mem_vars hm'u hm'z
  -- By Lemma 6.1 (swap_preserve) applied twice to m =α m':
  have h1 : ((m.swap u a).swap z u) =α ((m'.swap u a).swap z u) :=
    AlphaEquiv.swap_preserve (AlphaEquiv.swap_preserve hm')
  -- Rewrite using the syntactic equality:
  rw [h_eq] at h1
  -- By Lemma 6.1 (swap_preserve) applied to the symmetric direction:
  have h2 : (m'.swap z a) =α (m.swap z a) :=
    AlphaEquiv.swap_preserve (AlphaEquiv.symm hm')
  -- Chain: (m.swap u a).swap z u =α (m'.swap u a).swap z u
  --         = m'.swap z a =α m.swap z a
  exact AlphaEquiv.trans h1 h2

/-- **Lemma 6.6** [Crole2012] (Barendregt variable convention):
For any term `m` and variable `y` with `y ∉ fv(m)`,
there exists `m'` α-equivalent to `m` with `y ∉ vars(m')`.

Informally, we can always rename bound atoms so that a particular atom does not
occur. -/
lemma exists_alphaEquiv_not_mem_vars {m : Term Var} {y : Var}
    (hy : y ∉ m.fv) : ∃ m', m =α m' ∧ y ∉ m'.vars := by
  by_contra h;
  convert Classical.byContradiction fun h' => ?_;
  convert h';
  convert Classical.not_not;
  simp_all only [not_exists, not_and, Decidable.not_not,
    not_false_eq_true, not_true_eq_false]
  convert h ( m.rename y ( HasFresh.fresh ( m.vars ∪ { y } ) ) ) ( by
    grind +suggestions ) using 1
  simp +decide [rename_vars]
  grind

end LambdaCalculus.Named.Untyped.Term

end Cslib
