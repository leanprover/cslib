/-
Copyright (c) 2026 David Wegmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 4.7 (via Claude Code), David Wegmann
-/

module

public import Cslib.Foundations.Syntax.HasParallelSubstitution
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic

/-! # Parallel substitution for locally-nameless untyped λ-terms

PROTOTYPE: instantiates `HasParallelSubstitution` / `LawfulHasParallelSubstitution`
for the locally-nameless untyped `Term`, to test how the interface maps onto the
existing definitions. Not yet wired into the import tree.

Because the representation is locally nameless — bound variables are de Bruijn
indices and only free variables (`fvar`) are substituted — parallel substitution
is purely structural and capture-free, so the instance needs **no** typeclass
constraints (no `DecidableEq`, no `HasFresh`), exactly like the single-variable
`HasSubstitution` instance for this `Term`.

We also show that the existing single-variable `Term.subst` is the special case
of `psubst` at a point-updated assignment (`subst_eq_psubst`).
-/

@[expose] public section

namespace Cslib

universe u

variable {Var : Type u}

namespace LambdaCalculus.LocallyNameless.Untyped.Term

/-- Parallel (simultaneous) substitution of free variables: replace every `fvar x`
by `σ x`, in a single structural pass. Capture-free by local namelessness. -/
@[scoped grind =]
def psubst (σ : Var → Term Var) : Term Var → Term Var
  | bvar i  => bvar i
  | fvar x  => σ x
  | app l r => app (psubst σ l) (psubst σ r)
  | abs M   => abs (psubst σ M)

@[simp] theorem psubst_bvar (σ : Var → Term Var) (i : ℕ) : psubst σ (bvar i) = bvar i := rfl
@[simp] theorem psubst_fvar (σ : Var → Term Var) (x : Var) : psubst σ (fvar x) = σ x := rfl
@[simp] theorem psubst_app (σ : Var → Term Var) (l r : Term Var) :
    psubst σ (app l r) = app (psubst σ l) (psubst σ r) := rfl
@[simp] theorem psubst_abs (σ : Var → Term Var) (M : Term Var) :
    psubst σ (abs M) = abs (psubst σ M) := rfl

/-- Substituting every free variable by itself is the identity. -/
@[simp] theorem psubst_fvar_id (M : Term Var) : psubst fvar M = M := by
  induction M <;> simp_all

/-- The operation instance: `var` is `fvar`, `psubst` is the structural pass above.
Note the complete absence of constraints on `Var`. -/
instance instHasParallelSubstitution : HasParallelSubstitution (Term Var) Var where
  var := fvar
  psubst := Term.psubst

/-- The typeclass operation reduces to the concrete `Term.psubst` (definitionally).
Lets `simp`/`grind` see through the typeclass projection. -/
@[simp] theorem psubst_eq (σ : Var → Term Var) (M : Term Var) :
    HasParallelSubstitution.psubst σ M = Term.psubst σ M := rfl

/-- The laws hold unconditionally: this `Term` (with `fvar`/`psubst`) is a lawful
parallel-substitution structure — i.e. a relative monad on free variables. -/
instance instLawfulHasParallelSubstitution : LawfulHasParallelSubstitution (Term Var) Var where
  psubst_var _ _ := rfl
  psubst_id := fun t => by
    change Term.psubst fvar t = t
    induction t <;> simp_all
  psubst_comp := fun σ τ t => by
    change Term.psubst σ (Term.psubst τ t) = Term.psubst (fun x => Term.psubst σ (τ x)) t
    induction t <;> simp_all

/-- The existing single-variable substitution `m[x := sub]` is the special case of
`psubst` where the assignment is `fvar` updated at `x` to `sub`. This is how the
two interfaces line up. -/
theorem subst_eq_psubst [DecidableEq Var] (m : Term Var) (x : Var) (sub : Term Var) :
    m.subst x sub = psubst (fun y => if x = y then sub else fvar y) m := by
  induction m <;> simp_all [Term.subst]

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
