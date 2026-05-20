/-
Copyright (c) 2026 David Wegmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 4.7 (via Claude Code), David Wegmann
-/

module

public import Cslib.Init

/-! # Parallel (simultaneous) substitution

A typeclass for *parallel* substitution: replacing every variable of a term
simultaneously, according to an assignment `σ : Var → T`, in a single pass.

This is the operation needed by first-order unification — where a unifier is a
simultaneous assignment and most-general-unifier reasoning relies on substitution
composition — and it subsumes the finite multi-substitution used elsewhere (e.g.
the strong-normalization proof), which is recovered by turning a finite
`Context` into a total assignment.

Unlike `Cslib.HasSubstitution` (single-variable replacement `t[x := t']`),
parallel substitution is *not* derivable from iterated single substitutions:
applying bindings one at a time is sequential, whereas here all variables are
replaced at once.

## Operation vs. laws

Following the `Monad` / `LawfulMonad` pattern (and mirroring `Cslib.HasSubstitution`,
which is a pure notation typeclass), the operation and its laws are split:

* `HasParallelSubstitution` carries only `var` and `psubst`, plus notation.
* `LawfulHasParallelSubstitution` carries the laws.

A syntax with variables that satisfies the laws is exactly a (relative) monad:
`var` is the unit (`return`) and `psubst` is the Kleisli extension (`bind`, with
arguments flipped). In particular `psubst_comp` is associativity, which gives
substitution *composition* `t⟦τ⟧ₚ⟦σ⟧ₚ = t⟦σ ∘ₚ τ⟧ₚ` — the algebra the MGU proof
rests on. The laws hold unconditionally for capture-free representations
(first-order terms, locally-nameless λ-terms); named representations, whose
substitution is only well-behaved up to α-equivalence, are deliberately not
expected to be lawful instances.
-/

public section

namespace Cslib

universe u v

/-- Types `T` whose values are syntax over variables of type `Var`, equipped with
*parallel* (simultaneous) substitution.

`var` embeds a variable as a value; `psubst σ t` replaces every variable `x`
occurring in `t` by `σ x`, all at once. This is a pure notation/operation class;
the substitution laws live in `LawfulHasParallelSubstitution`. -/
class HasParallelSubstitution (T : Type u) (Var : outParam (Type v)) where
  /-- Embed a variable as a value. -/
  var : Var → T
  /-- Simultaneously replace every variable `x` in `t` by `σ x`. -/
  psubst : (Var → T) → T → T

namespace HasParallelSubstitution

/-- Notation for parallel substitution, `t⟦σ⟧ₚ`: apply assignment `σ` to `t`. -/
scoped notation:max t "⟦" σ "⟧ₚ" => HasParallelSubstitution.psubst σ t

variable {T : Type u} {Var : Type v} [HasParallelSubstitution T Var]

/-- Kleisli composition of assignments: `(σ ∘ₚ τ) x = (τ x)⟦σ⟧ₚ`, i.e. apply `τ`
first, then `σ`. -/
def comp (σ τ : Var → T) : Var → T := fun x => psubst σ (τ x)

@[inherit_doc]
scoped infixr:90 " ∘ₚ " => comp

/-- `σ` is at least as general as `τ` (written `σ ≤ₚ τ`) when `τ` factors through
`σ`: there is an assignment `ρ` with `τ = ρ ∘ₚ σ`, i.e. `τ x = (σ x)⟦ρ⟧ₚ` for
every variable `x`. Equivalently, in the "apply to every term" formulation (see
`moreGeneral_iff`), applying `τ` to any term equals applying `σ` and then `ρ`.

This is the standard "more general than" relation underlying most-general
unifiers. In the usual textbook notation, where the composite `στ` applies `σ`
first and then `τ`, it reads `σ ≤ₚ τ ↔ ∃ ρ, τ = σρ`; we write the same thing
with the (right-to-left) Kleisli composite `ρ ∘ₚ σ`. The relation is taken over
total assignments — there is deliberately no restriction to a finite domain.

This needs only the operation to *state*; that it is a preorder needs the laws. -/
def MoreGeneral (σ τ : Var → T) : Prop := ∃ ρ : Var → T, τ = ρ ∘ₚ σ

@[inherit_doc]
scoped infix:50 " ≤ₚ " => MoreGeneral

end HasParallelSubstitution

open HasParallelSubstitution in
/-- The laws of parallel substitution: a lawful instance is exactly a (relative)
monad with `var` as unit and `psubst` as Kleisli extension. Stated as a `Prop`
class over an existing `HasParallelSubstitution`, mirroring `LawfulMonad`. -/
class LawfulHasParallelSubstitution (T : Type u) (Var : outParam (Type v))
    [HasParallelSubstitution T Var] : Prop where
  /-- Substituting into a single variable looks it up in the assignment.
  (Monad left identity: `bind (pure x) σ = σ x`.) -/
  psubst_var : ∀ (σ : Var → T) (x : Var), psubst σ (var x) = σ x
  /-- The identity assignment `var` acts as the identity substitution.
  (Monad right identity: `bind t pure = t`.) -/
  psubst_id : ∀ (t : T), psubst var t = t
  /-- Substitutions compose into a single pass.
  (Monad associativity.) -/
  psubst_comp : ∀ (σ τ : Var → T) (t : T),
    psubst σ (psubst τ t) = psubst (fun x => psubst σ (τ x)) t

namespace HasParallelSubstitution

variable {T : Type u} {Var : Type v}
  [HasParallelSubstitution T Var] [LawfulHasParallelSubstitution T Var]

export LawfulHasParallelSubstitution (psubst_var psubst_id psubst_comp)

/-- Substitution composition, stated via `comp`: substituting by `τ` and then `σ`
is one substitution by `σ ∘ₚ τ`. -/
theorem psubst_psubst (σ τ : Var → T) (t : T) :
    psubst σ (psubst τ t) = psubst (σ ∘ₚ τ) t :=
  psubst_comp σ τ t

/-- Term-level characterization of generality, matching the "apply to every term"
formulation used for unifiers: `σ ≤ₚ τ` iff there is `ρ` with
`t⟦τ⟧ₚ = (t⟦σ⟧ₚ)⟦ρ⟧ₚ` for all terms `t`. The forward direction is `psubst_comp`;
the backward direction instantiates at `t = var x` and uses `psubst_var`. -/
theorem moreGeneral_iff {σ τ : Var → T} :
    σ ≤ₚ τ ↔ ∃ ρ : Var → T, ∀ t : T, psubst τ t = psubst ρ (psubst σ t) := by
  constructor
  · rintro ⟨ρ, rfl⟩
    exact ⟨ρ, fun t => (psubst_comp ρ σ t).symm⟩
  · rintro ⟨ρ, h⟩
    refine ⟨ρ, ?_⟩
    funext x
    simpa [comp, psubst_var] using h (var x)

/-- Generality is reflexive: the identity assignment `var` witnesses `σ ≤ₚ σ`. -/
@[refl]
theorem MoreGeneral.refl (σ : Var → T) : σ ≤ₚ σ :=
  ⟨var, by funext x; simp [comp, psubst_id]⟩

/-- Generality is transitive: compose the two witnessing assignments. -/
theorem MoreGeneral.trans {σ τ υ : Var → T} (h₁ : σ ≤ₚ τ) (h₂ : τ ≤ₚ υ) : σ ≤ₚ υ := by
  obtain ⟨ρ₁, rfl⟩ := h₁
  obtain ⟨ρ₂, rfl⟩ := h₂
  refine ⟨ρ₂ ∘ₚ ρ₁, ?_⟩
  funext x
  simp only [comp]
  exact psubst_comp ρ₂ ρ₁ (σ x)

end HasParallelSubstitution

end Cslib
