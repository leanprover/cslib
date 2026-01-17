/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Thomas Waring
-/

module

public import Cslib.Init
public import Mathlib.Logic.Relation
public import Mathlib.Util.Notation3

-- TODO remove this import
public import Mathlib.Algebra.Polynomial.Eval.Defs

@[expose] public section

/-!
# Reduction System

A reduction system is an operational semantics expressed as a relation between terms.
-/

namespace Cslib

universe u

/--
A reduction system is a relation between `Term`s.
-/
structure ReductionSystem (Term : Type u) where
  /-- The reduction relation. -/
  Red : Term → Term → Prop

structure TerminalReductionSystem (Term : Type u) extends ReductionSystem Term where
  /-- The terminal terms. -/
  Terminal : Term → Prop
  /-- A terminal term cannot be further reduced. -/
  terminal_not_reducible : ∀ t t', Terminal t → ¬ Red t t'

section MultiStep

/-! ## Multi-step reductions -/

/-- Multi-step reduction relation. -/
abbrev ReductionSystem.MRed (rs : ReductionSystem Term) :=
  Relation.ReflTransGen rs.Red

/-- All multi-step reduction relations are reflexive. -/
@[refl]
theorem ReductionSystem.MRed.refl (rs : ReductionSystem Term) (t : Term) : rs.MRed t t :=
  Relation.ReflTransGen.refl

/-- Any reduction is a multi-step -/
theorem ReductionSystem.MRed.single (rs : ReductionSystem Term) (h : rs.Red a b) :
  rs.MRed a b :=
  Relation.ReflTransGen.single h

end MultiStep

section Steps

inductive ReductionSystem.reducesToInSteps
    (rs : ReductionSystem Term) : Term → Term → ℕ → Prop
  | refl (t : Term) : reducesToInSteps rs t t 0
  | cons (t t' t'' : Term) (n : ℕ) (h₁ : rs.Red t t') (h₂ : reducesToInSteps rs t' t'' n) :
      reducesToInSteps rs t t'' (n + 1)

lemma ReductionSystem.reducesToInSteps.trans {rs : ReductionSystem Term} {a b c : Term} {n m : ℕ}
    (h₁ : reducesToInSteps rs a b n) (h₂ : reducesToInSteps rs b c m) :
    reducesToInSteps rs a c (n + m) := by
  induction h₁ with
  | refl _ => simp only [Nat.zero_add]; exact h₂
  | cons t t' t'' k h_red _ ih =>
    simp only [Nat.add_right_comm]
    exact reducesToInSteps.cons t t' c (k + m) h_red (ih h₂)

lemma ReductionSystem.reducesToInSteps.zero {rs : ReductionSystem Term} {a b : Term}
    (h : reducesToInSteps rs a b 0) :
    a = b := by
  cases h
  rfl

@[simp]
lemma ReductionSystem.reducesToInSteps.zero_iff {rs : ReductionSystem Term} {a b : Term} :
    reducesToInSteps rs a b 0 ↔ a = b := by
  constructor
  · exact reducesToInSteps.zero
  · intro h; subst h; exact reducesToInSteps.refl a


lemma ReductionSystem.reducesToInSteps.succ {rs : ReductionSystem Term} {a b : Term} {n : ℕ}
    (h : reducesToInSteps rs a b (n + 1)) :
    ∃ t', rs.Red a t' ∧ reducesToInSteps rs t' b n := by
  cases h with
  | cons _ t' _ _ h_red h_steps => exact ⟨t', h_red, h_steps⟩

lemma ReductionSystem.reducesToInSteps.succ_iff {rs : ReductionSystem Term} {a b : Term} {n : ℕ} :
    reducesToInSteps rs a b (n + 1) ↔ ∃ t', rs.Red a t' ∧ reducesToInSteps rs t' b n := by
  constructor
  · exact ReductionSystem.reducesToInSteps.succ
  · rintro ⟨t', h_red, h_steps⟩
    exact ReductionSystem.reducesToInSteps.cons a t' b n h_red h_steps

lemma ReductionSystem.reducesToInSteps.succ' {rs : ReductionSystem Term} {a b : Term} {n : ℕ}
    (h : reducesToInSteps rs a b (n + 1)) :
    ∃ t', reducesToInSteps rs a t' n ∧ rs.Red t' b := by
  induction n generalizing a b with
  | zero =>
    obtain ⟨t', h_red, h_steps⟩ := succ h
    rw [zero_iff] at h_steps
    subst h_steps
    exact ⟨a, reducesToInSteps.refl a, h_red⟩
  | succ k ih =>
    obtain ⟨t', h_red, h_steps⟩ := succ h
    obtain ⟨t'', h_steps', h_red'⟩ := ih h_steps
    exact ⟨t'', reducesToInSteps.cons a t' t'' k h_red h_steps', h_red'⟩

lemma ReductionSystem.reducesToInSteps.succ'_iff
    {rs : ReductionSystem Term} {a b : Term} {n : ℕ} :
    reducesToInSteps rs a b (n + 1) ↔ ∃ t', reducesToInSteps rs a t' n ∧ rs.Red t' b := by
  constructor
  · exact succ'
  · rintro ⟨t', h_steps, h_red⟩
    have h_one : reducesToInSteps rs t' b 1 := cons t' b b 0 h_red (refl b)
    have := trans h_steps h_one
    simp only [Nat.add_one] at this
    exact this

lemma ReductionSystem.reducesToInSteps.small_change
    {rs : ReductionSystem Term} {a b : Term} (h : Term → ℕ)
    (h_step : ∀ a b, rs.Red a b → h b ≤ h a + 1)
    (m : ℕ)
    (hevals : rs.reducesToInSteps a b m) :
    h b ≤ h a + m := by
  induction hevals with
  | refl _ => simp
  | cons t t' t'' k h_red _ ih =>
    have h_step' := h_step t t' h_red
    omega

/--
If `g` is a homomorphism from `rs` to `rs'` (i.e., it preserves the reduction relation),
then `reducesToInSteps` is preserved under `g`.
-/
lemma ReductionSystem.reducesToInSteps.map {Term Term' : Type*}
    {rs : ReductionSystem Term} {rs' : ReductionSystem Term'}
    (g : Term → Term') (hg : ∀ a b, rs.Red a b → rs'.Red (g a) (g b))
    {a b : Term} {n : ℕ}
    (h : reducesToInSteps rs a b n) :
    reducesToInSteps rs' (g a) (g b) n := by
  induction h with
  | refl t => exact reducesToInSteps.refl (g t)
  | cons t t' t'' m h_red h_steps ih =>
    exact reducesToInSteps.cons (g t) (g t') (g t'') m (hg t t' h_red) ih

def ReductionSystem.reducesToWithinSteps (rs : ReductionSystem Term) (a b : Term) (n : ℕ) : Prop :=
  ∃ m ≤ n, reducesToInSteps rs a b m

/-- Reflexivity of `reducesToWithinSteps` in 0 steps. -/
lemma ReductionSystem.reducesToWithinSteps.refl {rs : ReductionSystem Term} (a : Term) :
    reducesToWithinSteps rs a a 0 := by
  use 0
  exact ⟨Nat.le_refl 0, reducesToInSteps.refl a⟩

/-- Transitivity of `reducesToWithinSteps` in the sum of the step bounds. -/
@[trans]
lemma ReductionSystem.reducesToWithinSteps.trans {rs : ReductionSystem Term}
    {a b c : Term} {n₁ n₂ : ℕ}
    (h₁ : reducesToWithinSteps rs a b n₁) (h₂ : reducesToWithinSteps rs b c n₂) :
    reducesToWithinSteps rs a c (n₁ + n₂) := by
  obtain ⟨m₁, hm₁, hevals₁⟩ := h₁
  obtain ⟨m₂, hm₂, hevals₂⟩ := h₂
  use m₁ + m₂
  constructor
  · omega
  · exact reducesToInSteps.trans hevals₁ hevals₂

/-- Monotonicity of `reducesToWithinSteps` in the step bound. -/
lemma ReductionSystem.reducesToWithinSteps.mono_steps {rs : ReductionSystem Term}
    {a b : Term} {n₁ n₂ : ℕ}
    (h : reducesToWithinSteps rs a b n₁) (hn : n₁ ≤ n₂) :
    reducesToWithinSteps rs a b n₂ := by
  obtain ⟨m, hm, hevals⟩ := h
  use m
  constructor
  · omega
  · exact hevals

/-- If `h : Term → ℕ` increases by at most 1 on each step of `rs`,
then the value of `h` at the output is at most `h` at the input plus the step bound. -/
lemma ReductionSystem.reducesToWithinSteps.small_change {rs : ReductionSystem Term}
    {a b : Term} (h : Term → ℕ)
    (h_step : ∀ a b, rs.Red a b → h b ≤ h a + 1)
    (n : ℕ)
    (hevals : reducesToWithinSteps rs a b n) :
    h b ≤ h a + n := by
  obtain ⟨m, hm, hevals_m⟩ := hevals
  have := reducesToInSteps.small_change h h_step m hevals_m
  omega

/--
If `g` is a homomorphism from `rs` to `rs'` (i.e., it preserves the reduction relation),
then `reducesToWithinSteps` is preserved under `g`.
-/
lemma ReductionSystem.reducesToWithinSteps.map {Term Term' : Type*}
    {rs : ReductionSystem Term} {rs' : ReductionSystem Term'}
    (g : Term → Term') (hg : ∀ a b, rs.Red a b → rs'.Red (g a) (g b))
    {a b : Term} {n : ℕ}
    (h : reducesToWithinSteps rs a b n) :
    reducesToWithinSteps rs' (g a) (g b) n := by
  obtain ⟨m, hm, hevals⟩ := h
  exact ⟨m, hm, reducesToInSteps.map g hg hevals⟩

/-- A single reduction step gives `reducesToWithinSteps` with bound 1. -/
lemma ReductionSystem.reducesToWithinSteps.single {rs : ReductionSystem Term}
    {a b : Term} (h : rs.Red a b) :
    reducesToWithinSteps rs a b 1 := by
  use 1
  constructor
  · exact Nat.le_refl 1
  · exact reducesToInSteps.cons a b b 0 h (reducesToInSteps.refl b)

/-- `reducesToInSteps` implies `reducesToWithinSteps` with the same bound. -/
lemma ReductionSystem.reducesToWithinSteps.of_reducesToInSteps {rs : ReductionSystem Term}
    {a b : Term} {n : ℕ}
    (h : reducesToInSteps rs a b n) :
    reducesToWithinSteps rs a b n :=
  ⟨n, Nat.le_refl n, h⟩

/-- Zero steps means the terms are equal. -/
lemma ReductionSystem.reducesToWithinSteps.zero {rs : ReductionSystem Term} {a b : Term}
    (h : reducesToWithinSteps rs a b 0) :
    a = b := by
  obtain ⟨m, hm, hevals⟩ := h
  have : m = 0 := Nat.le_zero.mp hm
  subst this
  exact reducesToInSteps.zero hevals

@[simp]
lemma ReductionSystem.reducesToWithinSteps.zero_iff {rs : ReductionSystem Term} {a b : Term} :
    reducesToWithinSteps rs a b 0 ↔ a = b := by
  constructor
  · exact reducesToWithinSteps.zero
  · intro h
    subst h
    exact reducesToWithinSteps.refl a

end Steps

/--
Given a map σ → Option σ, we can construct a terminal reduction system on `σ`
where a term is terminal if it maps to `none` under the given function.
and otherwise is reducible to its `some` value under the given function.
-/
def TerminalReductionSystem.Option {σ : Type*} (f : σ → Option σ) : TerminalReductionSystem σ where
  Red := fun a b => f a = some b
  Terminal := fun a => f a = none
  terminal_not_reducible := by
    intros t t' h_terminal h_red
    simp [h_terminal] at h_red

open Lean Elab Meta Command Term

-- thank you to Kyle Miller for this:
-- https://leanprover.zulipchat.com/#narrow/channel/239415-metaprogramming-.2F-tactics/topic/Working.20with.20variables.20in.20a.20command/near/529324084

/-- A command to create a `ReductionSystem` from a relation, robust to use of `variable `-/
elab "create_reduction_sys" rel:ident name:ident : command => do
  liftTermElabM do
    let rel ← realizeGlobalConstNoOverloadWithInfo rel
    let ci ← getConstInfo rel
    forallTelescope ci.type fun args ty => do
      let throwNotRelation := throwError m!"type{indentExpr ci.type}\nis not a relation"
      unless args.size ≥ 2 do
        throwNotRelation
      unless ← isDefEq (← inferType args[args.size - 2]!) (← inferType args[args.size - 1]!) do
        throwNotRelation
      unless (← whnf ty).isProp do
        throwError m!"expecting Prop, not{indentExpr ty}"
      let params := ci.levelParams.map .param
      let rel := mkAppN (.const rel params) args[0:args.size-2]
      let bundle ← mkAppM ``ReductionSystem.mk #[rel]
      let value ← mkLambdaFVars args[0:args.size-2] bundle
      let type ← inferType value
      addAndCompile <| .defnDecl {
        name := name.getId
        levelParams := ci.levelParams
        type
        value
        safety := .safe
        hints := Lean.ReducibilityHints.abbrev
      }
      addTermInfo' name (.const name.getId params) (isBinder := true)
      addDeclarationRangesFromSyntax name.getId name

/--
  This command adds notations for a `ReductionSystem.Red` and `ReductionSystem.MRed`. This should
  not usually be called directly, but from the `reduction_sys` attribute.

  As an example `reduction_notation foo "β"` will add the notations "⭢β" and "↠β".

  Note that the string used will afterwards be registered as a notation. This means that if you have
  also used this as a constructor name, you will need quotes to access corresponding cases, e.g. «β»
  in the above example.
-/
syntax attrKind "reduction_notation" ident (str)? : command
macro_rules
  | `($kind:attrKind reduction_notation $rs $sym) =>
    `(
      @[nolint docBlame]
      $kind:attrKind notation3 t:39 " ⭢" $sym:str t':39 => (ReductionSystem.Red  $rs) t t'
      @[nolint docBlame]
      $kind:attrKind notation3 t:39 " ↠" $sym:str t':39 => (ReductionSystem.MRed $rs) t t'
     )
  | `($kind:attrKind reduction_notation $rs) =>
    `(
      @[nolint docBlame]
      $kind:attrKind notation3 t:39 " ⭢ " t':39 => (ReductionSystem.Red  $rs) t t'
      @[nolint docBlame]
      $kind:attrKind notation3 t:39 " ↠ " t':39 => (ReductionSystem.MRed $rs) t t'
     )


/--
  This attribute calls the `reduction_notation` command for the annotated declaration, such as in:

  ```
  @[reduction rs "ₙ", simp]
  def PredReduction (a b : ℕ) : Prop := a = b + 1
  ```
-/
syntax (name := reduction_sys) "reduction_sys" ident (ppSpace str)? : attr

initialize Lean.registerBuiltinAttribute {
  name := `reduction_sys
  descr := "Register notation for a relation and its closures."
  add := fun decl stx _ => MetaM.run' do
    match stx with
    | `(attr | reduction_sys $rs $sym) =>
        let mut sym := sym
        unless sym.getString.endsWith " " do
          sym := Syntax.mkStrLit (sym.getString ++ " ")
        let rs := rs.getId.updatePrefix decl.getPrefix |> Lean.mkIdent
        liftCommandElabM <| Command.elabCommand (← `(create_reduction_sys $(mkIdent decl) $rs))
        liftCommandElabM <| (do
          modifyScope ({ · with currNamespace := decl.getPrefix })
          Command.elabCommand (← `(scoped reduction_notation $rs $sym)))
    | `(attr | reduction_sys $rs) =>
        let rs := rs.getId.updatePrefix decl.getPrefix |> Lean.mkIdent
        liftCommandElabM <| Command.elabCommand (← `(create_reduction_sys $(mkIdent decl) $rs))
        liftCommandElabM <| (do
          modifyScope ({ · with currNamespace := decl.getPrefix })
          Command.elabCommand (← `(scoped reduction_notation $rs)))
    | _ => throwError "invalid syntax for 'reduction_sys' attribute"
}

end Cslib
