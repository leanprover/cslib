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


-- TODO refactor the contents of this section into ReductionSystem
-- then delete them
section EvalsToJunk



/-- `f` eventually reaches `b` when repeatedly evaluated on `a`, in exactly `steps` steps. -/
def EvalsToInTime {σ : Type*} (f : σ → Option σ) (a : σ) (b : Option σ) (steps : ℕ) : Prop :=
  (· >>= f)^[steps] a = b

/-- Reflexivity of `EvalsTo` in 0 steps. -/
lemma EvalsToInTime.refl {σ : Type*} (f : σ → Option σ) (a : σ) : EvalsToInTime f a (some a) 0 :=
  rfl

/-- Transitivity of `EvalsTo` in the sum of the numbers of steps. -/
@[trans]
lemma EvalsToInTime.trans {σ : Type*} (f : σ → Option σ) (a : σ) (b : σ) (c : Option σ)
    (steps₁ steps₂ : ℕ) (h₁ : EvalsToInTime f a b steps₁) (h₂ : EvalsToInTime f b c steps₂) :
    EvalsToInTime f a c (steps₂ + steps₁) := by
  simp only [EvalsToInTime] at *; rw [Function.iterate_add_apply, h₁, h₂]

/-- If we evaluate to some state in n+1 steps, there is an intermediate state
    that we reach in n steps, and then one more step reaches the final state. -/
lemma EvalsToInTime.succ_decompose {σ : Type*} (f : σ → Option σ) (a : σ) (b : σ)
    (n : ℕ) (h : EvalsToInTime f a (some b) (n + 1)) :
    ∃ c : σ, EvalsToInTime f a (some c) n ∧ f c = some b := by
  simp only [EvalsToInTime, Function.iterate_succ_apply'] at h
  match hc' : (· >>= f)^[n] (some a) with
  | none => simp_all
  | some c => exact ⟨c, hc', by simp_all⟩

lemma EvalsToInTime.succ_iff {σ : Type*} (f : σ → Option σ) (a : σ) (b : σ) (n : ℕ) :
    EvalsToInTime f a (some b) (n + 1) ↔ ∃ c : σ, EvalsToInTime f a (some c) n ∧ f c = some b :=
  ⟨succ_decompose f a b n, fun ⟨_, hc_eval, hc_step⟩ => by
    simp only [EvalsToInTime, Function.iterate_succ_apply'] at hc_eval ⊢;
    rw [hc_eval]; exact hc_step⟩

theorem Turing.BinTM0.EvalsToInTime.congr.extracted_1_2.{u_2, u_1}
    {σ : Type u_1} {σ' : Type u_2} (f : σ → Option σ)
    (f' : σ' → Option σ') (g : σ → σ')
    (hg : ∀ (x : σ), Option.map g (f x) = f' (g x)) (n : ℕ) (a : σ) :
    (Option.map g ((flip Option.bind f)^[n] (some a))).bind f' =
      ((flip Option.bind f)^[n] (some a)).bind fun a ↦ f' (g a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Function.iterate_succ_apply, flip, Option.bind_some, <- hg] at ih ⊢
    grind





/--
If `f` is homomorphic to `f'` via `g`, then if `f` evals to `b` from `a` in `steps` steps,
then `f'` evals to `g b` from `g a` in `steps` steps.
-/
lemma EvalsToInTime.map {σ σ' : Type*} (f : σ → Option σ) (f' : σ' → Option σ')
    (g : σ → σ') (hg : ∀ x, Option.map g (f x) = f' (g x))
    (a : σ) (b : Option σ)
    (steps : ℕ)
    (h : EvalsToInTime f a b steps) : EvalsToInTime f' (g a) (Option.map g b) steps := by
  induction steps generalizing a b with
  | zero =>
    simp only [EvalsToInTime, Option.bind_eq_bind, Function.iterate_zero, id_eq] at h ⊢
    subst h
    rfl
  | succ n ih =>
    simp only [EvalsToInTime, Option.bind_eq_bind, Function.iterate_succ_apply',
      forall_eq'] at h ih ⊢
    subst h
    rw [ih]
    clear ih
    simp only [Option.map_bind, Function.comp_apply, hg]
    exact Turing.BinTM0.EvalsToInTime.congr.extracted_1_2 f f' g hg n a

/--
If `h : σ → ℕ` increases by at most 1 on each step of `f`,
then the value of `h` at the output after `steps` steps is at most `h` at the input plus `steps`.
-/
lemma EvalsToInTime.small_change {σ : Type*} (f : σ → Option σ) (h : σ → ℕ)
    (h_step : ∀ a b, f a = some b → h b ≤ h a + 1)
    (a : σ) (b : σ)
    (steps : ℕ)
    (hevals : EvalsToInTime f a b steps) :
    h b ≤ h a + steps := by
  induction steps generalizing a b with
  | zero =>
    simp only [EvalsToInTime, Option.bind_eq_bind, Function.iterate_zero, id_eq, Option.some.injEq,
      add_zero] at hevals ⊢
    subst hevals
    exact Nat.le_refl (h a)
  | succ n ih =>
    rw [EvalsToInTime.succ_iff] at hevals
    obtain ⟨c, hevals_n, h_step_eq⟩ := hevals
    specialize ih a c hevals_n
    specialize h_step c b h_step_eq
    omega


-- m -> step_bound
/-- `f` eventually reaches `b` in at most `m` steps when repeatedly
evaluated on `a`. -/
def EvalsToWithinTime {σ : Type*} (f : σ → Option σ) (a : σ) (b : Option σ) (m : ℕ) : Prop :=
  ∃ steps ≤ m, EvalsToInTime f a b steps

/-- Reflexivity of `EvalsToWithinTime` in 0 steps. -/
def EvalsToWithinTime.refl {σ : Type*} (f : σ → Option σ) (a : σ) :
    EvalsToWithinTime f a (some a) 0 := by
  use 0
  exact if_false_right.mp rfl

/-- Transitivity of `EvalsToWithinTime` in the sum of the numbers of steps. -/
@[trans]
def EvalsToWithinTime.trans {σ : Type*} (f : σ → Option σ) (m₁ : ℕ) (m₂ : ℕ) (a : σ) (b : σ)
    (c : Option σ) (h₁ : EvalsToWithinTime f a b m₁) (h₂ : EvalsToWithinTime f b c m₂) :
    EvalsToWithinTime f a c (m₂ + m₁) := by
  obtain ⟨steps₁, hsteps₁, hevals₁⟩ := h₁
  obtain ⟨steps₂, hsteps₂, hevals₂⟩ := h₂
  use steps₂ + steps₁
  constructor
  · omega
  · exact EvalsToInTime.trans f a b c steps₁ steps₂ hevals₁ hevals₂

def EvalsToWithinTime.map {σ σ' : Type*} (f : σ → Option σ) (f' : σ' → Option σ')
    (g : σ → σ') (hg : ∀ x, Option.map g (f x) = f' (g x))
    (a : σ) (b : Option σ)
    (m : ℕ)
    (h : EvalsToWithinTime f a b m) : EvalsToWithinTime f' (g a) (Option.map g b) m := by
  obtain ⟨steps, hsteps, hevals⟩ := h
  use steps
  constructor
  · exact hsteps
  · exact EvalsToInTime.map f f' g hg a b steps hevals

/--
Monotonicity of `EvalsToWithinTime` in the time bound.
-/
def EvalsToWithinTime.mono_time {σ : Type*} (f : σ → Option σ) (a : σ) (b : Option σ)
    {m₁ m₂ : ℕ} (h : EvalsToWithinTime f a b m₁) (hm : m₁ ≤ m₂) : EvalsToWithinTime f a b m₂ := by
  obtain ⟨steps, hsteps, hevals⟩ := h
  use steps
  simp_all only
  simp
  omega

lemma EvalsToWithinTime.small_change {σ : Type*} (f : σ → Option σ) (h : σ → ℕ)
    (h_step : ∀ a b, f a = some b → h b ≤ h a + 1)
    (a : σ) (b : σ)
    (m : ℕ)
    (hevals : EvalsToWithinTime f a (some b) m) :
    h b ≤ h a + m := by
  obtain ⟨steps, hsteps, hevals_steps⟩ := hevals
  have := EvalsToInTime.small_change f h h_step a b steps hevals_steps
  omega


end EvalsToJunk

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
