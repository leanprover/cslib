/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Data.HasTrue
public import Cslib.Foundations.Syntax.HasSubstitution
public import Mathlib.Data.Finset.Basic

/-!
# Local expressions, stores, and evaluation

Choreographic programming and associated languages (like process calculi for modelling distributed
protocol implementations) are typically defined abstracting from how processes locally compute and
store values [Montesi2023].

This module defines this interface. Local signatures (`LocalSig`) define the variables available to
a process. Signatures of networks (`Sig`) assign a local signature to each process. Similarly, we
define local stores (`LocalSig.Store`) mapping local variables to values, and global stores
(`Sig.Store`) mapping processes to their local stores.

## Implementation notes

Stores may assign different value types to different variables. Local computation uses plain Lean
functions and relations (for modelling nondeterminism). Expressions are typed and keep a small
syntax: values, variable reads, pairs, and calls of relations, so that the variables read by an
expression can be computed (`LocalSig.Expr.vars`). A call `.call r e` may evaluate to any `b` such
that `r a b`, where `a` is a value of `e`, which allows for nondeterministic local computations. A
deterministic call of a Lean function `f` is the call of its graph, written `f <$> e` or with the
braced notation `{f e}`.

Processes have independent local signatures, so the same variable name may denote variables of
different types in different processes. A variable of process `p` in a signature `S` has
type `S.Var p α`.

Local signatures include decidable equality of variable names, which is required by the write
operation for stores.

## References

* [F. Montesi, *Introduction to Choreographies*][Montesi2023]
-/

@[expose] public section

namespace Cslib.Mech

/-! ## Local signatures and stores -/

/-- A local signature, specifying variable names with their types. -/
structure LocalSig.{u, v} where
  /-- The type of variable names. -/
  VarName : Type u
  /-- Variable names have decidable equality. -/
  [decEq : DecidableEq VarName]
  /-- The type of the values stored in each variable. -/
  VarType : VarName → Type v

attribute [instance] LocalSig.decEq

namespace LocalSig

/-- A variable of type `α` under the local signature `L`. -/
structure Var (L : LocalSig.{u, v}) (α : Type v) : Type u where
  /-- The variable's name. -/
  name : L.VarName
  /-- Proof that the variable has type `α` in `L`. -/
  has_type : L.VarType name = α

/-- The type `α` of a variable `x : L.Var α`. -/
abbrev Var.Type {L : LocalSig} {α} (_ : L.Var α) := α

/-- Variables of different types necessarily have different names. -/
theorem Var.name_ne_of_type_ne {L : LocalSig} {α β} (h : α ≠ β) (x : L.Var α) (y : L.Var β) :
    x.name ≠ y.name :=
  fun e => h (x.has_type.symm.trans (e ▸ y.has_type))

/-- A local store. -/
def Store (L : LocalSig) := (x : L.VarName) → L.VarType x

/-- Read a typed variable in a local store. Results are stated with the notation `σ[x]`. -/
def Store.read {L : LocalSig} {α} (σ : L.Store) (x : L.Var α) : α :=
  x.has_type.mp (σ x.name)

/-- Write a typed variable in a local store. Results are stated with the notation `σ[x := v]`. -/
def Store.write {L : LocalSig} {α} (σ : L.Store) (x : L.Var α) (v : α) : L.Store :=
  Function.update σ x.name (x.has_type.mpr v)

/-! ### Notation for local stores

A store `σ` is read with `σ[x]` and written with `σ[x := v]`. -/

/-- For any local store `σ`, `σ[x]` is the value of the variable `x` in `σ`. -/
instance Store.instGetElem {L : LocalSig} {α} : GetElem L.Store (L.Var α) α (fun _ _ => True) where
  getElem σ x _ := σ.read x

/-- For any local store `σ`, `σ[x := v]` is the store obtained from `σ` by writing `v` in `x`. -/
instance Store.instHasSubstitution {L : LocalSig} {α} : HasSubstitution L.Store (L.Var α) α where
  subst σ x v := σ.write x v

@[simp, grind =]
theorem Store.read_def {L : LocalSig} {α} (σ : L.Store) (x : L.Var α) :
    σ.read x = σ[x] := rfl

@[simp, grind =]
theorem Store.write_def {L : LocalSig} {α} (σ : L.Store) (x : L.Var α)
    (v : α) : σ.write x v = σ[x := v] := rfl

/-- Two stores are equal if they agree on every read. -/
@[ext, grind ext]
theorem Store.ext {L : LocalSig} {σ₁ σ₂ : L.Store} (h : ∀ α (x : L.Var α), σ₁[x] = σ₂[x]) :
    σ₁ = σ₂ :=
  funext fun y => h _ ⟨y, rfl⟩

/-- The value of a written store at a variable name. -/
theorem Store.subst_apply {L : LocalSig} {α} (σ : L.Store) (x : L.Var α) (v : α) (y : L.VarName) :
    σ[x := v] y = if h : y = x.name then h ▸ x.has_type.mpr v else σ y := by
  split <;> rename_i h
  · subst h
    exact Function.update_self ..
  · exact Function.update_of_ne h ..

/-- Writing a variable preserves the values of all other names. -/
theorem Store.subst_apply_of_ne {L : LocalSig} {α} (σ : L.Store) (x : L.Var α) (v : α)
    {y : L.VarName} (h : y ≠ x.name) : σ[x := v] y = σ y := by
  rw [subst_apply, dite_eq_right h]

/-- Reading a variable after a write. If the variable read has the name of the variable written,
their types are equal and the written value is returned. -/
@[grind =]
theorem Store.getElem_subst {L : LocalSig} {α β} (σ : L.Store) (x : L.Var α) (v : α) (y : L.Var β) :
    σ[x := v][y] =
      if h : y.name = x.name then cast (by rw [← x.has_type, ← y.has_type, h]) v else σ[y] := by
  change y.has_type.mp (σ[x := v] y.name) = _
  split <;> rename_i h
  · rw [subst_apply, dite_eq_left h]
    obtain ⟨yn, rfl⟩ := y
    obtain ⟨xn, rfl⟩ := x
    simp only at h
    subst h
    rfl
  · rw [subst_apply_of_ne _ _ _ h]
    rfl

/-- Reading a variable after writing it returns the written value. -/
@[simp, grind =]
theorem Store.getElem_subst_self {L : LocalSig} {α} (σ : L.Store) (x : L.Var α) (v : α) :
    σ[x := v][x] = v := by
  change x.has_type.mp (σ[x := v] x.name) = v
  simp [subst_apply]

/-- Writing a variable does not affect reading another. -/
@[simp, grind =]
theorem Store.getElem_subst_of_ne {L : LocalSig} {α β} (σ : L.Store) (x : L.Var α) (a : α)
    (y : L.Var β) (h : y.name ≠ x.name) : σ[x := a][y] = σ[y] := by
  change y.has_type.mp (σ[x := a] y.name) = y.has_type.mp (σ y.name)
  rw [subst_apply_of_ne _ _ _ h]

/-- A later write to the same variable overrides an earlier write. -/
@[simp, grind =]
theorem Store.subst_subst_self {L : LocalSig} {α} (σ : L.Store) (x : L.Var α) (a b : α) :
    σ[x := a][x := b] = σ[x := b] := by
  grind

/-- Writes to different variables commute. -/
theorem Store.subst_comm {L : LocalSig} {α β} (σ : L.Store) (x : L.Var α) (y : L.Var β) (a : α)
    (b : β) (h : x.name ≠ y.name) : σ[x := a][y := b] = σ[y := b][x := a] := by
  grind

/-! ## Local expressions -/

/-- A local expression. -/
inductive Expr (L : LocalSig.{u, v}) : Type v → Type (max u (v + 1))
  /-- A value. -/
  | val {α} (v : α) : L.Expr α
  /-- Read a local variable. -/
  | var {α} (x : L.Var α) : L.Expr α
  /-- Evaluate two expressions as a pair. -/
  | pair {α β} (left : L.Expr α) (right : L.Expr β) : L.Expr (α × β)
  /-- Perform the computation `r` (modelled as a relation, in order to allow for nondeterminism) on
    the value of expression `arg`: the result may be any `b` with `r a b`, where `a` is the value of
    `arg`. -/
  | call {α β} (r : α → β → Prop) (arg : L.Expr α) : L.Expr β

/-- Any variable is an expression. -/
instance {L : LocalSig} {α} : Coe (L.Var α) (L.Expr α) := ⟨Expr.var⟩

/-- Apply a Lean function to an expression: the call of its graph. -/
def Expr.map {L : LocalSig} {α β} (f : α → β) (e : L.Expr α) : L.Expr β :=
  .call (fun a b => b = f a) e

/-- Apply a binary Lean function to two expressions. -/
def Expr.map₂ {L : LocalSig} {α β γ} (f : α → β → γ) (a : L.Expr α) (b : L.Expr β) : L.Expr γ :=
  .map (fun p => f p.1 p.2) (.pair a b)

instance {L : LocalSig} : Functor (L.Expr) where
  map := Expr.map

instance {L : LocalSig} : Seq (L.Expr) where
  seq f a := Expr.map₂ (fun g x => g x) f (a ())

/-- The names of the variables read by an expression. -/
def Expr.vars {L : LocalSig} {α} : L.Expr α → Finset L.VarName
  | .val _ => ∅
  | .var x => {x.name}
  | .pair left right => left.vars ∪ right.vars
  | .call _ arg => arg.vars

@[simp, grind =]
theorem Expr.vars_val {L : LocalSig} {α} (v : α) : (Expr.val (L := L) v).vars = ∅ := rfl

@[simp, grind =]
theorem Expr.vars_var {L : LocalSig} {α} (x : L.Var α) : (Expr.var x).vars = {x.name} :=
  rfl

@[simp, grind =]
theorem Expr.vars_pair {L : LocalSig} {α β} (left : L.Expr α) (right : L.Expr β) :
    (Expr.pair left right).vars = left.vars ∪ right.vars := rfl

@[simp, grind =]
theorem Expr.vars_call {L : LocalSig} {α β} (r : α → β → Prop) (arg : L.Expr α) :
    (Expr.call r arg).vars = arg.vars := rfl

@[simp, grind =]
theorem Expr.vars_map {L : LocalSig} {α β} (f : α → β) (e : L.Expr α) :
    (e.map f).vars = e.vars := rfl

/-- Evaluation of expressions relative to a local store: `e.Eval σ v` states that `e` may evaluate
to `v`. -/
inductive Expr.Eval.{u, v} {L : LocalSig.{u, v}} (σ : L.Store) : {α : Type v} → L.Expr α → α → Prop
  /-- A value evaluates to itself. -/
  | val {α} (v : α) : Eval σ (.val v) v
  /-- A variable evaluates to its value in the local store. -/
  | var {α} (x : L.Var α) : Eval σ (.var x) σ[x]
  /-- Two components of a pair evaluate independently. -/
  | pair {α β} {left : L.Expr α} {right : L.Expr β} {a : α} {b : β}
      (hl : Eval σ left a) (hr : Eval σ right b) : Eval σ (.pair left right) (a, b)
  /-- A call evaluates its argument and returns any result related to it. -/
  | call {α β} {r : α → β → Prop} {arg : L.Expr α} {a : α} {b : β}
      (harg : Eval σ arg a) (hr : r a b) : Eval σ (.call r arg) b

/-- A variable has the value stored at its name. -/
@[simp, grind =]
theorem Expr.Eval.var_iff {L : LocalSig} (σ : L.Store) {α} (x : L.Var α) (v : α) :
    Expr.Eval σ (.var x) v ↔ v = σ[x] := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .var x

/-- A call evaluates exactly to the results related to a value of its argument. -/
theorem Expr.Eval.call_iff {L : LocalSig} (σ : L.Store) {α β} (r : α → β → Prop)
    (arg : L.Expr α) (b : β) : Expr.Eval σ (.call r arg) b ↔ ∃ a, arg.Eval σ a ∧ r a b := by
  constructor
  · intro h
    cases h with
    | call harg hr => exact ⟨_, harg, hr⟩
  · rintro ⟨_, harg, hr⟩
    exact .call harg hr

/-- Applying a Lean function evaluates to its value on a value of the argument. -/
@[simp]
theorem Expr.Eval.map_iff {L : LocalSig} (σ : L.Store) {α β} (f : α → β)
    (arg : L.Expr α) (b : β) : (arg.map f).Eval σ b ↔ ∃ a, arg.Eval σ a ∧ b = f a :=
  call_iff σ _ arg b

/-- Two stores agree on a set of variable names if every variable with a name in the set has the
same value in both. -/
def Store.AgreeOn {L : LocalSig} (σ₁ σ₂ : L.Store) (s : Finset L.VarName) : Prop :=
  ∀ {α} (x : L.Var α), x.name ∈ s → σ₁[x] = σ₂[x]

theorem Store.AgreeOn.refl {L : LocalSig} (σ : L.Store) (s : Finset L.VarName) : σ.AgreeOn σ s :=
  fun _ _ => rfl

theorem Store.AgreeOn.symm {L : LocalSig} {σ₁ σ₂ : L.Store} {s : Finset L.VarName}
    (h : σ₁.AgreeOn σ₂ s) : σ₂.AgreeOn σ₁ s :=
  fun x hx => (h x hx).symm

theorem Store.AgreeOn.mono {L : LocalSig} {σ₁ σ₂ : L.Store} {s t : Finset L.VarName}
    (hst : s ⊆ t) (h : σ₁.AgreeOn σ₂ t) : σ₁.AgreeOn σ₂ s :=
  fun x hx => h x (hst hx)

/-- Agreement on a set implies agreement on every subset. -/
theorem Store.AgreeOn.antitone {L : LocalSig} {σ₁ σ₂ : L.Store} : Antitone (AgreeOn σ₁ σ₂ ·) :=
  fun _ _ hst h => h.mono hst

/-- Writing a variable outside a set preserves agreement on the set. -/
theorem Store.agreeOn_subst {L : LocalSig} {α} (σ : L.Store) (x : L.Var α) (v : α)
    {s : Finset L.VarName} (h : x.name ∉ s) : σ[x := v].AgreeOn σ s :=
  fun _ hy => getElem_subst_of_ne _ _ _ _ fun e => h (e ▸ hy)

/-- The values of an expression depend only on the variables it reads. -/
theorem Expr.Eval.of_agreeOn {L : LocalSig} {σ₁ σ₂ : L.Store} {α} {e : L.Expr α} {v : α}
    (h : σ₁.AgreeOn σ₂ e.vars) (he : e.Eval σ₁ v) : e.Eval σ₂ v := by
  induction he with
  | val v => exact .val v
  | var x => rw [h x (by simp)]; exact .var x
  | pair _ _ ihl ihr =>
    exact .pair (ihl (h.mono Finset.subset_union_left)) (ihr (h.mono Finset.subset_union_right))
  | call _ hr ih => exact .call (ih h) hr

/-- Stores that agree on the variables read by an expression give it the same values. -/
theorem Expr.Eval.congr {L : LocalSig} {σ₁ σ₂ : L.Store} {α} {e : L.Expr α} {v : α}
    (h : σ₁.AgreeOn σ₂ e.vars) : e.Eval σ₁ v ↔ e.Eval σ₂ v :=
  ⟨of_agreeOn h, of_agreeOn h.symm⟩

end LocalSig

/-! ### Notation for local expressions

We define the syntactic category `mechExpr` for expressions. A local expression is either a braced
Lean computation `{...}`, which may read local variables with `$`, or a term of type `L.Expr α`,
such as `f <$> x <*> e` or `LocalSig.Expr.var x`. The braced form has priority, so `{...}` is not
read as a Lean term such as a singleton set. Since the longest parse wins, a longer Lean term that
begins with braces, such as `{s} ∪ t`, is still read as a term. The notation `` `(MechExpr| e) ``
produces the `L.Expr` denoted by `e`.

In `{f $x $y}`, the `$`-reads become arguments of a Lean function applied to `x` and `y`, and
`{value}` embeds a Lean value. A `$` name must not also occur as an ordinary identifier in the same
braces: this conservative restriction prevents accidentally capturing a binder. Rename the Lean
identifier or write `f <$> x <*> y` when that distinction is needed. Ambiguous parses containing
`$` are rejected; `f <$> x <*> y` can be used instead. Lean quotations within braces retain their
own antiquotations. -/

/-- Syntactic category for local expressions. -/
declare_syntax_cat mechExpr

/-- A braced Lean computation, which may read local variables with `$`, as in `{$x + 1}`. -/
syntax (name := mechExprBraced) (priority := high) "{" term "}" : mechExpr

/-- A local expression given as a term of type `L.Expr α`. -/
syntax (name := mechExprTerm) term : mechExpr

/-- The local expression denoted by a `mechExpr`. -/
syntax "`(MechExpr| " mechExpr ")" : term

open Lean in
private meta partial def extractLocalReads (stx : Syntax) :
    MacroM (Syntax × Array (Ident × Ident)) := do
  -- Lean quotations have their own antiquotations, which must remain untouched.
  if stx.getKind == ``Lean.Parser.Term.quot || stx.getKind == ``Lean.Parser.Term.dynamicQuot ||
      stx.getKind == ``Lean.Parser.Term.precheckedQuot ||
      stx.getKind == ``Lean.Parser.Command.quot || stx.getKind == ``Lean.Parser.Tactic.quot then
    return (stx, #[])
  if stx.getKind == `term.pseudo.antiquot then
    let target := stx[2]
    unless target.isIdent && stx[1].isNone && stx[3].isNone do
      Macro.throwErrorAt stx "expected a variable name after `$`"
    let binder ← withFreshMacroScope `(ident| localValue)
    return (binder.raw, #[(binder, ⟨target⟩)])
  let mut args := #[]
  let mut reads := #[]
  for arg in stx.getArgs do
    let (arg', found) ← extractLocalReads arg
    args := args.push arg'
    reads := reads ++ found
  if stx.getKind == `choice && !reads.isEmpty then
    Macro.throwErrorAt stx
      "ambiguous Lean syntax containing `$`; write `f <$> x <*> y` for this expression"
  return (stx.setArgs args, reads)

open Lean in
private meta partial def plainIdentifiers (stx : Syntax) : Array Ident := Id.run do
  if stx.getKind == `term.pseudo.antiquot || stx.getKind == ``Lean.Parser.Term.quot ||
      stx.getKind == ``Lean.Parser.Term.dynamicQuot ||
      stx.getKind == ``Lean.Parser.Term.precheckedQuot ||
      stx.getKind == ``Lean.Parser.Command.quot || stx.getKind == ``Lean.Parser.Tactic.quot then
    return #[]
  if stx.isIdent then return #[⟨stx⟩]
  let mut found := #[]
  for arg in stx.getArgs do
    found := found ++ plainIdentifiers arg
  return found

open Lean in
/-- Expand a braced Lean computation into a local expression. -/
private meta def expandBracedExpr (stx : Syntax) : MacroM (TSyntax `term) := do
  let (body, reads) ← extractLocalReads stx
  let plain := plainIdentifiers stx
  for (_, target) in reads do
    if plain.any (fun id => id.getId.eraseMacroScopes == target.getId.eraseMacroScopes) then
      Macro.throwErrorAt target
        "a `$` variable also occurs as a plain identifier in this expression; \
         rename the Lean identifier to avoid capturing a local binder"
  let body : TSyntax `term := ⟨body⟩
  let mut result : TSyntax `term ← if reads.isEmpty then
    `(LocalSig.Expr.map (fun _ : PUnit => $body) (.val PUnit.unit))
  else do
    let mut fn := body
    for (binder, target) in reads.toList.reverse do
      fn ← `(fun ($binder : LocalSig.Var.Type $target) => $fn)
    let first := reads[0]!.2
    `(LocalSig.Expr.map $fn (LocalSig.Expr.var $first))
  for (_, target) in reads.toList.drop 1 do
    result ← `($result <*> LocalSig.Expr.var $target)
  return result

open Lean in
/-- Whether the syntax contains a `$` read outside Lean quotations. -/
private meta partial def hasLocalRead (stx : Syntax) : Bool :=
  if stx.getKind == ``Lean.Parser.Term.quot || stx.getKind == ``Lean.Parser.Term.dynamicQuot ||
      stx.getKind == ``Lean.Parser.Term.precheckedQuot ||
      stx.getKind == ``Lean.Parser.Command.quot || stx.getKind == ``Lean.Parser.Tactic.quot then
    false
  else
    stx.getKind == `term.pseudo.antiquot || stx.getArgs.any hasLocalRead

macro_rules
  | `(`(MechExpr| { $body:term })) => expandBracedExpr body
  | `(`(MechExpr| $e:term)) => do
    if hasLocalRead e then
      Lean.Macro.throwErrorAt e
        "`$` reads are only allowed in a braced computation `{…}` that spans the whole expression"
    return e

/-! ## Signatures of networks -/

set_option linter.checkUnivs false in
/-- The signature of a network, which assigns a local signature to each process. -/
abbrev Sig.{u,v,w} (Pid : Type u) := Pid → LocalSig.{v, w}

namespace Sig

/-- A variable of type `α` of process `p`. -/
abbrev Var {Pid} (S : Sig Pid) (p : Pid) (α : Type*) := (S p).Var α

/-- A local expression of type `α` of process `p`. -/
abbrev Expr {Pid} (S : Sig Pid) (p : Pid) (α : Type*) := (S p).Expr α

/-- A global store represents the memory state of an entire network, mapping each process to a
local store of its own local signature. -/
abbrev Store {Pid} (S : Sig Pid) := (p : Pid) → (S p).Store

/-- Write the local variable `x` of process `p`. Results are stated with the notation
`gs[⟨p, x⟩ := v]`. -/
def Store.write {Pid} [DecidableEq Pid] {S : Sig Pid} {α}
    (gs : S.Store) (p : Pid) (x : S.Var p α) (v : α) : S.Store :=
  Function.update gs p ((gs p)[x := v])

/-! ### Notation for global stores

We define notation for read and write operations on global stores. For any global store `gs`:
- `(gs p)[x]` reads the value of variable `x` at process `p`;
- `gs[⟨p, x⟩ := v]` writes the value `v` in variable `x` at process `p`.
-/

/-- Instance for the write notation `gs[⟨p, x⟩ := v]`. -/
@[default_instance]
instance Store.instHasSubstitution {Pid} [DecidableEq Pid] {S : Sig Pid} {α} :
    HasSubstitution S.Store ((p : Pid) × S.Var p α) α where
  subst gs px v := gs.write px.1 px.2 v

@[simp, grind =]
theorem Store.write_def {Pid} [DecidableEq Pid] {S : Sig Pid} {α}
    (gs : S.Store) (p : Pid) (x : S.Var p α) (v : α) : gs.write p x v = gs[⟨p, x⟩ := v] := rfl

theorem Store.subst_eq_update {Pid} [DecidableEq Pid] {S : Sig Pid} {α}
    (gs : S.Store) (p : Pid) (x : S.Var p α) (v : α) :
    gs[⟨p, x⟩ := v] = Function.update gs p ((gs p)[x := v]) := rfl

/-- The local store of a process after a write operation at that process. -/
@[simp, grind =]
theorem Store.subst_apply_self {Pid} [DecidableEq Pid] {S : Sig Pid} {α}
    (gs : S.Store) (p : Pid) (x : S.Var p α) (v : α) : gs[⟨p, x⟩ := v] p = (gs p)[x := v] := by
  simp [subst_eq_update]

/-- Stores writes are local: writing at one process does not affect the store of another process. -/
@[simp, grind =]
theorem Store.subst_apply_of_ne {Pid} [DecidableEq Pid] {S : Sig Pid} {α}
    (gs : S.Store) (p q : Pid) (x : S.Var p α) (v : α) (h : q ≠ p) :
    gs[⟨p, x⟩ := v] q = gs q := by
  simp [subst_eq_update, h]

/-- Reading a variable just written returns the written value. -/
@[grind =]
theorem Store.getElem_subst_self {Pid} [DecidableEq Pid] {S : Sig Pid} {α}
    (gs : S.Store) (p : Pid) (x : S.Var p α) (v : α) : (gs[⟨p, x⟩ := v] p)[x] = v := by
  simp

/-- Writing one variable preserves the value of another variable of the same process. -/
@[grind =]
theorem Store.getElem_subst_of_name_ne {Pid} [DecidableEq Pid] {S : Sig Pid} {α β}
    (gs : S.Store) (p : Pid) (x : S.Var p α) (a : α) (y : S.Var p β) (h : y.name ≠ x.name) :
    (gs[⟨p, x⟩ := a] p)[y] = (gs p)[y] := by
  simp [h]

/-- A later write to the same process and variable overrides an earlier write. -/
@[simp, grind =]
theorem Store.subst_subst_self {Pid} [DecidableEq Pid] {S : Sig Pid} {α}
    (gs : S.Store) (p : Pid) (x : S.Var p α) (a b : α) :
    gs[⟨p, x⟩ := a][⟨p, x⟩ := b] = gs[⟨p, x⟩ := b] := by
  simp [subst_eq_update]

/-- Writes to distinct processes commute. -/
theorem Store.subst_comm_of_ne {Pid} [DecidableEq Pid] {S : Sig Pid} {α β}
    (gs : S.Store) (p q : Pid) (x : S.Var p α) (y : S.Var q β) (a : α) (b : β) (h : p ≠ q) :
    gs[⟨p, x⟩ := a][⟨q, y⟩ := b] = gs[⟨q, y⟩ := b][⟨p, x⟩ := a] := by
  simp only [subst_eq_update, Function.update_of_ne h, Function.update_of_ne (Ne.symm h)]
  exact Function.update_comm h _ _ _

/-- Writes to different variables of the same process commute. -/
theorem Store.subst_comm_of_name_ne {Pid} [DecidableEq Pid] {S : Sig Pid} {α β}
    (gs : S.Store) (p : Pid) (x : S.Var p α) (y : S.Var p β) (a : α) (b : β)
    (h : x.name ≠ y.name) : gs[⟨p, x⟩ := a][⟨p, y⟩ := b] = gs[⟨p, y⟩ := b][⟨p, x⟩ := a] := by
  simp [subst_eq_update, LocalSig.Store.subst_comm _ _ _ _ _ h]

end Sig

end Cslib.Mech
