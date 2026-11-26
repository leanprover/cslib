/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

module

public import Cslib.Foundations.Syntax.HasSubstitution
public import Mathlib.Data.Multiset.Bind
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Logic.Relation
public import Mathlib.ModelTheory.Syntax

/-!
# Interaction Nets

This file defines interaction nets [Lafont1990] in the textual calculus of
[HassanMackieSato2015], Section 3, and their reduction.

A net is written as a *configuration* `⟨t̄ | Δ⟩`: a sequence of terms `t̄`, the interface of the
net, and a multiset `Δ` of unordered equations between terms. A term is a name or an agent applied
to terms; a term `α(t₁, …, tₙ)` is a tree whose root is the principal port of `α`. A name stands
for a wire: it occurs at most twice in a configuration.

Terms are the first-order terms of Mathlib, `FirstOrder.Language.Term`: the symbols of the
interaction system are the function symbols of a first-order language `L`, a symbol of arity `n`
being an element of `L.Functions n`, and names are the variables. The relation symbols of `L` are
not used.

## Main definitions

- `FirstOrder.Language.Term.names`: the names of a term, counted with multiplicity.
- `Equation`: unordered pairs of terms.
- `Configuration`: a head (sequence of terms) and a body (multiset of equations).
- `Configuration.Linear`: every name occurs at most twice.
- `Rule`: an interaction rule `α(x₁, …, xₙ) = β(y₁, …, yₘ) ⇒ Δ` for a pair of symbols.
- `Rule.Linear`: the parameters are distinct and every name of the rule occurs exactly twice.
- `System`: an interaction system, with at most one rule for each pair of symbols.
- `Equation.subst`: the simultaneous substitution of terms for all names, which extends
  `FirstOrder.Language.Term.subst` to equations.
- `t[x := u]`: the substitution of a term for one name, in a term, an equation or a configuration.
- `Rule.IsInstance`: the substitutions that instantiate a rule on an active pair, with fresh
  names for the internal names of the rule.
- `Step`: one step of reduction, by Communication, Substitution, Collect or Interaction.

## Notation

- `c ⭢[R] c'`: `c` reduces to `c'` in one step with the rules of `R`.
- `c ↠[R] c'`: `c` reduces to `c'` in any number of steps with the rules of `R`.

## Implementation notes

- `FirstOrder.Language.Term.names` is declared in the namespace of Mathlib's terms, so that it
  can be written `t.names`. Mathlib's `FirstOrder.Language.Term.varFinset` forgets the number of
  occurrences of a name, which linearity needs.
- The rule set is not a component of a configuration: it is a parameter of the reduction.
- The conditions on the number of occurrences of names (`Configuration.Linear`, `Rule.Linear`)
  are predicates, not fields of the structures.
- The indirection terms `$t` of [HassanMackieSato2015] belong to its implementation model and are
  not part of this development.
- `System` does not require the rule set to be closed under symmetry.
- `Step` does not choose the fresh names of an Interaction: it accepts every instance of the rule,
  following "we work modulo α-equivalence for bound names" in [HassanMackieSato2015].

## References

* [Y. Lafont, *Interaction Nets*][Lafont1990]
* [Y. Lafont, *Interaction Combinators*][Lafont1997]
* [A. Hassan, I. Mackie, S. Sato, *An Implementation Model for Interaction Nets*]
  [HassanMackieSato2015]
-/

@[expose] public section

open FirstOrder Language

universe u v w

variable {L : Language.{u, v}} {Name : Type w}

/-! ### Terms, equations and configurations -/

/-- The names of a term counted with multiplicity. -/
def FirstOrder.Language.Term.names : L.Term Name → Multiset Name
  | var x     => {x}
  | func _ ts => Finset.univ.val.bind fun i => (ts i).names

namespace Cslib.InteractionNets

/-- An equation `t = u` is an unordered pair of terms. -/
abbrev Equation (L : Language.{u, v}) (Name : Type w) :=
  Sym2 (L.Term Name)

/-- The names of an equation counted with multiplicity. -/
def Equation.names (e : Equation L Name) : Multiset Name :=
  Sym2.lift ⟨fun t u => t.names + u.names, fun _ _ => add_comm _ _⟩ e

/-- A configuration `⟨t̄ | Δ⟩`. -/
structure Configuration (L : Language.{u, v}) (Name : Type w) where
  /-- The head `t̄`: the terms at the interface of the net. -/
  head : List (L.Term Name)
  /-- The body `Δ`: the active pairs and the renamings of the net. -/
  body : Multiset (Equation L Name)

/-- The names of a configuration counted with multiplicity. -/
def Configuration.names (c : Configuration L Name) : Multiset Name :=
  (c.head.map Term.names).sum + c.body.bind Equation.names

/-- A configuration is linear if every name occurs at most twice in it. -/
def Configuration.Linear [DecidableEq Name] (c : Configuration L Name) : Prop :=
  ∀ x, c.names.count x ≤ 2

/-! ### Rules and interaction systems -/

/-- An interaction rule `α(x₁, …, xₙ) = β(y₁, …, yₘ) ⇒ Δ` for the pair of symbols `(α, β)`. -/
structure Rule (L : Language.{u, v}) (Name : Type w) {n m : ℕ}
    (α : L.Functions n) (β : L.Functions m) where
  /-- The parameters `x₁, …, xₙ`: the names of the auxiliary ports of `α`. -/
  xNames : Fin n → Name
  /-- The parameters `y₁, …, yₘ`: the names of the auxiliary ports of `β`. -/
  yNames : Fin m → Name
  /-- The right-hand side of the rule. -/
  Δ : Multiset (Equation L Name)

section Rule

variable {n m : ℕ} {α : L.Functions n} {β : L.Functions m}

/-- The parameters of a rule counted with multiplicity. -/
def Rule.params (r : Rule L Name α β) : Multiset Name :=
  Finset.univ.val.map r.xNames + Finset.univ.val.map r.yNames

/-- The names of a rule counted with multiplicity: its parameters and the names of its
right-hand side. -/
def Rule.names (r : Rule L Name α β) : Multiset Name :=
  r.params + r.Δ.bind Equation.names

/-- A rule is linear if its parameters are distinct and every name occurs exactly twice in it,
or not at all. -/
def Rule.Linear [DecidableEq Name] (r : Rule L Name α β) : Prop :=
  r.params.Nodup ∧ ∀ x, r.names.count x = 2 ∨ r.names.count x = 0

/-- To prove that a rule is linear, it is enough to count the names that occur in it. -/
theorem Rule.linear_of_forall_mem [DecidableEq Name] (r : Rule L Name α β)
    (hp : r.params.Nodup) (h : ∀ x ∈ r.names, r.names.count x = 2) : r.Linear := by
  refine ⟨hp, fun x => ?_⟩
  by_cases hx : x ∈ r.names
  · exact .inl (h x hx)
  · exact .inr (Multiset.count_eq_zero_of_notMem hx)

end Rule

/-- An interaction system: at most one rule for each pair of symbols. -/
structure System (L : Language.{u, v}) (Name : Type w) where
  /-- The rule for the pair of symbols `(α, β)`, if there is one. -/
  rule : {n m : ℕ} → (α : L.Functions n) → (β : L.Functions m) → Option (Rule L Name α β)

/-! ### Substitution

The simultaneous substitution of terms for the names of a term is Mathlib's
`FirstOrder.Language.Term.subst`. -/

/-- The simultaneous substitution, which replaces every name `x` by the term `σ x`, on both sides
of an equation. -/
def Equation.subst (e : Equation L Name) (σ : Name → L.Term Name) : Equation L Name :=
  Sym2.map (fun t => t.subst σ) e

/-- The substitution `t[x := u]`, which replaces the name `x` by the term `u` in `t`.
It replaces every occurrence of `x`. In a linear configuration the name that is replaced has one
occurrence left, which is the case considered in [HassanMackieSato2015]. -/
instance [DecidableEq Name] : HasSubstitution (L.Term Name) Name (L.Term Name) where
  subst t x u := t.subst (Function.update var x u)

/-- The substitution `e[x := u]`, on both sides of an equation. -/
instance [DecidableEq Name] : HasSubstitution (Equation L Name) Name (L.Term Name) where
  subst e x u := e.subst (Function.update var x u)

/-- The substitution `c[x := u]`, on the head and on the body of a configuration. -/
instance [DecidableEq Name] : HasSubstitution (Configuration L Name) Name (L.Term Name) where
  subst c x u := ⟨c.head.map fun t => t[x := u], c.body.map fun e => e[x := u]⟩

/-! ### Instances of a rule -/

section Instance

variable {n m : ℕ} {α : L.Functions n} {β : L.Functions m}

/-- A name is internal to a rule if it occurs in the right-hand side and is not a parameter. -/
def Rule.IsInternal (r : Rule L Name α β) (x : Name) : Prop :=
  x ∈ r.Δ.bind Equation.names ∧ (∀ i, x ≠ r.xNames i) ∧ (∀ j, x ≠ r.yNames j)

/-- The substitution `σ` instantiates the rule `r` on the active pair `α(ts) = β(ss)`.
It replaces the parameters of the rule by the terms `ts` and `ss`, and the internal names of the
rule by names that are pairwise distinct and are not in `avoid`. This is the instance of a rule of
[HassanMackieSato2015], Definition 2, followed by the substitution of the parameters. -/
def Rule.IsInstance (r : Rule L Name α β) (ts : Fin n → L.Term Name) (ss : Fin m → L.Term Name)
    (avoid : Multiset Name) (σ : Name → L.Term Name) : Prop :=
  (∀ i, σ (r.xNames i) = ts i) ∧
  (∀ j, σ (r.yNames j) = ss j) ∧
  ∃ ρ : Name → Name,
    (∀ x, r.IsInternal x → σ x = var (ρ x) ∧ ρ x ∉ avoid) ∧
    (∀ x y, r.IsInternal x → r.IsInternal y → ρ x = ρ y → x = y)

end Instance

/-! ### Reduction -/

/-- One step of reduction of a configuration, with the rules of the system `R`. -/
inductive Step [DecidableEq Name] (R : System L Name) :
    Configuration L Name → Configuration L Name → Prop where
  /-- Communication: `⟨ū | Δ, x = t, x = s⟩ ⭢ ⟨ū | Δ, t = s⟩`. -/
  | communication (us : List (L.Term Name)) (Δ : Multiset (Equation L Name))
      (x : Name) (t s : L.Term Name) :
      Step R
        ⟨us, s(var x, t) ::ₘ s(var x, s) ::ₘ Δ⟩
        ⟨us, s(t, s) ::ₘ Δ⟩
  /-- Substitution: `⟨ū | Δ, β(t̄) = u, x = s⟩ ⭢ ⟨ū | Δ, β(t̄)[x := s] = u⟩`, where `x` occurs
  in `t̄`. -/
  | substitution (us : List (L.Term Name)) (Δ : Multiset (Equation L Name))
      {n : ℕ} (β : L.Functions n) (ts : Fin n → L.Term Name)
      (u : L.Term Name) (x : Name) (s : L.Term Name)
      (hx : x ∈ (func β ts).names) :
      Step R
        ⟨us, s(func β ts, u) ::ₘ s(var x, s) ::ₘ Δ⟩
        ⟨us, s((func β ts)[x := s], u) ::ₘ Δ⟩
  /-- Collect: `⟨ū | Δ, x = s⟩ ⭢ ⟨ū[x := s] | Δ⟩`, where `x` occurs in `ū`. -/
  | collect (us : List (L.Term Name)) (Δ : Multiset (Equation L Name))
      (x : Name) (s : L.Term Name)
      (hx : x ∈ (us.map Term.names).sum) :
      Step R
        ⟨us, s(var x, s) ::ₘ Δ⟩
        ⟨us.map fun t => t[x := s], Δ⟩
  /-- Interaction: `⟨ū | Δ, α(t̄) = β(s̄)⟩ ⭢ ⟨ū | Δ, Δᵣ[x̄ := t̄, ȳ := s̄]⟩`, where
  `α(x̄) = β(ȳ) ⇒ Δᵣ` is an instance of the rule of `R` for `(α, β)`, whose internal names do not
  occur in the configuration. -/
  | interaction (us : List (L.Term Name)) (Δ : Multiset (Equation L Name))
      {n m : ℕ} (α : L.Functions n) (β : L.Functions m)
      (ts : Fin n → L.Term Name) (ss : Fin m → L.Term Name)
      (r : Rule L Name α β) (σ : Name → L.Term Name)
      (hr : R.rule α β = some r)
      (hσ : r.IsInstance ts ss (Configuration.names ⟨us, s(func α ts, func β ss) ::ₘ Δ⟩) σ) :
      Step R
        ⟨us, s(func α ts, func β ss) ::ₘ Δ⟩
        ⟨us, r.Δ.map (fun e => e.subst σ) + Δ⟩

/-- `c ⭢[R] c'`: the configuration `c` reduces to `c'` in one step with the rules of `R`. -/
scoped notation:39 c:39 " ⭢[" R "] " c':39 => Step R c c'

/-- `c ↠[R] c'`: the configuration `c` reduces to `c'` in any number of steps with the rules
of `R`. -/
scoped notation:39 c:39 " ↠[" R "] " c':39 => Relation.ReflTransGen (Step R) c c'

end Cslib.InteractionNets
