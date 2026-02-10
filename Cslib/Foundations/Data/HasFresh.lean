/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Kenny Lau
-/

module

public import Cslib.Init
public import Mathlib.Analysis.Normed.Field.Lemmas

@[expose] public section

universe u

namespace Cslib

/-- A type `α` has a computable `fresh` function if it is always possible, for any finite set
of `α`, to compute a fresh element not in the set. -/
class HasFresh (α : Type u) where
  /-- Given a finite set, returns an element not in the set. -/
  fresh : Finset α → α
  /-- Proof that `fresh` returns a fresh element for its input set. -/
  fresh_notMem (s : Finset α) : fresh s ∉ s

attribute [grind <=] HasFresh.fresh_notMem

/-- An existential version of the `HasFresh` typeclass. This is useful for the sake of brevity
in proofs. -/
theorem HasFresh.fresh_exists {α : Type u} [HasFresh α] (s : Finset α) : ∃ a, a ∉ s :=
  ⟨fresh s, fresh_notMem s⟩

public meta section

open Lean Elab Term Meta Parser Tactic

/-- Configuration for the `free_union` term elaborator. -/
structure FreeUnionConfig where
  /-- For `free_union Var`, include all `x : Var`. Defaults to true. -/
  singleton : Bool := true
  /-- For `free_union Var`, include all `xs : Finset Var`. Defaults to true. -/
  finset : Bool := true

/-- Elaborate a FreeUnionConfig. -/
declare_config_elab elabFreeUnionConfig FreeUnionConfig

/--
  Given a `DecidableEq Var` instance, this elaborator automatically constructs
  the union of any variables, finite sets of variables, and optionally the
  results of provided functions mapping to variables. This is configurable with
  optional boolean boolean arguments `singleton` and `finset`.

  As an example, consider the following:

  ```
  variable (x : ℕ) (xs : Finset ℕ) (var : String)

  def f (_ : String) : Finset ℕ := {1, 2, 3}
  def g (_ : String) : Finset ℕ := {4, 5, 6}

  -- info: ∅ ∪ {x} ∪ id xs : Finset ℕ
  #check free_union ℕ

  -- info: ∅ ∪ {x} ∪ id xs ∪ f var ∪ g var : Finset ℕ
  #check free_union [f, g] ℕ

  info: ∅ ∪ id xs : Finset ℕ
  #check free_union (singleton := false) ℕ

  -- info: ∅ ∪ {x} : Finset ℕ
  #check free_union (finset := false) ℕ

  -- info: ∅ : Finset ℕ
  #check free_union (singleton := false) (finset := false) ℕ
  ```
-/
syntax (name := freeUnion) "free_union" optConfig (" [" (term,*) "]")? term : term

set_option linter.style.emptyLine false in
/-- Elaborator for `free_union`. -/
@[term_elab freeUnion]
def HasFresh.freeUnion : TermElab := fun stx _ => do
  match stx with
  | `(free_union $cfg $[[$maps,*]]? $var:term) =>
    let cfg ← elabFreeUnionConfig cfg |>.run { elaborator := .anonymous } |>.run' { goals := [] }

    -- the type of our variables
    let var ← elabType var

    -- maps to variables
    let maps := maps.map (·.getElems) |>.getD #[]
    let mut maps ← maps.mapM (flip elabTerm none)

    -- construct ∅
    let dl ← getDecLevel var
    let FinsetType := mkApp (mkConst ``Finset [dl]) var
    let EmptyCollectionInst ← synthInstance (mkApp (mkConst ``EmptyCollection [dl]) FinsetType)
    let empty :=
      mkAppN (mkConst ``EmptyCollection.emptyCollection [dl]) #[FinsetType, EmptyCollectionInst]

    -- singleton variables
    if cfg.singleton then
      let SingletonInst ← synthInstance <| mkAppN (mkConst ``Singleton [dl, dl]) #[var, FinsetType]
      let singleton_map :=
        mkAppN (mkConst ``Singleton.singleton [dl, dl]) #[var, FinsetType, SingletonInst]
      maps := maps.push singleton_map

    -- any finite sets
    if cfg.finset then
      let id_map := mkApp (mkConst ``id [← getLevel var]) FinsetType
      maps := maps.push id_map

    let mut finsets := #[]

    for ldecl in (← getLCtx) do
      if !ldecl.isImplementationDetail then
        let local_type ← ldecl.toExpr |> inferType >=> whnf
        for map in maps do
          if let Expr.forallE _ dom _ _ := ← inferType map then
            if (←isDefEq local_type dom) then
              finsets := finsets.push (mkApp map ldecl.toExpr)

    -- construct a union fold
    let UnionInst ← synthInstance (mkApp (mkConst ``Union [dl]) FinsetType)
    let UnionFinset := mkAppN (mkConst ``Union.union [dl]) #[FinsetType, UnionInst]
    let union := finsets.foldl (mkApp2 UnionFinset) empty

    return union
  | _ => throwUnsupportedSyntax

end

export HasFresh (fresh fresh_notMem fresh_exists)

/-- `HasFresh α` implies a computably infinite type. -/
instance HasFresh.to_infinite (α : Type u) [HasFresh α] : Infinite α := by
  apply Infinite.of_not_fintype
  rintro ⟨elems, _⟩
  grind [fresh_notMem elems]

/-- All infinite types have an associated (at least noncomputable) fresh function.
This, in conjunction with `HasFresh.to_infinite`, characterizes `HasFresh`. -/
noncomputable instance HasFresh.of_infinite (α : Type u) [Infinite α] : HasFresh α where
  fresh s := Infinite.exists_notMem_finset s |>.choose
  fresh_notMem s := by grind

open Finset in
/-- Construct a fresh element from an embedding of `ℕ` using `Nat.find`. -/
def HasFresh.ofNatEmbed {α : Type u} [DecidableEq α] (e : ℕ ↪ α) : HasFresh α where
  fresh s := e (Nat.find (p := fun n ↦ e n ∉ s) ⟨(s.preimage e e.2.injOn).max.succ,
    fun h ↦ not_lt_of_ge (le_max <| mem_preimage.2 h) (WithBot.lt_succ _)⟩)
  fresh_notMem s := Nat.find_spec (p := fun n ↦ e n ∉ s) _

/-- Construct a fresh element given a function `f` with `x < f x`. -/
def HasFresh.ofSucc {α : Type u} [Inhabited α] [SemilatticeSup α] (f : α → α) (hf : ∀ x, x < f x) :
    HasFresh α where
  fresh s := if hs : s.Nonempty then f (s.sup' hs id) else default
  fresh_notMem s h := if hs : s.Nonempty
    then not_le_of_gt (hf (s.sup' hs id)) <| by rw [dif_pos hs] at h; exact s.le_sup' id h
    else hs ⟨_, h⟩

/-- `ℕ` has a computable fresh function. -/
instance : HasFresh ℕ :=
  .ofSucc (· + 1) Nat.lt_add_one

/-- `ℤ` has a computable fresh function. -/
instance : HasFresh ℤ :=
  .ofSucc (· + 1) Int.lt_succ

/-- `ℚ` has a computable fresh function. -/
instance : HasFresh ℚ :=
  .ofSucc (· + 1) fun x ↦ lt_add_of_pos_right x one_pos

/-- If `α` has a computable fresh function, then so does `Finset α`. -/
instance {α : Type u} [DecidableEq α] [HasFresh α] : HasFresh (Finset α) :=
  .ofSucc (fun s ↦ insert (fresh s) s) fun s ↦ Finset.ssubset_insert <| fresh_notMem s

/-- If `α` is inhabited, then `Multiset α` has a computable fresh function. -/
instance {α : Type u} [DecidableEq α] [Inhabited α] : HasFresh (Multiset α) :=
  .ofSucc (fun s ↦ default ::ₘ s) fun _ ↦ Multiset.lt_cons_self _ _

/-- `ℕ → ℕ` has a computable fresh function. -/
instance : HasFresh (ℕ → ℕ) :=
  .ofSucc (fun f x ↦ f x + 1) fun _ ↦ Pi.lt_def.2 ⟨fun _ ↦ Nat.le_succ _, 0, Nat.lt_succ_self _⟩

end Cslib
