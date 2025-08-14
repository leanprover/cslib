/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Kenny Lau
-/

import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Ring.CharZero
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.SuccPred
import Mathlib.Order.SuccPred.WithBot

universe u

/-- A type `α` has a computable `fresh` function if it is always possible, for any finite set
of `α`, to compute a fresh element not in the set. -/
class HasFresh (α : Type u) where
  /-- Given a finite set, returns an element not in the set. -/
  fresh : Finset α → α
  /-- Proof that `fresh` returns a fresh element for its input set. -/
  fresh_notMem (s : Finset α) : fresh s ∉ s

attribute [simp] HasFresh.fresh_notMem

/-- An existential version of the `HasFresh` typeclass. This is useful for the sake of brevity
in proofs. -/
theorem HasFresh.fresh_exists {α : Type u} [HasFresh α] (s : Finset α) : ∃ a, a ∉ s :=
  ⟨fresh s, fresh_notMem s⟩

open Lean Elab Term Meta Parser Tactic in
/-- 
  Given a `HasFresh Var` instance, this elaborator automatically constructs a term that is
  fresh with respect to variables in the local context. It creates a union of any variables, finite
  sets of variables, and results of a provided function for free variables (TODO).
-/
elab "fresh_union" cfg:optConfig var:term : term => do
  -- the type of our variables
  let var ← elabType var

  -- TODO: handle the optConfig
  logWarning m!"Configuration{cfg} not yet implemented."

  let mut finsets := #[]

  -- construct ∅
  let dl ← getDecLevel var
  let FinsetType := mkApp (mkConst ``Finset [dl]) var
  let EmptyCollectionInst ← synthInstance (mkApp (mkConst ``EmptyCollection [dl]) FinsetType)
  let empty := 
    mkApp2  (mkConst ``EmptyCollection.emptyCollection [dl]) FinsetType EmptyCollectionInst

  let SingletonInst ← synthInstance (mkApp2 (mkConst ``Singleton [dl, dl]) var FinsetType)

  for ldecl in (← getLCtx) do
    if !ldecl.isImplementationDetail then
      let type ← inferType (mkFVar ldecl.fvarId)
      -- singleton variables
      if (← isDefEq type var) then
        let singleton := 
          mkApp4 (mkConst ``Singleton.singleton [dl, dl]) var FinsetType SingletonInst ldecl.toExpr
        finsets := finsets.push singleton
      else
      -- any finite sets
      match type.getAppFnArgs with
      | (``Finset, #[var']) => if (← isDefEq var var') then finsets := finsets.push ldecl.toExpr
      | _ => pure ()

  -- construct a union fold
  let UnionInst ← synthInstance (mkApp (mkConst ``Union [dl]) FinsetType)
  let UnionFinset := mkApp2 (mkConst `Union.union [dl]) FinsetType UnionInst
  let union := finsets.foldl (mkApp2 UnionFinset) empty
    
  -- TODO : simp only [Finset.empty_union, Finset.union_assoc, Finset.mem_union, not_or]
  --        then recursively destruct the conjunction?
  return union

-- TODO: move this into a test once finalized
section example_tactic

variable (Var : Type) [DecidableEq Var] [HasFresh Var]

variable (Term : Type) (q : Var)
def fv : Term → Finset Var := fun _ ↦ {q}

open HasFresh

set_option pp.rawOnError true in
example (x : Var) (xs : Finset Var) : ∃ y, x ≠ y ∧ y ∉ xs := by
  let ⟨fresh, _⟩ := HasFresh.fresh_exists (fresh_union (free := fv) Var)
  exists fresh
  aesop

end example_tactic

export HasFresh (fresh fresh_notMem fresh_exists)

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
