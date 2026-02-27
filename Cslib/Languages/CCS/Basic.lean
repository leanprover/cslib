/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Syntax.Context
public import Mathlib.Tactic.ToAdditive
public import Mathlib.Tactic.ToDual

@[expose] public section

/-! # Calculus of Communicating Systems (CCS)

CCS [Milner80], as presented in [Sangiorgi2011]. In the semantics (see `CCS.lts`), we adopt the
option of constant definitions (K = P).

## Main definitions
- `CCS.Process`: processes.
- `CCS.Context`: contexts.

## Main results
- `CCS.Context.complete`: any process is equal to some context filled an atomic process
(nil or a constant).

## References

* [R. Milner, *A Calculus of Communicating Systems*][Milner80]
* [D. Sangiorgi, *Introduction to Bisimulation and Coinduction*][Sangiorgi2011]
-/

namespace Cslib.CCS

universe u v

/-- Actions. -/
inductive Act (Name : Type u) : Type u where
  | name (a : Name)
  | coname (a : Name)
  | τ
deriving DecidableEq

/-- Processes. -/
inductive Process (Name : Type u) (Constant : Type v) : Type (max u v) where
  | nil
  | pre (μ : Act Name) (p : Process Name Constant)
  | par (p q : Process Name Constant)
  | choice (p q : Process Name Constant)
  | res (a : Name) (p : Process Name Constant)
  | const (c : Constant)
deriving DecidableEq

namespace Act

/-- An action is visible if it a name or a coname. -/
@[scoped grind]
inductive IsVisible : Act Name → Prop where
  | name : IsVisible (Act.name a)
  | coname : IsVisible (Act.coname a)

/-- If an action is visible, it is not `τ`. -/
@[scoped grind →, simp]
theorem isVisible_neq_τ {μ : Act Name} (h : μ.IsVisible) : μ ≠ Act.τ := by
  cases μ <;> grind

/-- Checks that an action is the coaction of another. -/
@[scoped grind]
inductive Co {Name : Type u} : Act Name → Act Name → Prop where
  | nc : Co (name a) (coname a)
  | cn : Co (coname a) (name a)

/-- `Act.Co` is symmetric. -/
@[scoped grind →, symm]
theorem Co.symm (h : Act.Co μ μ') : Act.Co μ' μ := by grind

/-- If two actions are one the coaction of the other, then they are both visible. -/
@[scoped grind →]
theorem co_isVisible (h : Act.Co μ μ') : μ.IsVisible ∧ μ'.IsVisible := by grind

/-- Checks that an action is the coaction of another. This is the Boolean version of `Act.Co`. -/
@[scoped grind =]
def isCo [DecidableEq Name] (μ μ' : Act Name) : Bool :=
  match μ, μ' with
  | name a, coname b | coname a, name b => a = b
  | _, _ => false

theorem isCo_iff [DecidableEq Name] {μ μ' : Act Name} : isCo μ μ' ↔ Co μ μ' := by
  grind [cases Act]

/-- `Act.Co` is decidable if `Name` equality is decidable. -/
instance [DecidableEq Name] {μ μ' : Act Name} : Decidable (Co μ μ') :=
  decidable_of_decidable_of_iff isCo_iff

end Act

/-- Contexts. -/
@[scoped grind]
inductive Context (Name : Type u) (Constant : Type v) : Type (max u v) where
  | hole
  | pre (μ : Act Name) (c : Context Name Constant)
  | parL (c : Context Name Constant) (q : Process Name Constant)
  | parR (p : Process Name Constant) (c : Context Name Constant)
  | choiceL (c : Context Name Constant) (q : Process Name Constant)
  | choiceR (p : Process Name Constant) (c : Context Name Constant)
  | res (a : Name) (c : Context Name Constant)
deriving DecidableEq

/-- Replaces the hole in a `Context` with a `Process`. -/
@[scoped grind =]
def Context.fill (c : Context Name Constant) (p : Process Name Constant) : Process Name Constant :=
  match c with
  | hole => p
  | pre μ c => Process.pre μ (c.fill p)
  | parL c r => Process.par (c.fill p) r
  | parR r c => Process.par r (c.fill p)
  | choiceL c r => Process.choice (c.fill p) r
  | choiceR r c => Process.choice r (c.fill p)
  | res a c => Process.res a (c.fill p)

instance : HasContext (Process Name Constant) := ⟨Context Name Constant, Context.fill⟩

/-- Definition of context filling. -/
@[scoped grind =]
theorem isContext_def (c : Context Name Constant) (p : Process Name Constant) :
  c[p] = c.fill p := rfl

/-- Any `Process` can be obtained by filling a `Context` with an atom. This proves that `Context`
is a complete formalisation of syntactic contexts for CCS. -/
theorem Context.complete (p : Process Name Constant) :
    ∃ c : Context Name Constant, p = c[Process.nil] ∨
    ∃ k : Constant, p = c[Process.const k] := by
  induction p
  case nil =>
    exists hole
    grind
  case pre μ p ih =>
    obtain ⟨c, hc⟩ := ih
    exists pre μ c
    grind
  case par p q ihp ihq =>
    obtain ⟨cp, hcp⟩ := ihp
    exists parL cp q
    grind
  case choice p q ihp ihq =>
    obtain ⟨cp, hcp⟩ := ihp
    exists choiceL cp q
    grind
  case res a p ih =>
    obtain ⟨c, hc⟩ := ih
    exists res a c
    grind
  case const k =>
    exists hole
    grind

end Cslib.CCS
