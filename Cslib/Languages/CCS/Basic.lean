/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

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

namespace CCS

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

/-- An action is visible if it a name or a coname. -/
@[grind]
inductive Act.IsVisible : Act Name → Prop where
  | name : IsVisible (Act.name a)
  | coname : IsVisible (Act.coname a)

/-- If an action is visible, it is not `τ`. -/
@[grind, simp]
theorem Act.isVisible_neq_τ {μ : Act Name} (h : μ.IsVisible) : μ ≠ Act.τ := by
  cases μ <;> grind

/-- Checks that an action is the coaction of another. -/
@[grind]
inductive Act.Co {Name : Type u} : Act Name → Act Name → Prop where
  | nc : Act.Co (Act.name a) (Act.coname a)
  | cn : Act.Co (Act.coname a) (Act.name a)

/-- `Act.Co` is symmetric. -/
@[grind, symm]
theorem Act.Co.symm (h : Act.Co μ μ') : Act.Co μ' μ := by grind

/-- If two actions are one the coaction of the other, then they are both visible. -/
@[grind]
theorem Act.co_isVisible (h : Act.Co μ μ') : μ.IsVisible ∧ μ'.IsVisible := by grind

/-- `Act.Co` is decidable if `Name` equality is decidable. -/
instance {Name : Type u} [hdec : DecidableEq Name] {μ μ' : Act Name} :
  Decidable (Act.Co μ μ') := by
  cases μ
  case name a =>
    cases μ'
    case name b =>
      apply Decidable.isFalse
      intro h'
      cases h'
    case coname b =>
      by_cases hab : a = b
      case pos =>
        rw [hab]
        apply Decidable.isTrue
        constructor
      case neg =>
        apply Decidable.isFalse
        intro h'
        cases h'
        contradiction
    case τ =>
      apply Decidable.isFalse
      intro h'
      cases h'
  case coname a =>
    cases μ'
    case name b =>
      by_cases hab : a = b
      case pos =>
        rw [hab]
        apply Decidable.isTrue
        constructor
      case neg =>
        apply Decidable.isFalse
        intro h'
        cases h'
        contradiction
    case coname b =>
      apply Decidable.isFalse
      intro h'
      cases h'
    case τ =>
      apply Decidable.isFalse
      intro h'
      cases h'
  case τ =>
    apply Decidable.isFalse
    intro h'
    cases h'

/-- Contexts. -/
@[grind]
inductive Context (Name : Type u) (Constant : Type v): Type (max u v) where
  | hole
  | pre (μ : Act Name) (c : Context Name Constant)
  | parL (c : Context Name Constant) (q : Process Name Constant)
  | parR (p : Process Name Constant) (c : Context Name Constant)
  | choiceL (c : Context Name Constant) (q : Process Name Constant)
  | choiceR (p : Process Name Constant) (c : Context Name Constant)
  | res (a : Name) (c : Context Name Constant)
deriving DecidableEq

/-- Replaces the hole in a `Context` with a `Process`. -/
@[grind]
def Context.fill {Name : Type u} {Constant : Type v} (c : Context Name Constant) (p : Process Name Constant) : Process Name Constant :=
  match c with
  | hole => p
  | pre μ c => Process.pre μ (c.fill p)
  | parL c r => Process.par (c.fill p) r
  | parR r c => Process.par r (c.fill p)
  | choiceL c r => Process.choice (c.fill p) r
  | choiceR r c => Process.choice r (c.fill p)
  | res a c => Process.res a (c.fill p)

/-- Any `Process` can be obtained by filling a `Context` with an atom. This proves that `Context`
is a complete formalisation of syntactic contexts for CCS. -/
theorem Context.complete (p : Process Name Constant) :
  ∃ c : Context Name Constant, p = (c.fill Process.nil) ∨
  ∃ k : Constant, p = c.fill (Process.const k) := by
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

end CCS
