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

variable (Name : Type u) (Constant : Type v)

namespace CCS

/-- Actions. -/
inductive Act : Type u where
  | name (a : Name)
  | coname (a : Name)
  | τ
deriving DecidableEq

/-- Processes. -/
inductive Process : Type (max u v) where
  | nil
  | pre (μ : Act Name) (p : Process)
  | par (p q : Process)
  | choice (p q : Process)
  | res (a : Name) (p : Process)
  | const (c : Constant)
deriving DecidableEq

/-- An action is visible if it a name or a coname. -/
@[grind]
def Act.IsVisible (μ : Act Name) : Prop :=
  match μ with
  | name _ => True
  | coname _ => True
  | τ => False

/-- The type of visible actions. -/
abbrev VisibleAct := { μ : Act Name // μ.IsVisible }

instance : Coe (VisibleAct Name) (Act Name) where
  coe μ := μ.val

@[cases_eliminator, elab_as_elim]
def VisibleAct.casesOn {Name : Type u} {motive : VisibleAct Name → Sort _} (μ : VisibleAct Name)
  (name : (a : Name) → motive ⟨Act.name a, by constructor⟩)
  (coname : (a : Name) → motive ⟨Act.coname a, by constructor⟩) :
  motive μ := by
  rcases μ with ⟨μ, hv⟩
  cases μ
  case mk.name a =>
    apply name a
  case mk.coname a =>
    apply coname a
  case mk.τ =>
    cases hv

@[elab_as_elim]
def VisibleAct.rec {Name : Type u} {motive : VisibleAct Name → Sort _}
  (name : (a : Name) → motive ⟨Act.name a, by simp [Act.IsVisible]⟩)
  (coname : (a : Name) → motive ⟨Act.coname a, by simp [Act.IsVisible]⟩)
  (μ : VisibleAct Name) :
  motive μ := by
  rcases μ with ⟨μ, hv⟩
  cases μ
  case mk.name a =>
    apply name a
  case mk.coname a =>
    apply coname a
  case mk.τ =>
    cases hv

@[elab_as_elim]
def VisibleAct.recOn {Name : Type u} {motive : VisibleAct Name → Sort _} (μ : VisibleAct Name)
  (name : (a : Name) → motive ⟨Act.name a, by simp [Act.IsVisible]⟩)
  (coname : (a : Name) → motive ⟨Act.coname a, by simp [Act.IsVisible]⟩) :
  motive μ := by
  rcases μ with ⟨μ, hv⟩
  cases μ
  case mk.name a =>
    apply name a
  case mk.coname a =>
    apply coname a
  case mk.τ =>
    cases hv

@[grind, simp]
theorem VisibleAct.neq_τ (μ : VisibleAct Name) : μ.val ≠ Act.τ := by
  cases μ <;> grind

/-- Co action. -/
@[grind]
def VisibleAct.co {Name : Type u} (μ : VisibleAct Name) : VisibleAct Name :=
  match μ with
  | ⟨Act.name a, _⟩ => ⟨Act.coname a, True.intro⟩
  | ⟨Act.coname a, _⟩ => ⟨Act.name a, True.intro⟩

/-- `Act.co` is an involution. -/
theorem Act.co.involution (μ : VisibleAct Name) : μ.co.co = μ := by
  simp only [VisibleAct.co]
  grind [VisibleAct.co]

/-- Contexts. -/
@[grind]
inductive Context : Type (max u v) where
  | hole
  | pre (μ : Act Name) (c : Context)
  | parL (c : Context) (q : Process Name Constant)
  | parR (p : Process Name Constant) (c : Context)
  | choiceL (c : Context) (q : Process Name Constant)
  | choiceR (p : Process Name Constant) (c : Context)
  | res (a : Name) (c : Context)
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
