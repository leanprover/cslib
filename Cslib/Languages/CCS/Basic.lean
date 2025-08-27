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

/-- Co action. -/
def Act.co (μ : Act Name) : Act Name :=
  match μ with
  | name a => coname a
  | coname a => name a
  | τ => τ

/-- `Act.co` is an involution. -/
theorem Act.co.involution (μ : Act Name) : μ.co.co = μ := by
  cases μ <;> simp only [Act.co]

/-- Contexts. -/
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
theorem Context.complete (p : Process Name Constant) : ∃ c : Context Name Constant, p = (c.fill Process.nil) ∨ ∃ k : Constant, p = c.fill (Process.const k) := by
  induction p
  case nil =>
    exists hole
    left
    simp [fill]
  case pre μ p ih =>
    obtain ⟨c, hc⟩ := ih
    exists pre μ c
    simp [fill]
    assumption
  case par p q ihp ihq =>
    obtain ⟨cp, hcp⟩ := ihp
    exists parL cp q
    simp [fill]
    assumption
  case choice p q ihp ihq =>
    obtain ⟨cp, hcp⟩ := ihp
    exists choiceL cp q
    simp [fill]
    assumption
  case res a p ih =>
    obtain ⟨c, hc⟩ := ih
    exists res a c
    simp [fill]
    assumption
  case const k =>
    exists hole
    right
    exists k

end CCS
