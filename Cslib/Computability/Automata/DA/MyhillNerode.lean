/-
Copyright (c) 2026 Akhilesh Balaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji
-/

module

public import Cslib.Computability.Automata.DA.Basic
public import Cslib.Computability.Automata.DA.Congr
public import Cslib.Computability.Languages.RegularLanguage
public import Cslib.Computability.Languages.Congruences.RightCongruence
public import Mathlib.Computability.Language

@[expose] public section

/-! # All three subparts of the Myhill-Nerode Theorem for DFAs

(1) `L` regular iff. `∼_L` has a finite number of equivalence classes `N`.
(2) `N` is the number of states in the minimal DFA accepting `L`.
(3) The minimal DFA is unique up to unique isomorphism. That is, for any
    minimal DFA acceptor, there exists exactly one isomorphism from it to the
    following one:

  > Let each equivalence class `⟦ x ⟧` correspond to a state, and let state
  transitions be `a : ⟦ x ⟧ → ⟦ x a ⟧` for each `a ∈ Σ`.
  Let the starting state be `⟦ ϵ ⟧`, and the accepting states be `⟦ x ⟧` where
  `x ∈ L`.

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][Hopcroft2006]
-/

namespace Language

variable {α : Type} {l m : Language α}

def RightQuotient (L : Language α) (y : List α) : Language α := { x | x ++ y ∈ L }

end Language

namespace Cslib

open Cslib
open scoped RightCongruence

open Language

namespace Automata.DA
open Acceptor

variable {α : Type} {l m : Language α}

def NerodeCongruence (l : Language α) : RightCongruence α where
  r x y := ∀ z, x ++ z ∈ l ↔ y ++ z ∈ l
  iseqv := ⟨fun _ _ => Iff.rfl, fun h z => (h z).symm, fun h_1 h_2 z => (h_1 z).trans (h_2 z)⟩
  right_cov := ⟨fun a {x y} (h : ∀ z, x ++ z ∈ l ↔ y ++ z ∈ l) z =>
    List.append_assoc x a z ▸ List.append_assoc y a z ▸ h (a ++ z)⟩

def NerodeCongruence.toFinAcc (l : Language α) : 
    DA.FinAcc (Quotient (NerodeCongruence l).eq) α :=
  letI c := NerodeCongruence l
  { c.toDA with
    accept := {q | Quotient.lift (fun x => x ∈ l) (by
      intro x y hxy
      simpa using hxy []) q} }

@[simp, scoped grind =]
theorem nerodecongruence_to_finacc_acc (l : Language α) :
    language (NerodeCongruence.toFinAcc l) = l := by
      ext x
      simp [NerodeCongruence.toFinAcc, language, Acceptor.Accepts]
      exact Iff.of_eq rfl

theorem nerodeCongruence_accepts_apply
    (M : DA.FinAcc State α) (x y : List α) :
    (NerodeCongruence (language M)).r x y ↔
      ∀ z,
        M.mtr (M.mtr M.start x) z ∈ M.accept ↔
        M.mtr (M.mtr M.start y) z ∈ M.accept := by
  simp only [FLTS.mtr, ← List.foldl_append]
  rfl

theorem IsRegular.finite_range_nerode_quotient (h : l.IsRegular) :
    Finite (Quotient (NerodeCongruence l).eq) := by
  rcases IsRegular.iff_dfa.mp h with ⟨State, hFin, M, hM⟩
  rw [← hM]
  apply Finite.of_surjective
    (fun s : State => Quotient.mk (NerodeCongruence (language M)).eq
      (Classical.epsilon (fun x => M.mtr M.start x = s)))
  intro q
  induction q using Quotient.inductionOn with
  | h x =>
    exact ⟨M.mtr M.start x, Quotient.sound (by
      change (NerodeCongruence (language M)).r _ x
      rw [nerodeCongruence_accepts_apply]
      intro z
      have heps : M.mtr M.start (Classical.epsilon
          (fun y => M.mtr M.start y = M.mtr M.start x)) = M.mtr M.start x :=
        @Classical.epsilon_spec _ (fun y => M.mtr M.start y = M.mtr M.start x) ⟨x, rfl⟩
      rw [heps])⟩

@[simp, scoped grind =]
theorem IsRegular_iff_finite_eqv_cls_wrt_nerode {l : Language α} :
    l.IsRegular ↔ Finite (Quotient (NerodeCongruence l).eq) := by
    constructor
    · intro h
      exact IsRegular.finite_range_nerode_quotient h
    · intro h
      refine IsRegular.iff_dfa.mpr ⟨Quotient (NerodeCongruence l).eq, h,
          NerodeCongruence.toFinAcc l, nerodecongruence_to_finacc_acc l⟩

end Automata.DA
end Cslib
