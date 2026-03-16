/-
Copyright (c) 2026 Fabrizio Montesi, Lorenzo Pace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Pace
-/

module

public import Cslib.Foundations.Semantics.LTS.Bisimulation
public import Cslib.Foundations.Data.OmegaSequence.Defs

@[expose] public section

/-! # Linear Temporal Logic

Linear Temporal Logic (LTL) is a logic for reasoning about the validity of propositional atoms
in linear time.

## Main definitions

- `Proposition`: the language of propositions, parametrized on the type of atoms.
- `Satisfies ls φ`: the ω-sequence `ls` satisfies proposition `p`.
- `Proposition.equiv`: equivalence of two propositions modulo `Satisfies`.

## Main statements

- `next_self_dual`: Negation can be brought inside the `next` operator.
- `distrib_eventually_or`: the `eventually` operator distributes on disjunction.
- `expansion_until`: expansion rule for the `until` operator
- `expansion_eventually`: expansion rule for the `eventually` operator

## References
Course slides, University of Pisa: https://pages.di.unipi.it/gadducci/SVV-24/slideB/svv_b_01.pdf
-/

namespace Cslib.Logic.LTL

/-- Propositions, where `T` is the type of atoms. -/
inductive Proposition (T : Type u) : Type u where
  | true
  | false
  | not (φ₁ : Proposition T)
  | and (φ₁ φ₂ : Proposition T)
  | or (φ₁ φ₂ : Proposition T)
  | implies (φ₁ φ₂ : Proposition T)
  | iff (φ₁ φ₂ : Proposition T)
  | next (φ : Proposition T)
  | eventually (φ : Proposition T)
  | always (φ : Proposition T)
  | until_op (φ : Proposition T) (φ : Proposition T)
  | atom (p : T)

/-- Satisfaction relation for ω-sequences of atom valuations. -/
@[simp, scoped grind =]
def Satisfies (ls : ωSequence (Set T)) : Proposition T → Prop
  | .true => True
  | .false => False
  | .and φ₁ φ₂ => Satisfies ls φ₁ ∧ Satisfies ls φ₂
  | .or φ₁ φ₂ => Satisfies ls φ₁ ∨ Satisfies ls φ₂
  | .implies φ₁ φ₂ => Satisfies ls φ₁ → Satisfies ls φ₂
  | .iff φ₁ φ₂ => Satisfies ls φ₁ ↔ Satisfies ls φ₂
  | .atom (p) => p ∈ ls 0
  | .not φ => ¬ (Satisfies ls φ)
  | .next φ => Satisfies (ls.drop 1) φ
  | .eventually φ => ∃ k : ℕ, Satisfies (ωSequence.drop k ls) φ
  | .always φ => ∀ k : ℕ , Satisfies (ωSequence.drop k ls) φ
  | .until_op φ₁ φ₂ => ∃ k : ℕ,
      Satisfies (ωSequence.drop k ls) φ₂ ∧
      ∀ i : ℕ, i < k →
        Satisfies (ωSequence.drop i ls) φ₁

notation:50 ls " ⊧ " φ => Satisfies ls φ

/-- Validity of LTL propositions on ω-sequences. -/
@[simp, scoped grind =]
def Proposition.Valid (φ₁ : Proposition T) : Prop :=
  ∀ (ls : ωSequence (Set T)) , ls ⊧ φ₁


notation:50 φ₁ " ≈ " φ₂ => Proposition.Valid (Proposition.iff φ₁ φ₂)

/-- Negation can be brought inside the `next` operator. -/
@[scoped grind .]
theorem next_self_dual {T} : ∀ (φ : Proposition T), φ.next.not ≈ φ.not.next := by
  simp

/-- The `eventually` operator distributes on disjunction. -/
@[scoped grind .]
theorem distrib_eventually_or {T} : ∀ (φ : Proposition T) (ψ : Proposition T) ,
Proposition.eventually (φ.or ψ) ≈ (Proposition.or (φ.eventually) (ψ.eventually)) := by
  simp
  grind

/-- Expansion rule for the `until` operator. -/
@[scoped grind .]
theorem expansion_until {T} : ∀ (φ : Proposition T) (ψ : Proposition T) ,
φ.until_op ψ ≈ ψ.or (φ.and ((φ.until_op ψ).next)) := by
intros
unfold Proposition.Valid
intro
apply Iff.intro
· intro h
  unfold Satisfies
  simp only [Satisfies, ωSequence.drop_drop]
  rcases h with ⟨x, hx⟩
  cases x
  · simp only [ωSequence.drop_zero, not_lt_zero, IsEmpty.forall_iff, implies_true, and_true] at hx
    left
    exact hx
  · right
    constructor
    · have hxr := hx.right
      specialize hxr 0
      simp only [lt_add_iff_pos_left, Order.lt_add_one_iff,
      zero_le, ωSequence.drop_zero, forall_const] at hxr
      exact hxr
    · grind
· intro h
  rcases h with hL | hR
  · exists 0
    simp only [ωSequence.drop_zero, not_lt_zero, IsEmpty.forall_iff, implies_true, and_true]
    exact hL
  have hRr := hR.right
  rcases hRr with ⟨x, hx⟩
  exists (1 + x)
  constructor
  · have hxl := hx.left
    simp only [ωSequence.drop_drop] at hxl
    exact hxl
  · intro i hi
    rcases i with rfl | j
    · have hRl := hR.left
      exact hRl
    · have hxr := hx.right
      specialize hxr j
      have hi' : Nat.succ j < Nat.succ x := by
        simpa [Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hi
      have hj : j < x := Nat.lt_of_succ_lt_succ hi'
      rw [Nat.add_comm j 1]
      simp only [ωSequence.drop_drop] at hxr
      exact (hxr hj)


/-- Expansion rule for the `eventually` operator. -/
@[scoped grind .]
theorem expansion_eventually {T} : ∀ (ψ : Proposition T) ,
Proposition.eventually ψ ≈ ψ.or (ψ.eventually.next) := by
simp only [Proposition.Valid, Satisfies, ωSequence.drop_drop]
intros
apply Iff.intro
· intro h
  rcases h with ⟨x, hx⟩
  cases x
  · simp only [ωSequence.drop_zero] at hx
    left
    exact hx
  · right
    rename_i j
    rw [← Nat.add_comm] at hx
    exists j
· intro h
  rcases h with hL | hR
  · exists 0
  · rcases hR with ⟨x, hx⟩
    exists 1 + x


end Cslib.Logic.LTL
