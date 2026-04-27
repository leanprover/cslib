/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Languages.CombinatoryLogic.Defs

/-!
# SKI reduction is confluent

This file proves the **Church-Rosser** theorem for the SKI calculus, that is, if `a ↠ b` and
`a ↠ c`, `b ↠ d` and `c ↠ d` for some term `d`. More strongly (though equivalently), we show
that the relation of having a common reduct is transitive — in the above situation, `a` and `b`,
and `a` and `c` have common reducts, so the result implies the same of `b` and `c`. Note that
`MJoin Red` is symmetric (trivially) and reflexive (since `↠` is), so we in fact show that
`MJoin Red` is an equivalence.

Our proof
follows the method of Tait and Martin-Löf for the lambda calculus, as presented for instance in
Chapter 4 of Peter Selinger's notes:
<https://www.mscs.dal.ca/~selinger/papers/papers/lambdanotes.pdf>.

## Main definitions

- `ParallelReduction` : a relation `⭢ₚ` on terms such that `⭢ ⊆ ⭢ₚ ⊆ ↠`, allowing simultaneous
reduction on the head and tail of a term.

## Main results

- `parallelReduction_diamond` : parallel reduction satisfies the diamond property, that is, it is
confluent in a single step.
- `mJoin_red_equivalence` : by a general result, the diamond property for `⭢ₚ` implies the same
for its reflexive-transitive closure. This closure is exactly `↠`, which implies the
**Church-Rosser** theorem as sketched above.
-/

@[expose] public section

namespace Cslib

namespace SKI

open Red MRed Relation

/-- A reduction step allowing simultaneous reduction of disjoint redexes -/
@[reduction_sys "ₚ"]
inductive ParallelReduction : SKI → SKI → Prop
  /-- Parallel reduction is reflexive, -/
  | refl (a : SKI) : ParallelReduction a a
  /-- Contains `Red`, -/
  | red_I (a : SKI) : ParallelReduction (I ⬝ a) a
  | red_K (a b : SKI) : ParallelReduction (K ⬝ a ⬝ b) a
  | red_S (a b c : SKI) : ParallelReduction (S ⬝ a ⬝ b ⬝ c) (a ⬝ c ⬝ (b ⬝ c))
  /-- and allows simultaneous reduction of disjoint redexes. -/
  | par ⦃a a' b b' : SKI⦄ :
      ParallelReduction a a' → ParallelReduction b b' → ParallelReduction (a ⬝ b) (a' ⬝ b')

/-- The inclusion `⭢ₚ ⊆ ↠` -/
theorem mRed_of_parallelReduction {a a' : SKI} (h : a ⭢ₚ a') : a ↠ a' := by
  cases h
  case refl => exact Relation.ReflTransGen.refl
  case par a a' b b' ha hb =>
    apply parallel_mRed
    · exact mRed_of_parallelReduction ha
    · exact mRed_of_parallelReduction hb
  case red_I => exact Relation.ReflTransGen.single (red_I a')
  case red_K b => exact Relation.ReflTransGen.single (red_K a' b)
  case red_S a b c => exact Relation.ReflTransGen.single (red_S a b c)

/-- The inclusion `⭢ ⊆ ⭢ₚ` -/
theorem parallelReduction_of_red {a a' : SKI} (h : a ⭢ a') : a ⭢ₚ a' := by
  cases h
  case red_S => apply ParallelReduction.red_S
  case red_K => apply ParallelReduction.red_K
  case red_I => apply ParallelReduction.red_I
  case red_head a a' b h =>
    apply ParallelReduction.par
    · exact parallelReduction_of_red h
    · exact ParallelReduction.refl b
  case red_tail a b b' h =>
    apply ParallelReduction.par
    · exact ParallelReduction.refl a
    · exact parallelReduction_of_red h

/-- The inclusions of `mRed_of_parallelReduction` and
`parallelReduction_of_red` imply that `⭢` and `⭢ₚ` have the same reflexive-transitive
closure. -/
theorem reflTransGen_parallelReduction_mRed :
    ReflTransGen ParallelReduction = ReflTransGen Red := by
  ext a b
  constructor
  · apply Relation.reflTransGen_of_isTrans_reflexive
    exact @mRed_of_parallelReduction
  · apply Relation.reflTransGen_of_isTrans_reflexive
    exact fun a a' h => Relation.ReflTransGen.single (parallelReduction_of_red h)

/-!
Irreducibility for the (partially applied) primitive combinators.

TODO: possibly these should be proven more generally (in another file) for `↠`.
-/

lemma I_irreducible (a : SKI) (h : I ⭢ₚ a) : a = I := by
  cases h
  rfl

lemma K_irreducible (a : SKI) (h : K ⭢ₚ a) : a = K := by
  cases h
  rfl

lemma Ka_irreducible (a c : SKI) (h : (K ⬝ a) ⭢ₚ c) : ∃ a', a ⭢ₚ a' ∧ c = K ⬝ a' := by
  cases h
  case refl => use a, .refl a
  case par b a' h h' => rw [K_irreducible b h]; use a'

lemma S_irreducible (a : SKI) (h : S ⭢ₚ a) : a = S := by
  cases h
  rfl

lemma Sa_irreducible (a c : SKI) (h : (S ⬝ a) ⭢ₚ c) : ∃ a', a ⭢ₚ a' ∧ c = S ⬝ a' := by
  cases h
  case refl =>
    exact ⟨a, ParallelReduction.refl a, rfl⟩
  case par b a' h h' => rw [S_irreducible b h]; use a'

lemma Sab_irreducible (a b c : SKI) (h : (S ⬝ a ⬝ b) ⭢ₚ c) :
    ∃ a' b', a ⭢ₚ a' ∧ b ⭢ₚ b' ∧ c = S ⬝ a' ⬝ b' := by
  cases h
  case refl => use a, b, .refl a, .refl b
  case par c b' hc hb =>
    let ⟨d, hd⟩ := Sa_irreducible a c hc
    rw [hd.2]
    use d, b', hd.1

/--
The key result: the Church-Rosser property holds for `⭢ₚ`. The proof is a lengthy case analysis
on the reductions `a ⭢ₚ a₁` and `a ⭢ₚ a₂`, but is entirely mechanical.
-/
theorem parallelReduction_diamond : Diamond ParallelReduction := by
  intro a a₁ a₂ h₁ h₂
  cases h₁
  case refl => exact ⟨a₂, h₂, .refl a₂⟩
  case par a a' b b' ha' hb' =>
    cases h₂
    case refl =>
      use a' ⬝ b'
      exact ⟨.refl (a' ⬝ b'), .par ha' hb'⟩
    case par a'' b'' ha'' hb'' =>
      let ⟨a₃, ha⟩ := parallelReduction_diamond ha' ha''
      let ⟨b₃, hb⟩ := parallelReduction_diamond hb' hb''
      use a₃ ⬝ b₃
      constructor
      · exact .par ha.1 hb.1
      · exact .par ha.2 hb.2
    case red_I =>
      rw [I_irreducible a' ha']
      use b', .red_I b'
    case red_K =>
      let ⟨a₂', ha₂'⟩ := Ka_irreducible a₂ a' ha'
      rw [ha₂'.2]
      use a₂'
      exact ⟨.red_K a₂' b', ha₂'.1⟩
    case red_S a c =>
      let ⟨a'', c', h⟩ := Sab_irreducible a c a' ha'
      rw [h.2.2]
      use a'' ⬝ b' ⬝ (c' ⬝ b'), .red_S a'' c' b'
      apply ParallelReduction.par <;>
        apply ParallelReduction.par <;>
        grind
  case red_I =>
    cases h₂
    case refl => use a₁; exact ⟨.refl a₁, .red_I a₁⟩
    case par c a₁' hc ha =>
      rw [I_irreducible c hc]
      use a₁'
      exact ⟨ha, .red_I a₁'⟩
    case red_I => use a₁; exact ⟨.refl a₁, .refl a₁⟩
  case red_K c =>
    cases h₂
    case refl => use a₁; exact ⟨.refl a₁, .red_K a₁ c⟩
    case par a' c' ha hc =>
      let ⟨a₁', h'⟩ := Ka_irreducible a₁ a' ha
      rw [h'.2]
      use a₁'
      exact ⟨h'.1, .red_K a₁' c'⟩
    case red_K =>
      use a₁; exact ⟨.refl a₁, .refl a₁⟩
  case red_S a b c =>
    cases h₂
    case refl =>
      use a ⬝ c ⬝ (b ⬝ c)
      exact ⟨.refl _, .red_S ..⟩
    case par d c' hd hc =>
      let ⟨a', b', h⟩ := Sab_irreducible a b d hd
      rw [h.2.2]
      use a' ⬝ c' ⬝ (b' ⬝ c')
      constructor
      · apply ParallelReduction.par
        · exact .par h.left hc
        · exact .par h.2.1 hc
      · exact .red_S ..
    case red_S => exact ⟨a ⬝ c ⬝ (b ⬝ c), .refl _, .refl _,⟩

theorem join_parallelReduction_equivalence :
    Equivalence (MJoin ParallelReduction) :=
  Confluent.equivalence_join_reflTransGen <| Diamond.toConfluent parallelReduction_diamond

/-- The **Church-Rosser** theorem in its general form. -/
theorem mJoin_red_equivalence : Equivalence (MJoin Red) := by
  rw [MJoin, ←reflTransGen_parallelReduction_mRed]
  exact join_parallelReduction_equivalence

/-- The **Church-Rosser** theorem in the form it is usually stated. -/
theorem MRed.diamond : Confluent Red := by
  intro a b c hab hac
  apply mJoin_red_equivalence.trans (y := a)
  · exact mJoin_red_equivalence.symm (MJoin.single hab)
  · exact MJoin.single hac

end SKI

end Cslib
