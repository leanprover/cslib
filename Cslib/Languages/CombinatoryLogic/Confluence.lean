/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Languages.CombinatoryLogic.Basic
public import Cslib.Foundations.Relation.Confluence

/-!
# SKI reduction is confluent

This file proves the **Church-Rosser** theorem for the SKI calculus, that is, if `a ↠ b` and
`a ↠ c`, `b ↠ d` and `c ↠ d` for some term `d`. More strongly (though equivalently), we show
that the relation of having a common reduct is transitive — in the above situation, `a` and `b`,
and `a` and `c` have common reducts, so the result implies the same of `b` and `c`. Note that
`Join (ReflTransGen Red)` is symmetric (trivially) and reflexive (since `↠` is), so we in fact show
that `Join (ReflTransGen Red)` is an equivalence.

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
- `join_mRed_equivalence` : by a general result, the diamond property for `⭢ₚ` implies the same
for its reflexive-transitive closure. This closure is exactly `↠`, which implies the
**Church-Rosser** theorem as sketched above.
- `I_mRed_eq`, `K_mRed_eq`, `Ka_mRed_iff`, `S_mRed_eq`, `Sa_mRed_iff`, `Sab_mRed_iff` :
multi-step head-normal decomposition and irreducibility of (partially applied) primitive
combinators.
- `not_join_S_K`, `not_join_TT_FF`, `isBool_unique` : consistency and non-degeneracy of SKI
reduction and Church booleans.
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

/-- The inclusion `(· ⭢ₚ ·) ≤ (· ↠ ·)`. -/
theorem ParallelReduction.le_reflTransGen_red :
    (· ⭢ₚ ·) ≤ (· ↠ ·) := by
  intro a a' h
  cases h
  case refl => exact Relation.ReflTransGen.refl
  case par a a' b b' ha hb =>
    apply parallel_mRed
    · exact ha.le_reflTransGen_red
    · exact hb.le_reflTransGen_red
  case red_I => exact Relation.ReflTransGen.single (Red.red_I a')
  case red_K b => exact Relation.ReflTransGen.single (Red.red_K a' b)
  case red_S a b c => exact Relation.ReflTransGen.single (Red.red_S a b c)

/-- The inclusion `(· ⭢ ·) ≤ (· ⭢ₚ ·)`. -/
theorem Red.le_parallelReduction :
    (· ⭢ ·) ≤ (· ⭢ₚ ·) := by
  intro a a' h
  cases h
  case red_S => apply ParallelReduction.red_S
  case red_K => apply ParallelReduction.red_K
  case red_I => apply ParallelReduction.red_I
  case red_head a a' b h =>
    apply ParallelReduction.par
    · exact h.le_parallelReduction
    · exact ParallelReduction.refl b
  case red_tail a b b' h =>
    apply ParallelReduction.par
    · exact ParallelReduction.refl a
    · exact h.le_parallelReduction

/-- The relations `⭢` and `⭢ₚ` have the same reflexive-transitive closure. -/
theorem reflTransGen_parallelReduction_mRed :
    ReflTransGen ParallelReduction = ReflTransGen Red := by
  apply le_antisymm
  · exact reflTransGen_le_of_le ParallelReduction.le_reflTransGen_red
  · exact ReflTransGen.mono Red.le_parallelReduction

/-!
### Irreducibility for the (partially applied) primitive combinators
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

/-- Multi-step irreducibility of `I`. -/
theorem I_mRed_eq (a : SKI) (h : I ↠ a) : a = I := by
  rw [← reflTransGen_parallelReduction_mRed] at h
  induction h with
  | refl => rfl
  | tail _ hbc ih =>
    rw [ih] at hbc
    exact I_irreducible _ hbc

/-- `I` reduces in zero or more steps to `a` if and only if `a = I`. -/
@[simp]
theorem I_mRed_iff (a : SKI) : (I ↠ a) ↔ a = I :=
  ⟨I_mRed_eq a, fun h => h ▸ .refl⟩

/-- Multi-step irreducibility of `K`. -/
theorem K_mRed_eq (a : SKI) (h : K ↠ a) : a = K := by
  rw [← reflTransGen_parallelReduction_mRed] at h
  induction h with
  | refl => rfl
  | tail _ hbc ih =>
    rw [ih] at hbc
    exact K_irreducible _ hbc

/-- `K` reduces in zero or more steps to `a` if and only if `a = K`. -/
@[simp]
theorem K_mRed_iff (a : SKI) : (K ↠ a) ↔ a = K :=
  ⟨K_mRed_eq a, fun h => h ▸ .refl⟩

/-- Multi-step head-normal decomposition of `K ⬝ a`. -/
theorem Ka_mRed_iff (a c : SKI) : (K ⬝ a) ↠ c ↔ ∃ a', a ↠ a' ∧ c = K ⬝ a' := by
  constructor
  · intro h
    rw [← reflTransGen_parallelReduction_mRed] at h
    induction h with
    | refl => exact ⟨a, .refl, rfl⟩
    | tail _ hbc ih =>
      obtain ⟨a₁, ha₁, rfl⟩ := ih
      obtain ⟨a₂, ha₂, rfl⟩ := Ka_irreducible a₁ _ hbc
      exact ⟨a₂, ha₁.trans ha₂.le_reflTransGen_red, rfl⟩
  · rintro ⟨a', ha', rfl⟩
    exact MRed.tail K ha'

/-- Multi-step irreducibility of `S`. -/
theorem S_mRed_eq (a : SKI) (h : S ↠ a) : a = S := by
  rw [← reflTransGen_parallelReduction_mRed] at h
  induction h with
  | refl => rfl
  | tail _ hbc ih =>
    rw [ih] at hbc
    exact S_irreducible _ hbc

/-- `S` reduces in zero or more steps to `a` if and only if `a = S`. -/
@[simp]
theorem S_mRed_iff (a : SKI) : (S ↠ a) ↔ a = S :=
  ⟨S_mRed_eq a, fun h => h ▸ .refl⟩

/-- Multi-step head-normal decomposition of `S ⬝ a`. -/
theorem Sa_mRed_iff (a c : SKI) : (S ⬝ a) ↠ c ↔ ∃ a', a ↠ a' ∧ c = S ⬝ a' := by
  constructor
  · intro h
    rw [← reflTransGen_parallelReduction_mRed] at h
    induction h with
    | refl => exact ⟨a, .refl, rfl⟩
    | tail _ hbc ih =>
      obtain ⟨a₁, ha₁, rfl⟩ := ih
      obtain ⟨a₂, ha₂, rfl⟩ := Sa_irreducible a₁ _ hbc
      exact ⟨a₂, ha₁.trans ha₂.le_reflTransGen_red, rfl⟩
  · rintro ⟨a', ha', rfl⟩
    exact MRed.tail S ha'

/-- Multi-step head-normal decomposition of `S ⬝ a ⬝ b`. -/
theorem Sab_mRed_iff (a b c : SKI) :
    (S ⬝ a ⬝ b) ↠ c ↔ ∃ a' b', a ↠ a' ∧ b ↠ b' ∧ c = S ⬝ a' ⬝ b' := by
  constructor
  · intro h
    rw [← reflTransGen_parallelReduction_mRed] at h
    induction h with
    | refl => exact ⟨a, b, .refl, .refl, rfl⟩
    | tail _ hbc ih =>
      obtain ⟨a₁, b₁, ha₁, hb₁, rfl⟩ := ih
      obtain ⟨a₂, b₂, ha₂, hb₂, rfl⟩ := Sab_irreducible a₁ b₁ _ hbc
      exact ⟨a₂, b₂, ha₁.trans ha₂.le_reflTransGen_red, hb₁.trans hb₂.le_reflTransGen_red, rfl⟩
  · rintro ⟨a', b', ha', hb', rfl⟩
    exact parallel_mRed (MRed.tail S ha') hb'

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
    Equivalence (Join (ReflTransGen ParallelReduction)) :=
  Confluent.equivalence_join_reflTransGen <| Diamond.to_confluent parallelReduction_diamond

/-- The **Church-Rosser** theorem in its general form. -/
theorem join_mRed_equivalence : Equivalence (Join (ReflTransGen Red)) := by
  rw [←reflTransGen_parallelReduction_mRed]
  exact join_parallelReduction_equivalence

/-- The **Church-Rosser** theorem in the form it is usually stated. -/
theorem MRed.diamond : Confluent Red := by
  intro a b c hab hac
  apply join_mRed_equivalence.trans (y := a)
  · exact join_mRed_equivalence.symm (Join.single hab)
  · exact Join.single hac

/-! ### Consistency and non-degeneracy -/

/-- `S` and `K` have no common reduct. -/
theorem not_join_S_K : ¬ Join (ReflTransGen Red) S K := by
  rintro ⟨c, hSc, hKc⟩
  have h := (S_mRed_eq c hSc).symm.trans (K_mRed_eq c hKc)
  cases h

/-- Multi-step irreducibility of `TT`. -/
theorem TT_mRed_eq (a : SKI) (h : TT ↠ a) : a = TT := by
  rw [TT] at h ⊢
  exact K_mRed_eq a h

/-- `TT` reduces in zero or more steps to `a` if and only if `a = TT`. -/
theorem TT_mRed_iff (a : SKI) : (TT ↠ a) ↔ a = TT :=
  ⟨TT_mRed_eq a, fun h => h ▸ .refl⟩

/-- Multi-step irreducibility of `FF`. -/
theorem FF_mRed_eq (a : SKI) (h : FF ↠ a) : a = FF := by
  rw [FF] at h ⊢
  obtain ⟨a', ha', rfl⟩ := (Ka_mRed_iff I a).mp h
  rw [I_mRed_eq a' ha']

/-- `FF` reduces in zero or more steps to `a` if and only if `a = FF`. -/
theorem FF_mRed_iff (a : SKI) : (FF ↠ a) ↔ a = FF :=
  ⟨FF_mRed_eq a, fun h => h ▸ .refl⟩

/-- `TT` and `FF` have no common reduct. -/
theorem not_join_TT_FF : ¬ Join (ReflTransGen Red) TT FF := by
  rintro ⟨c, hTc, hFc⟩
  have h := (TT_mRed_eq c hTc).symm.trans (FF_mRed_eq c hFc)
  rw [TT, FF] at h
  cases h

/-- `TT` does not multi-step reduce to `FF`. -/
theorem not_TT_mRed_FF : ¬ (TT ↠ FF) :=
  fun h => not_join_TT_FF (Join.single h)

/-- `FF` does not multi-step reduce to `TT`. -/
theorem not_FF_mRed_TT : ¬ (FF ↠ TT) :=
  fun h => not_join_TT_FF ⟨TT, .refl, h⟩

/-- No SKI term simultaneously represents `true` and `false`. -/
theorem isBool_unique {a : SKI} {b₁ b₂ : Bool} (h₁ : IsBool b₁ a) (h₂ : IsBool b₂ a) :
    b₁ = b₂ := by
  have hj := MRed.diamond (h₁ S K) (h₂ S K)
  cases b₁ <;> cases b₂
  · rfl
  · exact False.elim (not_join_S_K (join_mRed_equivalence.symm hj))
  · exact False.elim (not_join_S_K hj)
  · rfl

end SKI

end Cslib
