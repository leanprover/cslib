/-
Copyright (c) 2026 Sparsa Roychowdhury. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sparsa Roychowdhury
-/

module

public import Cslib.Computability.Automata.MPDA.WellNested
public import Mathlib.Data.List.Induction

/-! # Well-nestedness is stack-agnostic

Well-nested sequences do not distinguish between stacks: a sequence is well-nested exactly when it
can be executed from the empty stack to the empty stack after merging all stacks into a single
stack of pairs `(i, γ)`. On that single stack, `↓ᵢ γ` pushes `(i, γ)` and `↑ᵢ γ` pops `(i, γ)`.

This gives a decision procedure for well-nestedness, `MPDA.mergedRun`.

## Main definitions

- `MPDA.Op.mergedStep`: the effect of an operation on the merged stack.
- `MPDA.mergedLTS`: the transition system on merged stacks.
- `MPDA.WellNestedPrefix`: a well-nested sequence interleaved with pushes that remain pending.
- `MPDA.mergedRun`: executable runs on the merged stack.

## Main statements

- `MPDA.mergedLTS_mTr_nil_iff`: the runs on the merged stack that start from the empty stack and end
  with stack `t` are exactly the well-nested prefixes with pending pushes `t`.
- `MPDA.wellNested_iff_mergedLTS_mTr`: a sequence is well-nested if and only if it leads from the
  empty merged stack to the empty merged stack.
- A `Decidable` instance for `MPDA.WellNested`.
-/

@[expose] public section

namespace Cslib.Automata.MPDA

variable {n : ℕ} {Γ α : Type*}

/-- `WellNestedPrefix t w` holds when `w` is a well-nested sequence interleaved with pushes that
remain pending, and `t` lists these pending pushes, the last one first. -/
inductive WellNestedPrefix : List (Fin n × Γ) → List (α × Op n Γ) → Prop where
  | base {u : List (α × Op n Γ)} : WellNested u → WellNestedPrefix [] u
  | push {t : List (Fin n × Γ)} {w u : List (α × Op n Γ)} {a : α} {i : Fin n} {γ : Γ} :
    WellNestedPrefix t w → WellNested u → WellNestedPrefix ((i, γ) :: t) (w ++ (a, .push i γ) :: u)

theorem WellNestedPrefix.append_wellNested {t : List (Fin n × Γ)} {w v : List (α × Op n Γ)}
    (h : WellNestedPrefix t w) (hv : WellNested v) : WellNestedPrefix t (w ++ v) := by
  cases h with
  | base hu => exact .base (hu.append hv)
  | push hw hu =>
    rw [List.append_assoc, List.cons_append]
    exact .push hw (hu.append hv)

theorem wellNestedPrefix_nil_iff {w : List (α × Op n Γ)} :
    WellNestedPrefix ([] : List (Fin n × Γ)) w ↔ WellNested w := by
  constructor
  · rintro ⟨hw⟩
    exact hw
  · exact .base

variable [DecidableEq Γ]

/-- The effect of an operation on the merged stack, whose entries record the stack index together
with the stack symbol. A pop is enabled only when the top entry has the same index and symbol. -/
def Op.mergedStep : List (Fin n × Γ) → Op n Γ → Option (List (Fin n × Γ))
  | s, .nop => some s
  | s, .push i γ => some ((i, γ) :: s)
  | [], .pop _ _ => none
  | (j, δ) :: s, .pop i γ => if j = i ∧ δ = γ then some s else none

/-- The transition system on the merged stack. -/
def mergedLTS : LTS (List (Fin n × Γ)) (α × Op n Γ) where
  Tr s μ t := μ.2.mergedStep s = some t

@[simp]
theorem mergedLTS_tr {s t : List (Fin n × Γ)} {μ : α × Op n Γ} :
    mergedLTS.Tr s μ t ↔ μ.2.mergedStep s = some t := Iff.rfl

/-- A well-nested sequence leaves any merged stack unchanged. -/
theorem WellNested.mergedLTS_mTr {w : List (α × Op n Γ)} (hw : WellNested w)
    (s : List (Fin n × Γ)) : mergedLTS.MTr s w s := by
  induction hw generalizing s with
  | nil => exact .refl
  | nop _ ih => exact .stepL (by simp [Op.mergedStep]) (ih s)
  | @pushPop a b i γ w w' _ _ ih ih' =>
    have hpush : (mergedLTS : LTS _ (α × Op n Γ)).Tr s (a, .push i γ) ((i, γ) :: s) := by
      simp [Op.mergedStep]
    have hpop : (mergedLTS : LTS _ (α × Op n Γ)).Tr ((i, γ) :: s) (b, .pop i γ) s := by
      simp [Op.mergedStep]
    exact .stepL hpush ((ih _).comp _ (.stepL hpop (ih' s)))

/-- The runs on the merged stack from the empty stack to `t` are exactly the well-nested prefixes
whose pending pushes are `t`. -/
theorem mergedLTS_mTr_nil_iff {w : List (α × Op n Γ)} {t : List (Fin n × Γ)} :
    mergedLTS.MTr [] w t ↔ WellNestedPrefix t w := by
  constructor
  · induction w using List.reverseRecOn generalizing t with
    | nil =>
      intro h
      rw [← LTS.MTr.nil_eq _ h]
      exact .base .nil
    | append_singleton w μ ih =>
      intro h
      obtain ⟨s, hw, hμ⟩ := (LTS.MTr.append_iff _).mp h
      rw [LTS.MTr.singleton_iff, mergedLTS_tr] at hμ
      have hs := ih hw
      obtain ⟨a, op⟩ := μ
      cases op with
      | nop =>
        simp only [Op.mergedStep, Option.some.injEq] at hμ
        subst hμ
        exact hs.append_wellNested (.nop .nil)
      | push i γ =>
        simp only [Op.mergedStep, Option.some.injEq] at hμ
        subst hμ
        exact .push hs .nil
      | pop i γ =>
        cases hs with
        | base _ => simp [Op.mergedStep] at hμ
        | @push t' w₀ u a' j δ hw₀ hu =>
          simp only [Op.mergedStep] at hμ
          split_ifs at hμ with hjδ
          obtain ⟨rfl, rfl⟩ := hjδ
          simp only [Option.some.injEq] at hμ
          subst hμ
          rw [List.append_assoc, List.cons_append]
          exact hw₀.append_wellNested (.pushPop hu .nil)
  · intro h
    induction h with
    | base hu => exact hu.mergedLTS_mTr []
    | @push t w u a i γ _ hu ih =>
      refine ih.comp _ (.stepL ?_ (hu.mergedLTS_mTr _))
      simp [Op.mergedStep]

/-- Well-nestedness is stack-agnostic: a sequence is well-nested exactly when it leads from the
empty merged stack to the empty merged stack. -/
theorem wellNested_iff_mergedLTS_mTr {w : List (α × Op n Γ)} :
    WellNested w ↔ mergedLTS.MTr ([] : List (Fin n × Γ)) w [] := by
  rw [mergedLTS_mTr_nil_iff, wellNestedPrefix_nil_iff]

/-- Executable runs on the merged stack. -/
def mergedRun : List (Fin n × Γ) → List (α × Op n Γ) → Option (List (Fin n × Γ))
  | s, [] => some s
  | s, μ :: w => (μ.2.mergedStep s).bind fun t => mergedRun t w

theorem mergedRun_eq_some_iff {w : List (α × Op n Γ)} {s t : List (Fin n × Γ)} :
    mergedRun s w = some t ↔ mergedLTS.MTr s w t := by
  induction w generalizing s with
  | nil => simp [mergedRun, eq_comm]
  | cons μ w ih =>
    simp only [mergedRun, Option.bind_eq_some_iff, ih, LTS.MTr.cons_iff, mergedLTS_tr]

theorem wellNested_iff_mergedRun {w : List (α × Op n Γ)} :
    WellNested w ↔ mergedRun ([] : List (Fin n × Γ)) w = some [] := by
  rw [mergedRun_eq_some_iff, wellNested_iff_mergedLTS_mTr]

instance (w : List (α × Op n Γ)) : Decidable (WellNested w) :=
  decidable_of_iff _ wellNested_iff_mergedRun.symm

end Cslib.Automata.MPDA
