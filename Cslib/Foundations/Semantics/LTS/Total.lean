/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Foundations.Semantics.FLTS.Basic
public import Cslib.Foundations.Semantics.LTS.OmegaExecution

/-!
# Total LTS

This file defines, and proves some theorems about, the notion of an LTS being "total"
and a "totalize" construction that converts any LTS into a total LTS.
-/

@[expose] public section

namespace Cslib.LTS

open ωSequence Sum

variable {State Label : Type*} {lts : LTS State Label}

/-- An LTS is total iff every state has a `μ`-derivative for every label `μ`. -/
class Total (lts : LTS State Label) where
  /-- The condition of being total. -/
  total s μ : ∃ s', lts.Tr s μ s'

/-- Choose an FLTS that is a "sub-LTS" of a total LTS. -/
noncomputable def chooseFLTS (lts : LTS State Label) [h : lts.Total] : FLTS State Label where
  tr s μ := Classical.choose <| h.total s μ

/-- The FLTS chosen by `chooseFLTS` always provides legal transitions. -/
theorem Total.chooseFLTS (lts : LTS State Label) [h : lts.Total] (s : State) (μ : Label) :
    lts.Tr s μ (lts.chooseFLTS.tr s μ) :=
  Classical.choose_spec <| h.total s μ

/-- `chooseOmegaExecution` builds an infinite execution of a total LTS from any starting state
and over any infinite sequence of labels. -/
noncomputable def chooseOmegaExecution (lts : LTS State Label) [lts.Total]
    (s : State) (μs : ωSequence Label) : ℕ → State
  | 0 => s
  | n + 1 => lts.chooseFLTS.tr (lts.chooseOmegaExecution s μs n) (μs n)

/-- If a LTS is total, then there exists an infinite execution from any starting state and
over any infinite sequence of labels. -/
theorem Total.omegaExecution_exists [h : lts.Total] (s : State) (μs : ωSequence Label) :
    ∃ ss, lts.OmegaExecution ss μs ∧ ss 0 = s := by
  use lts.chooseOmegaExecution s μs
  grind [chooseOmegaExecution, Total.chooseFLTS]

/-- If a LTS is total, then any finite execution can be extended to an infinite execution,
provided that the label type is inbabited. -/
theorem Total.extend_omegaExecution [Inhabited Label] [ht : lts.Total]
    {μl : List Label} {s t : State} (hm : lts.MTr s μl t) :
    ∃ μs ss, lts.OmegaExecution ss (μl ++ω μs) ∧ ss 0 = s ∧ ss μl.length = t := by
  let μs : ωSequence Label := .const default
  obtain ⟨ss', ho, h0⟩ := Total.omegaExecution_exists (h := ht) t μs
  grind [OmegaExecution.append hm ho h0]

/-- `totalize` constructs a total LTS from any given LTS by adding a sink state. -/
def totalize (lts : LTS State Label) : LTS (State ⊕ Unit) Label where
  Tr s' μ t' := match s', t' with
    | Sum.inl s, Sum.inl t => lts.Tr s μ t
    | _, Sum.inr () => True
    | Sum.inr (), Sum.inl _ => False

/-- The LTS constructed by `totalize` is indeed total. -/
instance (lts : LTS State Label) : lts.totalize.Total where
  total _ _ := by simp [totalize]

/-- In `totalize`, there is no finite execution from the sink state to any non-sink state. -/
theorem totalize.no_sink_to_nonsink {μs : List Label} {t : State} :
    ¬ lts.totalize.MTr (Sum.inr ()) μs (Sum.inl t) := by
  intro h
  generalize h_s : (Sum.inr () : State ⊕ Unit) = s'
  generalize h_t : (Sum.inl t : State ⊕ Unit) = t'
  rw [h_s, h_t] at h
  induction h <;> grind [totalize]

/-- In `totalize`, the transitions between non-sink states correspond exactly to
the transitions in the original LTS. -/
@[simp]
theorem totalize.nonsink_tr_iff {μ : Label} {s t : State} :
    lts.totalize.Tr (Sum.inl s) μ (Sum.inl t) ↔ lts.Tr s μ t := by
  simp [totalize]

/-- In `totalize`, the multistep transitions between non-sink states correspond exactly to
the multistep transitions in the original LTS. -/
@[simp]
theorem totalize.nonsink_mtr_iff {μs : List Label} {s t : State} :
    lts.totalize.MTr (Sum.inl s) μs (Sum.inl t) ↔ lts.MTr s μs t := by
  constructor <;> intro h
  · generalize h_s : (Sum.inl s : State ⊕ Unit) = s'
    generalize h_t : (Sum.inl t : State ⊕ Unit) = t'
    rw [h_s, h_t] at h
    induction h generalizing s
    case refl _ => grind [MTr]
    case stepL t1' μ t2' μs t3' h_tr h_mtr h_ind =>
      obtain ⟨rfl⟩ := h_s
      cases t2'
      case inl t2 => grind [MTr, totalize.nonsink_tr_iff.mp h_tr]
      case inr t2 => grind [totalize.no_sink_to_nonsink]
  · induction h
    case refl _ => grind [MTr]
    case stepL t1 μ t2 μs t3 h_tr h_mtr h_ind =>
      grind [MTr, totalize.nonsink_tr_iff.mpr h_tr]

end Cslib.LTS
