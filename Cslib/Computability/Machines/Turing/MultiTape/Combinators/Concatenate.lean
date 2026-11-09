/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindInput
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Sequential
public import Mathlib.Basic.Finite.Sum
public import Cslib.Foundations.Data.Fin.Tuple

/-!
# Concatenating the outputs of two machines on the same input

`concatenate tm₁ tm₂` runs the machines on disjoint groups of work tapes, rewinding the input
between them. The second machine starts on its own fresh, blank work tapes and appends to the
first machine's output. Neither machine needs to clear its tapes or reset its heads before halting.
-/

public section

namespace Turing.MultiTapeTM

variable {k₁ k₂ : ℕ} {Symbol State₁ State₂ : Type*}

/-- Run two machines on the same input, concatenating their outputs and using disjoint
work tapes. -/
noncomputable def concatenate (tm₁ : MultiTapeTM k₁ Symbol State₁)
    (tm₂ : MultiTapeTM k₂ Symbol State₂) :
    MultiTapeTM (k₁ + k₂) Symbol ((State₁ ⊕ RewindState) ⊕ State₂) :=
  ((tm₁.extendTapes (Fin.castAddEmb k₂)).seq
    ((rewindInput Symbol).extendTapes (noTapes (k₁ + k₂)))).seq
      (tm₂.extendTapes (Fin.natAddEmb k₁))

namespace Concatenate

/-- Run the first machine on the combined tape set, modifying only on the first tapes. -/
private theorem first_phase {tm : MultiTapeTM k₁ Symbol State₁} {input : List Symbol}
    (p : tm.RunPath input) (hh : p.head = tm.initCfg input) (halt : p.last.Halted) :
    let q := p.map (embedHom tm (Fin.castAddEmb k₂) (fun _ _ => none) (fun _ => 0))
    q.head = (tm.extendTapes (Fin.castAddEmb k₂)).initCfg input ∧ q.last.Halted ∧
      q.last.inputPos.val ≤ 1 + p.length ∧ q.space ≤ p.space + k₂ := by
  refine ⟨?_, halt, ?_, (space_map_embedHom_le ..).trans (by omega)⟩
  · simp only [RelSeries.head_map, embedHom_apply, hh]
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;>
      simp only [embed, MultiTapeNTM.initCfg, Cfg.init] <;>
      cases partialInv (Fin.castAddEmb k₂) i <;> rfl
  · change (p (Fin.last p.length)).inputPos.val ≤ _
    rw [runPath_apply_eq_runFrom, hh]
    exact inputPos_runFrom_le ..

/-- Rewind the input while preserving the work tapes, their head positions, and the output. -/
private theorem rewind_phase {k : ℕ} {State : Type*} {input : List Symbol}
    (c : Cfg k Symbol State input) :
    let r := (rewindInput Symbol).extendTapes (noTapes k)
    ∃ p : r.RunPath input, p.head = c.withState (some r.q₀) ∧
      p.last = ⟨none, 1, c.workTapes, c.workTapePos, c.output⟩ ∧
      p.length = c.inputPos.val - 1 + 2 ∧ p.space ≤ k := by
  let q := MultiTapeNTM.RunPath.ofDeterministic (rewindInput Symbol)
    ⟨some (rewindInput Symbol).q₀, c.inputPos, nofun, nofun, c.output⟩ (c.inputPos.val - 1 + 2)
  refine ⟨q.map (embedHom (rewindInput Symbol) (noTapes k) c.workTapes c.workTapePos),
    ?_, ?_, rfl, ?_⟩
  · simp only [RelSeries.head_map, embedHom_apply, embed_noTapes]
    rfl
  · simp only [RelSeries.last_map, embedHom_apply]
    have hq : q.last = ⟨none, 1, nofun, nofun, c.output⟩ :=
      runFrom_rewindInput c.inputPos nofun nofun c.output
    rw [hq, embed_noTapes]
  · simpa [MultiTapeNTM.RunPath.space] using
      space_map_embedHom_le (rewindInput Symbol) (noTapes k) c.workTapes c.workTapePos q

/-- Run the second machine on the combined tape set, modifying only on the second set of tapes. -/
private theorem second_phase {tm : MultiTapeTM k₂ Symbol State₂} {input : List Symbol}
    (c₁ : Cfg k₁ Symbol State₁ input) (p : tm.RunPath input)
    (hh : p.head = tm.initCfg input) (halt : p.last.Halted) :
    let c := embed (Fin.castAddEmb k₂) c₁ (fun _ _ => none) (fun _ => 0)
    let q := (p.map (tm.prependOutputHom c₁.output)).map
      (embedHom tm (Fin.natAddEmb k₁) c.workTapes c.workTapePos)
    q.head = ⟨some tm.q₀, 1, c.workTapes, c.workTapePos, c₁.output⟩ ∧ q.last.Halted ∧
      q.last.output = c₁.output ++ p.last.output ∧ q.space ≤ p.space + k₁ := by
  refine ⟨?_, halt, rfl, (space_map_embedHom_le ..).trans (by change p.space + _ ≤ _; omega)⟩
  simp only [RelSeries.head_map, embedHom_apply, hh, MultiTapeNTM.initCfg, Cfg.init,
    MultiTapeNTM.prependOutputHom_apply, Cfg.prependOutput, List.append_nil, embed,
    Cfg.mk.injEq, and_true, true_and]
  constructor <;> funext i <;>
    grind only [→ partialInv_eq_some, Fin.castAdd_ne_natAdd,
      Fin.castAddEmb_apply, Fin.natAddEmb_apply]

end Concatenate

/-- Concatenating two computations preserves additive space bounds. Rewinding costs at most the
first computation's time plus two steps. The space estimate adds the bounds for running the
first machine, rewinding the input, and running the second machine. This counts some work-tape
cells more than once. -/
theorem ComputesInTimeAndSpace.concatenate {tm₁ : MultiTapeTM k₁ Symbol State₁}
    {tm₂ : MultiTapeTM k₂ Symbol State₂} {input out₁ out₂ : List Symbol} {t₁ t₂ s₁ s₂ : ℕ}
    (h₁ : tm₁.ComputesInTimeAndSpace input out₁ t₁ s₁)
    (h₂ : tm₂.ComputesInTimeAndSpace input out₂ t₂ s₂) :
    (tm₁.concatenate tm₂).ComputesInTimeAndSpace input (out₁ ++ out₂)
      (2 * t₁ + t₂ + 2) (s₁ + s₂ + 2 * (k₁ + k₂)) := by
  obtain ⟨p₁, hh₁, hhalt₁, ho₁, ht₁, hs₁⟩ := computesInTimeAndSpace_iff_exists_runPath.mp h₁
  obtain ⟨p₂, hh₂, hhalt₂, ho₂, ht₂, hs₂⟩ := computesInTimeAndSpace_iff_exists_runPath.mp h₂
  let pa := p₁.map (embedHom tm₁ (Fin.castAddEmb k₂) (fun _ _ => none) (fun _ => 0))
  obtain ⟨hha, hhalta, hin, hsa⟩ := Concatenate.first_phase (k₂ := k₂) p₁ hh₁ hhalt₁
  obtain ⟨pr, hhr, hrlast, htr, hsr⟩ := Concatenate.rewind_phase pa.last
  let pb := (p₂.map (tm₂.prependOutputHom p₁.last.output)).map
    (embedHom tm₂ (Fin.natAddEmb k₁) pa.last.workTapes pa.last.workTapePos)
  obtain ⟨hhb, hhaltb, hob, hsb⟩ := Concatenate.second_phase p₁.last p₂ hh₂ hhalt₂
  obtain ⟨par, hhar, hlar, htar, hsar, _⟩ := exists_runPath_seq (p₀ := pa) (p₁ := pr) hhalta hhr
  obtain ⟨p, hh, hl, ht, hsp, _⟩ := exists_runPath_seq (p₀ := par) (p₁ := pb)
    (by rw [hlar, hrlast]; rfl)
    (by simpa only [hlar, hrlast, Cfg.withState, Cfg.mapState, extendTapes_q₀, pa, pb,
      RelSeries.last_map, embedHom_apply, embed] using hhb)
  rw [MultiTapeTM.concatenate, computesInTimeAndSpace_iff_exists_runPath]
  refine ⟨p, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hh, hhar, show pa.head = _ from hha]
    rfl
  · simpa [hl, pa, pb, Cfg.Halted, Cfg.mapState] using hhaltb
  · simpa only [hl, pb, pa, RelSeries.last_map, embedHom_apply, Cfg.mapState, ho₁, ho₂] using hob
  all_goals
    simp_all only [pa, pb, RelSeries.map_length, RelSeries.last_map, embedHom_apply, embed]
    omega

/-- Compute a function whose encoded output is the concatenation of two computed outputs.
The input encoding is shared; the output types and encodings may differ. -/
theorem ComputesFunInTimeAndSpace.concatenate {tm₁ : MultiTapeTM k₁ Symbol State₁}
    {tm₂ : MultiTapeTM k₂ Symbol State₂} {α β γ δ : Type*} {f₁ : α → β} {f₂ : α → γ} {f : α → δ}
    {encIn : α ↪ List Symbol} {enc₁ : β ↪ List Symbol} {enc₂ : γ ↪ List Symbol}
    {encOut : δ ↪ List Symbol}
    {t₁ t₂ s₁ s₂ : α → ℕ}
    (h₁ : tm₁.ComputesFunInTimeAndSpace encIn enc₁ f₁ t₁ s₁)
    (h₂ : tm₂.ComputesFunInTimeAndSpace encIn enc₂ f₂ t₂ s₂)
    (henc : ∀ x, encOut (f x) = enc₁ (f₁ x) ++ enc₂ (f₂ x)) :
    (tm₁.concatenate tm₂).ComputesFunInTimeAndSpace encIn encOut f
      (fun x => 2 * t₁ x + t₂ x + 2) (fun x => s₁ x + s₂ x + 2 * (k₁ + k₂)) := by
  intro x
  simpa only [henc] using (h₁ x).concatenate (h₂ x)

/-- A function whose encoding concatenates two computed outputs is computable in linear time
and additive space overhead. The result function and encoding are specified by `henc`. -/
theorem ComputableInTimeAndSpace.concatenate {α β γ δ : Type*} {f₁ : α → β} {f₂ : α → γ} {f : α → δ}
    {encIn : α ↪ List Bool} {enc₁ : β ↪ List Bool} {enc₂ : γ ↪ List Bool}
    {encOut : δ ↪ List Bool}
    {t₁ t₂ s₁ s₂ : α → ℕ}
    (h₁ : ComputableInTimeAndSpace f₁ encIn enc₁ t₁ s₁)
    (h₂ : ComputableInTimeAndSpace f₂ encIn enc₂ t₂ s₂)
    (henc : ∀ x, encOut (f x) = enc₁ (f₁ x) ++ enc₂ (f₂ x)) :
    ComputableInTimeAndSpace f encIn encOut (fun x => 2 * t₁ x + t₂ x + 2)
      (fun x => 3 * (s₁ x + s₂ x)) := by
  obtain ⟨k₁, State₁, _, tm₁, hm₁⟩ := h₁
  obtain ⟨k₂, State₂, _, tm₂, hm₂⟩ := h₂
  refine ⟨k₁ + k₂, _, inferInstance, tm₁.concatenate tm₂,
    (hm₁.concatenate hm₂ henc).mono (fun _ => le_rfl) ?_⟩
  intro x
  have hk₁ := (hm₁ x).2.2.le
  have hk₂ := (hm₂ x).2.2.le
  omega

end Turing.MultiTapeTM
