/-
Copyright (c) 2026 Christian Reitwiessner and Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger, Aviv Bar Natan
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.TransformsTapes

/-!
# Sequential composition of machines on shared tapes

`MultiTapeNTM.seq tm₀ tm₁` follows a path of `tm₀` until its first halting step, then continues
with a path of `tm₁` on the resulting tapes. The handoff is folded into the first phase's halting
transition and costs no extra step. `MultiTapeNTM.transformsTapes_seq` proves that word
transformations compose, with time and space bounds adding.

`MultiTapeTM.seq` equips this same relation with its determinism proof. Its specification is the
shared theorem, with no separate deterministic correctness result.
-/

@[expose] public section

namespace Turing

variable {k : ℕ} {Symbol State₀ State₁ : Type*} {input : List Symbol}

namespace MultiTapeNTM

/-- Compose two machines, handing off during the first machine's halting transition. -/
@[simps q₀]
def seq (tm₀ : MultiTapeNTM k Symbol State₀) (tm₁ : MultiTapeNTM k Symbol State₁) :
    MultiTapeNTM k Symbol (State₀ ⊕ State₁) where
  q₀ := .inl tm₀.q₀
  Tr q inp work action := match q with
    | .inl q₀ => ∃ a, tm₀.Tr q₀ inp work a ∧
        action = { a with state := some (a.state.elim (.inr tm₁.q₀) .inl) }
    | .inr q₁ => ∃ a, tm₁.Tr q₁ inp work a ∧
        action = { a with state := a.state.map .inr }

variable {tm₀ : MultiTapeNTM k Symbol State₀} {tm₁ : MultiTapeNTM k Symbol State₁}

namespace Sequential

/-- Embed the first phase, mapping its halted state to the second machine's initial state. -/
def leftCfg (tm₁ : MultiTapeNTM k Symbol State₁) (cfg : Cfg k Symbol State₀ input) :
    Cfg k Symbol (State₀ ⊕ State₁) input :=
  cfg.mapState (fun st => some (st.elim (.inr tm₁.q₀) .inl))

/-- Embed a configuration of the second phase. -/
def rightCfg (cfg : Cfg k Symbol State₁ input) : Cfg k Symbol (State₀ ⊕ State₁) input :=
  cfg.mapState (Option.map .inr)

/-- The composed machine can follow every active step of the first phase. -/
lemma step_leftCfg {c c' : Cfg k Symbol State₀ input} (h : tm₀.Step c c')
    (hactive : ¬c.Halted) : (tm₀.seq tm₁).Step (leftCfg tm₁ c) (leftCfg tm₁ c') := by
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hactive
  obtain ⟨a, ha, rfl⟩ := (show ∃ a, tm₀.Tr q c.inputSymbol c.workTapeSymbols a ∧
    c' = a.apply c from by simpa [Step, hq] using h)
  simp only [Step, leftCfg, Cfg.mapState_state, hq, Option.elim_some]
  refine ⟨{ a with state := some (a.state.elim (.inr tm₁.q₀) .inl) }, ?_, rfl⟩
  exact ⟨a, ha, rfl⟩

/-- The composed machine can follow every step of the second phase. -/
lemma step_rightCfg {c c' : Cfg k Symbol State₁ input} (h : tm₁.Step c c') :
    (tm₀.seq tm₁).Step (rightCfg c) (rightCfg c') := by
  cases hq : c.state with
  | none =>
    obtain rfl := (step_of_halt hq).mp h
    exact (step_of_halt (by simp [Cfg.Halted, rightCfg, hq])).mpr rfl
  | some q =>
    obtain ⟨a, ha, rfl⟩ := (show ∃ a, tm₁.Tr q c.inputSymbol c.workTapeSymbols a ∧
      c' = a.apply c from by simpa [Step, hq] using h)
    simp only [Step, rightCfg, Cfg.mapState_state, hq, Option.map_some]
    refine ⟨{ a with state := a.state.map .inr }, ?_, rfl⟩
    exact ⟨a, ha, rfl⟩

@[simp]
lemma workTapePos_leftCfg (cfg : Cfg k Symbol State₀ input) :
    (leftCfg tm₁ cfg).workTapePos = cfg.workTapePos := rfl

@[simp]
lemma workTapePos_rightCfg (cfg : Cfg k Symbol State₁ input) :
    (rightCfg (State₀ := State₀) cfg).workTapePos = cfg.workTapePos := rfl

end Sequential

open Sequential in
/-- Sequential composition of word transformations, with additive time and space bounds. -/
theorem transformsTapes_seq
    {P₀ P₁ : (input : List Symbol) → (Fin k → List Symbol) → Prop}
    {Q₀ Q₁ : (input : List Symbol) → (Fin k → List Symbol) → (Fin k → List Symbol) → Prop}
    {t₀ s₀ t₁ s₁ : ℕ}
    (h₀ : tm₀.TransformsTapes P₀ Q₀ t₀ s₀) (h₁ : tm₁.TransformsTapes P₁ Q₁ t₁ s₁)
    (hmid : ∀ input ws ws', P₀ input ws → Q₀ input ws ws' → P₁ input ws') :
    (tm₀.seq tm₁).TransformsTapes P₀
      (fun input ws ws'' => ∃ ws', Q₀ input ws ws' ∧ Q₁ input ws' ws'')
      (t₀ + t₁) (s₀ + s₁) := by
  intro input ws out hP₀
  obtain ⟨ws', p₀, ht₀, hlast₀, hQ₀, hs₀⟩ := h₀ input ws out hP₀
  obtain ⟨ws'', p₁, ht₁, hlast₁, hQ₁, hs₁⟩ := h₁ input ws' out (hmid input ws ws' hP₀ hQ₀)
  -- Trim the first path at its first halt so every mapped step belongs to the first phase.
  obtain ⟨u, hu, huhalt, huactive⟩ := p₀.exists_minimal_halting_time (by simp [Cfg.Halted, hlast₀])
  have hu_last : p₀.cfgs[u] = wordsCfg input none ws' out := by
    have h := p₀.getElem_eq_of_halt (n := p₀.time) (by unfold RunPath.time; omega)
      (by rw [p₀.length_eq_time_add_one]; omega) huhalt
    simpa [hlast₀] using h.symm
  let left := (p₀.take u hu).map (leftCfg tm₁) fun n hn =>
    step_leftCfg ((p₀.take u hu).step_getElem n hn) (by
      simp only [RunPath.take_cfgs, List.length_take] at hn
      simpa using huactive n (by omega))
  let right := p₁.map (rightCfg (State₀ := State₀)) fun n hn =>
    step_rightCfg (tm₀ := tm₀) (p₁.step_getElem n hn)
  have hhandoff : left.last = rightCfg (wordsCfg input (some tm₁.q₀) ws' out) := by
    simp [left, hu_last, leftCfg, rightCfg]
  let combined := left.append right hhandoff
  have hlast : combined.last = wordsCfg input none ws'' out := by
    change rightCfg p₁.last = _
    rw [hlast₁]
    rfl
  have htime : combined.time = u + t₁ := by simp [combined, left, right, ht₁]
  have hle : combined.time ≤ t₀ + t₁ := by
    have := p₀.length_eq_time_add_one
    omega
  have hspace : combined.space ≤ s₀ + s₁ := by
    refine (left.space_append_le right hhandoff).trans (Nat.add_le_add ?_ ?_)
    · calc left.space = (p₀.take u hu).space := (p₀.take u hu).space_map _ _ fun _ => rfl
           _ ≤ s₀ := ((p₀.take u hu).space_mono p₀ (List.take_subset _ _)).trans hs₀
    · calc right.space = p₁.space := p₁.space_map _ _ fun _ => rfl
           _ ≤ s₁ := hs₁
  have hhalt : combined.last.Halted := by simp [Cfg.Halted, hlast]
  have htime' : (combined.pad (t₀ + t₁ - combined.time) hhalt).time = t₀ + t₁ := by
    rw [RunPath.time_pad]
    omega
  exact ⟨ws'', combined.pad (t₀ + t₁ - combined.time) hhalt, htime',
    hlast, ⟨ws', hQ₀, hQ₁⟩, (combined.space_pad _ hhalt).le.trans hspace⟩

end MultiTapeNTM

/-- Sequential composition of deterministic machines uses the same underlying relation. -/
def MultiTapeTM.seq (tm₀ : MultiTapeTM k Symbol State₀) (tm₁ : MultiTapeTM k Symbol State₁) :
    MultiTapeTM k Symbol (State₀ ⊕ State₁) where
  toMultiTapeNTM := tm₀.toMultiTapeNTM.seq tm₁.toMultiTapeNTM
  deterministic q inp work := by
    cases q <;> simp [MultiTapeNTM.seq, MultiTapeTM.tr_iff]

end Turing
