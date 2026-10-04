/-
Copyright (c) 2026 Christian Reitwiessner and Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.TransformsTapes

/-!
# Sequential composition of machines on shared tapes

The halting transition of the first machine starts the second machine, so the handoff costs no
extra step. Correctness joins the two witnessing paths at that configuration.
-/

@[expose] public section

namespace Turing.MultiTapeNTM

variable {k : ℕ} {Symbol State₀ State₁ : Type*} {input : List Symbol}

/-- Run the first machine until it halts, then start the second on the resulting tapes. -/
def seq (tm₀ : MultiTapeNTM k Symbol State₀) (tm₁ : MultiTapeNTM k Symbol State₁) :
    MultiTapeNTM k Symbol (State₀ ⊕ State₁) where
  q₀ := .inl tm₀.q₀
  Tr q inp work b := match q with
    | .inl q => ∃ a, tm₀.Tr q inp work a ∧
        b = { a with state := some (a.state.elim (.inr tm₁.q₀) .inl) }
    | .inr q => ∃ a, tm₁.Tr q inp work a ∧ b = { a with state := a.state.map .inr }

/-- Composing deterministic machines preserves determinism. -/
lemma IsDeterministic.seq {tm₀ : MultiTapeNTM k Symbol State₀} {tm₁ : MultiTapeNTM k Symbol State₁}
    (h₀ : tm₀.IsDeterministic) (h₁ : tm₁.IsDeterministic) : (tm₀.seq tm₁).IsDeterministic := by
  intro q inp work
  cases q with
  | inl q =>
    obtain ⟨a, ha, hu⟩ := h₀ q inp work
    refine ⟨_, ⟨a, ha, rfl⟩, ?_⟩
    rintro b ⟨a', ha', rfl⟩
    rw [hu a' ha']
  | inr q =>
    obtain ⟨a, ha, hu⟩ := h₁ q inp work
    refine ⟨_, ⟨a, ha, rfl⟩, ?_⟩
    rintro b ⟨a', ha', rfl⟩
    rw [hu a' ha']

variable {tm₀ : MultiTapeNTM k Symbol State₀} {tm₁ : MultiTapeNTM k Symbol State₁}

namespace Sequential

/-- Embed the first phase, sending its halted configuration to the second machine's start. -/
def leftCfg (tm₁ : MultiTapeNTM k Symbol State₁) (cfg : Cfg k Symbol State₀ input) :
    Cfg k Symbol (State₀ ⊕ State₁) input :=
  cfg.mapState (fun st ↦ some (st.elim (.inr tm₁.q₀) .inl))

/-- Embed a configuration of the second phase. -/
def rightCfg (cfg : Cfg k Symbol State₁ input) : Cfg k Symbol (State₀ ⊕ State₁) input :=
  cfg.mapState (Option.map .inr)

/-- Each running step of the first phase is a step of the composition. -/
lemma step_leftCfg {c c' : Cfg k Symbol State₀ input} (hc : ¬ c.Halted) (h : tm₀.Step c c') :
    (tm₀.seq tm₁).Step (leftCfg tm₁ c) (leftCfg tm₁ c') := by
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hc
  obtain ⟨a, ha, rfl⟩ := (step_of_state hq).mp h
  have hleft : (leftCfg tm₁ c).state = some (.inl q) := by simp [leftCfg, hq]
  exact (step_of_state hleft).mpr ⟨_, ⟨a, ha, rfl⟩, rfl⟩

/-- Each step of the second phase is a step of the composition. -/
lemma step_rightCfg {c c' : Cfg k Symbol State₁ input} (h : tm₁.Step c c') :
    (tm₀.seq tm₁).Step (rightCfg c) (rightCfg c') := by
  cases hq : c.state with
  | none =>
    obtain rfl := (step_of_halt hq).mp h
    exact (step_of_halt (c := rightCfg c') (by simp [Cfg.Halted, rightCfg, hq])).mpr rfl
  | some q =>
    obtain ⟨a, ha, rfl⟩ := (step_of_state hq).mp h
    have hright : (rightCfg (State₀ := State₀) c).state = some (.inr q) := by
      simp [rightCfg, hq]
    exact (step_of_state hright).mpr ⟨_, ⟨a, ha, rfl⟩, rfl⟩

end Sequential

open Sequential in
/-- Tape transformations compose with their time and space bounds adding. -/
theorem transformsTapes_seq
    {P₀ P₁ : (input : List Symbol) → (Fin k → List Symbol) → Prop}
    {Q₀ Q₁ : (input : List Symbol) → (Fin k → List Symbol) → (Fin k → List Symbol) → Prop}
    {t₀ s₀ t₁ s₁ : ℕ}
    (h₀ : TransformsTapes tm₀ P₀ Q₀ t₀ s₀) (h₁ : TransformsTapes tm₁ P₁ Q₁ t₁ s₁)
    (hmid : ∀ input ws ws', P₀ input ws → Q₀ input ws ws' → P₁ input ws') :
    TransformsTapes (tm₀.seq tm₁) P₀
      (fun input ws ws'' ↦ ∃ ws', Q₀ input ws ws' ∧ Q₁ input ws' ws'')
      (t₀ + t₁) (s₀ + s₁) := by
  intro input ws out hP₀
  obtain ⟨ws', p, hp, hlast, hQ₀, ht₀, hs₀⟩ := h₀ input ws out hP₀
  obtain ⟨ws'', q, hq, hlast', hQ₁, ht₁, hs₁⟩ := h₁ input ws' out (hmid input ws ws' hP₀ hQ₀)
  obtain ⟨i, hi, hactive⟩ := p.exists_first_halt (by rw [hlast]; rfl)
  let left : (tm₀.seq tm₁).RunPath input :=
    { length := i
      toFun n := leftCfg tm₁ (p.take i n)
      step n := step_leftCfg (hactive _ (by exact n.isLt)) ((p.take i).step n) }
  let right : (tm₀.seq tm₁).RunPath input := q.map ⟨rightCfg, step_rightCfg⟩
  have hjoin : left.last = right.head := by
    change leftCfg tm₁ (p.take i).last = rightCfg q.head
    rw [RelSeries.last_take, hi, hlast, hq]
    rfl
  refine ⟨ws'', left.smash right hjoin, ?_, ?_, ⟨ws', hQ₀, hQ₁⟩, ?_, ?_⟩
  · rw [RelSeries.head_smash]
    change leftCfg tm₁ (p.take i).head = _
    rw [RelSeries.head_take, hp]
    rfl
  · rw [RelSeries.last_smash]
    change rightCfg q.last = _
    rw [hlast']
    rfl
  · change i.val + q.length ≤ t₀ + t₁
    have := i.isLt
    omega
  · exact (RunPath.space_smash_le left right hjoin).trans
      (Nat.add_le_add ((RunPath.space_take_le p i).trans hs₀) hs₁)

end Turing.MultiTapeNTM
