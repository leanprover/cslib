/-
Copyright (c) 2026 Christian Reitwiessner and Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.TransformsTapes

/-!
# Sequential composition of machines on shared tapes

`seq tm₀ tm₁` behaves like `tm₀` until `tm₀` would halt, at which point it continues as `tm₁`,
started in its initial state on the tapes as `tm₀` left them. The state space is
`State₀ ⊕ State₁`, and the *halting transition* of the first phase is mapped to the initial state
of the second, so the handoff costs no extra step.

At the specification level this is `transformsTapes_seq`: transformations compose, with the time
and space bounds adding. The postcondition of `TransformsTapes` is what makes the proof direct:
the first machine halts in a full `wordsCfg`, which is exactly a starting configuration for the
second.

## Main results

* `Turing.MultiTapeTM.seq`: the composed machine.
* `Turing.MultiTapeTM.exists_runPath_seq`: run paths compose, and the configurations of the
  composed path are those of the two paths up to their states.
* `Turing.MultiTapeTM.transformsTapes_seq`: transformations compose, bounds adding.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State₀ State₁ : Type*} {input : List Symbol}

/-- The sequential composition of `tm₀` and `tm₁`: it behaves like `tm₀` until `tm₀` would halt,
at which point it switches to the initial state of `tm₁` and behaves like `tm₁`. The switch is
folded into the halting transition of `tm₀`, so it costs no step. -/
noncomputable def seq (tm₀ : MultiTapeTM k Symbol State₀) (tm₁ : MultiTapeTM k Symbol State₁) :
    MultiTapeTM k Symbol (State₀ ⊕ State₁) :=
  ofTr (.inl tm₀.q₀) fun q inp work =>
    match q with
    | .inl q₀ =>
      let a := tm₀.tr q₀ inp work
      { a with state := some (a.state.elim (.inr tm₁.q₀) .inl) }
    | .inr q₁ =>
      let a := tm₁.tr q₁ inp work
      { a with state := a.state.map .inr }

variable {tm₀ : MultiTapeTM k Symbol State₀} {tm₁ : MultiTapeTM k Symbol State₁}

namespace Sequential

/-- A configuration of the first phase: a configuration of `tm₀`, with a halted state mapped to
the initial state of the second phase. Under this map, the whole first phase of `seq` mirrors the
run of `tm₀`, *including* its halting step. -/
def leftCfg (tm₁ : MultiTapeTM k Symbol State₁) (cfg : Cfg k Symbol State₀ input) :
    Cfg k Symbol (State₀ ⊕ State₁) input :=
  cfg.mapState (fun st => some (st.elim (.inr tm₁.q₀) .inl))

/-- A configuration of the second phase. Under this map, the second phase of `seq` mirrors the
run of `tm₁`. -/
def rightCfg (cfg : Cfg k Symbol State₁ input) :
    Cfg k Symbol (State₀ ⊕ State₁) input :=
  cfg.mapState (Option.map .inr)

lemma step_leftCfg (cfg : Cfg k Symbol State₀ input) (h : cfg.state ≠ none) :
    (tm₀.seq tm₁).step (leftCfg tm₁ cfg) = leftCfg tm₁ (tm₀.step cfg) := by
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp h
  have h1 : (leftCfg tm₁ cfg).state = some (Sum.inl q : State₀ ⊕ State₁) := by
    simp [leftCfg, Cfg.mapState, hq]
  rw [step_of_state h1, step_of_state hq]
  simp only [seq, tr_ofTr]
  rfl

lemma step_rightCfg (cfg : Cfg k Symbol State₁ input) :
    (tm₀.seq tm₁).step (rightCfg cfg) = rightCfg (tm₁.step cfg) := by
  cases hq : cfg.state with
  | none =>
    have h1 : (rightCfg (State₀ := State₀) cfg).state = none := by simp [rightCfg, Cfg.mapState, hq]
    rw [step_of_halt h1, step_of_halt hq]
  | some q =>
    have h1 : (rightCfg (State₀ := State₀) cfg).state = some (Sum.inr q : State₀ ⊕ State₁) := by
      simp [rightCfg, hq]
    rw [step_of_state h1, step_of_state hq]
    simp only [seq, tr_ofTr]
    rfl

@[simp]
lemma forgetState_leftCfg (cfg : Cfg k Symbol State₀ input) :
    (leftCfg tm₁ cfg).forgetState = cfg.forgetState := rfl

@[simp]
lemma forgetState_rightCfg (cfg : Cfg k Symbol State₁ input) :
    (rightCfg (State₀ := State₀) cfg).forgetState = cfg.forgetState := rfl

/-- A halted configuration of the first phase is the start of the second phase. -/
lemma leftCfg_of_halt {cfg : Cfg k Symbol State₀ input} (h : cfg.state = none) :
    leftCfg tm₁ cfg = rightCfg (cfg.withState (some tm₁.q₀)) := by
  simp [leftCfg, rightCfg, Cfg.withState, Cfg.mapState, h]

end Sequential

open Sequential in
/-- **Sequential composition of runs.** A run path of `tm₀` to a halted configuration, followed by a
run path of `tm₁` to a halted configuration started where `tm₀` halted, gives a run path of `seq`
of at most as many steps, whose configurations are those of the two paths up to their states. -/
theorem exists_runPath_seq {p₀ : tm₀.RunPath input} (h₀ : p₀.last.Halted)
    {p₁ : tm₁.RunPath input} (h₁ : p₁.head = p₀.last.withState (some tm₁.q₀))
    (hp₁ : p₁.last.Halted) :
    ∃ p : (tm₀.seq tm₁).RunPath input, p.head = leftCfg tm₁ p₀.head ∧
      p.last = rightCfg p₁.last ∧ p.length ≤ p₀.length + p₁.length ∧
      ∀ c ∈ p, (∃ c₀ ∈ p₀, c.forgetState = c₀.forgetState) ∨
        ∃ c₁ ∈ p₁, c.forgetState = c₁.forgetState := by
  -- `seq` takes the running steps of `tm₀`, then those of `tm₁`
  obtain ⟨q₀, hh₀, hl₀, hlen₀, hmem₀⟩ := p₀.exists_running h₀
  obtain ⟨q₁, hh₁, hl₁, hlen₁, hmem₁⟩ := p₁.exists_running hp₁
  let f₀ := runningStepHom (tm' := tm₀.seq tm₁) (input := input) (leftCfg tm₁) step_leftCfg
  let f₁ := runningStepHom (tm' := tm₀.seq tm₁) (input := input) rightCfg
    fun c _ => step_rightCfg c
  refine ⟨(q₀.map f₀).smash (q₁.map f₁) (by simp [f₀, f₁, hl₀, hh₁, h₁, leftCfg_of_halt h₀]),
    by simp [f₀, hh₀], by simp [f₁, hl₁], by simp; lia, fun c hc => ?_⟩
  rcases RelSeries.mem_or_mem_of_mem_smash hc with hc | hc <;>
    obtain ⟨c', hc', rfl⟩ := RelSeries.exists_of_mem_map hc
  · exact .inl ⟨c', hmem₀ c' hc', rfl⟩
  · exact .inr ⟨c', hmem₁ c' hc', rfl⟩

open Sequential in
/-- **Sequential composition of transformations.** If the postcondition of the first
transformation implies the precondition of the second, the composed machine performs the two
transformations one after the other, with the time and space bounds adding and the emitted words
concatenating. -/
theorem transformsTapes_seq
    {P₀ P₁ : (input : List Symbol) → (Fin k → List Symbol) → Prop}
    {Q₀ Q₁ : (input : List Symbol) → (Fin k → List Symbol) → (Fin k → List Symbol) →
      List Symbol → Prop}
    {t₀ s₀ t₁ s₁ : ℕ}
    (h₀ : TransformsTapes tm₀ P₀ Q₀ t₀ s₀) (h₁ : TransformsTapes tm₁ P₁ Q₁ t₁ s₁)
    (hmid : ∀ input ws ws' e, P₀ input ws → Q₀ input ws ws' e → P₁ input ws') :
    TransformsTapes (tm₀.seq tm₁) P₀
      (fun input ws ws'' e => ∃ ws' e₀ e₁, Q₀ input ws ws' e₀ ∧ Q₁ input ws' ws'' e₁ ∧
        e = e₀ ++ e₁)
      (t₀ + t₁) (s₀ + s₁) := by
  intro input ws out hP₀
  obtain ⟨ws', e₀, hQ₀, p₀, hh₀, hl₀, ht₀, hs₀⟩ := h₀ input ws out hP₀
  obtain ⟨ws'', e₁, hQ₁, p₁, hh₁, hl₁, ht₁, hs₁⟩ :=
    h₁ input ws' (out ++ e₀) (hmid input ws ws' e₀ hP₀ hQ₀)
  obtain ⟨p, hh, hl, ht, hmem⟩ := exists_runPath_seq (p₀ := p₀) (p₁ := p₁) (by rw [hl₀]; rfl)
    (by simp [hh₁, hl₀]) (by rw [hl₁]; rfl)
  refine ⟨ws'', e₀ ++ e₁, ⟨ws', e₀, e₁, hQ₀, hQ₁, rfl⟩, p, by simp [hh, hh₀, leftCfg]; rfl,
    by simp [hl, hl₁, rightCfg], ht.trans (Nat.add_le_add ht₀ ht₁), ?_⟩
  -- every head position of the composed run is one of the first path or one of the second
  refine (p.space_le_sum_card
    (S := fun i => p₀.visitedByTapeHead i ∪ p₁.visitedByTapeHead i) fun c hc i => ?_).trans
    (((Finset.sum_le_sum fun i _ => Finset.card_union_le _ _).trans_eq
      Finset.sum_add_distrib).trans (Nat.add_le_add hs₀ hs₁))
  rcases hmem c hc with ⟨_, ⟨n, rfl⟩, he⟩ | ⟨_, ⟨n, rfl⟩, he⟩ <;>
    rw [show c.workTapePos i = _ from congrArg (·.workTapePos i) he]
  · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ n))
  · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ n))

end Turing.MultiTapeTM
