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
* `Turing.MultiTapeTM.transformsTapes_seq`: transformations compose, bounds adding.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State₀ State₁ : Type*} {input : List Symbol}

/-- The sequential composition of `tm₀` and `tm₁`: it behaves like `tm₀` until `tm₀` would halt,
at which point it switches to the initial state of `tm₁` and behaves like `tm₁`. The switch is
folded into the halting transition of `tm₀`, so it costs no step. -/
def seq (tm₀ : MultiTapeTM k Symbol State₀) (tm₁ : MultiTapeTM k Symbol State₁) :
    MultiTapeTM k Symbol (State₀ ⊕ State₁) where
  q₀ := .inl tm₀.q₀
  tr q inp work :=
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
  simp only [step, h1, hq]
  rfl

lemma step_rightCfg (cfg : Cfg k Symbol State₁ input) :
    (tm₀.seq tm₁).step (rightCfg cfg) = rightCfg (tm₁.step cfg) := by
  cases hq : cfg.state with
  | none =>
    have h1 : (rightCfg (State₀ := State₀) cfg).state = none := by simp [rightCfg, Cfg.mapState, hq]
    simp only [step, h1, hq]
  | some q =>
    have h1 : (rightCfg (State₀ := State₀) cfg).state = some (Sum.inr q : State₀ ⊕ State₁) := by
      simp [rightCfg, hq]
    simp only [step, h1, hq]
    rfl

/-- The second phase of `seq` mirrors the run of `tm₁`. -/
lemma runFrom_rightCfg (cfg : Cfg k Symbol State₁ input) (n : ℕ) :
    (tm₀.seq tm₁).runFrom (rightCfg cfg) n = rightCfg (tm₁.runFrom cfg n) :=
  runFrom_comm_of_step rightCfg (fun c => step_rightCfg c) cfg n

/-- While `tm₀` is running, `seq` mirrors it. -/
lemma runFrom_leftCfg (cfg : Cfg k Symbol State₀ input) (n : ℕ)
    (h : ∀ m < n, (tm₀.runFrom cfg m).state ≠ none) :
    (tm₀.seq tm₁).runFrom (leftCfg tm₁ cfg) n = leftCfg tm₁ (tm₀.runFrom cfg n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [runFrom_succ_eq_step', runFrom_succ_eq_step', ih fun m hm => h m (by omega),
      step_leftCfg _ (h n (by omega))]

@[simp]
lemma workTapePos_leftCfg (cfg : Cfg k Symbol State₀ input) :
    (leftCfg tm₁ cfg).workTapePos = cfg.workTapePos := rfl

@[simp]
lemma workTapePos_rightCfg (cfg : Cfg k Symbol State₁ input) :
    (rightCfg (State₀ := State₀) cfg).workTapePos = cfg.workTapePos := rfl

end Sequential

open Sequential in
/-- **Sequential composition of transformations.** If the postcondition of the first
transformation implies the precondition of the second, the composed machine performs the two
transformations one after the other, with the time and space bounds adding. -/
theorem transformsTapes_seq
    {P₀ P₁ : (input : List Symbol) → (Fin k → List Symbol) → Prop}
    {Q₀ Q₁ : (input : List Symbol) → (Fin k → List Symbol) → (Fin k → List Symbol) → Prop}
    {t₀ s₀ t₁ s₁ : ℕ}
    (h₀ : TransformsTapes tm₀ P₀ Q₀ t₀ s₀) (h₁ : TransformsTapes tm₁ P₁ Q₁ t₁ s₁)
    (hmid : ∀ input ws ws', P₀ input ws → Q₀ input ws ws' → P₁ input ws') :
    TransformsTapes (tm₀.seq tm₁) P₀
      (fun input ws ws'' => ∃ ws', Q₀ input ws ws' ∧ Q₁ input ws' ws'')
      (t₀ + t₁) (s₀ + s₁) := by
  intro input ws out hP₀
  obtain ⟨τ₀, hτ₀, ws', hrun₀, hQ₀, hspace₀⟩ := h₀ input ws out hP₀
  obtain ⟨τ₁, hτ₁, ws'', hrun₁, hQ₁, hspace₁⟩ := h₁ input ws' out (hmid input ws ws' hP₀ hQ₀)
  -- the first halting time of the first machine
  obtain ⟨u, hu, huhalt, huactive⟩ := exists_minimal_halting_time tm₀
    (wordsCfg input (some tm₀.q₀) ws out) τ₀ (by simp [hrun₀])
  have hu_run : tm₀.runFrom (wordsCfg input (some tm₀.q₀) ws out) u =
      wordsCfg input none ws' out := by
    rw [← runFrom_eq_of_halt tm₀ _ hu huhalt, hrun₀]
  -- the first phase mirrors the first machine, ending in the handoff configuration
  have hleft : ∀ m ≤ u, (tm₀.seq tm₁).runFrom (wordsCfg input (some (tm₀.seq tm₁).q₀) ws out) m
      = leftCfg tm₁ (tm₀.runFrom (wordsCfg input (some tm₀.q₀) ws out) m) := by
    intro m hm
    have : wordsCfg (State := State₀ ⊕ State₁) input (some (tm₀.seq tm₁).q₀) ws out =
        leftCfg tm₁ (wordsCfg input (some tm₀.q₀) ws out) := rfl
    rw [this, runFrom_leftCfg _ m fun r hr =>
      huactive r (by omega)]
  -- the handoff configuration is the second machine's start, seen through the right embedding
  have hhandoff : leftCfg tm₁ (tm₀.runFrom (wordsCfg input (some tm₀.q₀) ws out) u) =
      rightCfg (wordsCfg input (some tm₁.q₀) ws' out) := by
    rw [hu_run]
    rfl
  refine ⟨u + τ₁, by omega, ws'', ?_, ⟨ws', hQ₀, hQ₁⟩, ?_⟩
  · rw [runFrom_add, hleft u le_rfl, hhandoff, runFrom_rightCfg, hrun₁]
    rfl
  · refine le_trans (spaceUsed_add_le _ _ _) (Nat.add_le_add ?_ ?_)
    · -- the first phase visits what the first machine visits
      refine le_trans (le_of_eq (spaceUsed_eq_of_workTapePos _ _ u fun m hm => ?_))
        (le_trans (spaceUsed_mono tm₀ _ hu) hspace₀)
      rw [hleft m hm, workTapePos_leftCfg]
    · -- the second phase visits what the second machine visits
      rw [hleft u le_rfl, hhandoff]
      refine le_trans (le_of_eq (spaceUsed_eq_of_workTapePos _ _ τ₁ fun m hm => ?_)) hspace₁
      rw [runFrom_rightCfg, workTapePos_rightCfg]

end Turing.MultiTapeTM
