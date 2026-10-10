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
* `Turing.MultiTapeTM.HaltsAt.runFrom_seq`: once `tm₀` halts, `seq` mirrors `tm₁`.
* `Turing.MultiTapeTM.runFrom_seq`: runs compose; each machine only has to have halted by the end
  of its time bound.
* `Turing.MultiTapeTM.forgetState_runFrom_seq`: invariants of the state-free part of a
  configuration compose, which bounds the space of the composed run.
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

/-- The second phase of `seq` mirrors the run of `tm₁`. -/
lemma runFrom_rightCfg (cfg : Cfg k Symbol State₁ input) (n : ℕ) :
    (tm₀.seq tm₁).runFrom (rightCfg cfg) n = rightCfg (tm₁.runFrom cfg n) :=
  (Function.Semiconj.iterate_right (fun c => (step_rightCfg c).symm) n cfg).symm

/-- While `tm₀` is running, `seq` mirrors it. -/
lemma runFrom_leftCfg (cfg : Cfg k Symbol State₀ input) (n : ℕ)
    (h : ∀ m < n, (tm₀.runFrom cfg m).state ≠ none) :
    (tm₀.seq tm₁).runFrom (leftCfg tm₁ cfg) n = leftCfg tm₁ (tm₀.runFrom cfg n) := by
  simp only [runFrom] at h ⊢
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      ih fun m hm => h m (by omega),
      step_leftCfg _ (h n (by omega))]

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
/-- If `tm₀` halts at step `u`, then from step `u` on `seq` mirrors `tm₁`, started where `tm₀`
halted. -/
lemma HaltsAt.runFrom_seq {cfg : Cfg k Symbol State₀ input} {u : ℕ} (h : tm₀.HaltsAt cfg u)
    (n : ℕ) :
    (tm₀.seq tm₁).runFrom (leftCfg tm₁ cfg) (u + n) =
      rightCfg (tm₁.runFrom ((tm₀.runFrom cfg u).withState (some tm₁.q₀)) n) := by
  have hhandoff : (tm₀.seq tm₁).runFrom (leftCfg tm₁ cfg) u =
      rightCfg ((tm₀.runFrom cfg u).withState (some tm₁.q₀)) := by
    rw [runFrom_leftCfg cfg u fun _ hm => h.not_halted hm, leftCfg_of_halt h.halted]
  simp only [runFrom] at hhandoff ⊢
  rw [Nat.add_comm, Function.iterate_add_apply, hhandoff]
  exact runFrom_rightCfg _ n

open Sequential in
/-- **Sequential composition of runs.** If `tm₀` has halted in `mid` by step `t₀`, and `tm₁`,
started where `tm₀` halted, has halted in `fin` by step `t₁`, then the composed machine has halted
in `fin` by step `t₀ + t₁`. Each machine may halt earlier than its bound; in particular `tm₀` need
not be running at every step before `t₀`. -/
theorem runFrom_seq {cfg mid : Cfg k Symbol State₀ input} {fin : Cfg k Symbol State₁ input}
    {t₀ t₁ : ℕ} (h₀ : tm₀.runFrom cfg t₀ = mid) (hmid : mid.Halted)
    (h₁ : tm₁.runFrom (mid.withState (some tm₁.q₀)) t₁ = fin) (hfin : fin.Halted) :
    (tm₀.seq tm₁).runFrom (leftCfg tm₁ cfg) (t₀ + t₁) = rightCfg fin := by
  obtain ⟨u, hu, hhaltsAt⟩ := exists_haltsAt (tm := tm₀) (cfg := cfg) (h₀ ▸ hmid)
  have hrun : (tm₀.seq tm₁).runFrom (leftCfg tm₁ cfg) (u + t₁) = rightCfg fin := by
    rw [hhaltsAt.runFrom_seq, ← hhaltsAt.runFrom_eq hu, h₀, h₁]
  have hhalt : ((tm₀.seq tm₁).runFrom (leftCfg tm₁ cfg) (u + t₁)).Halted := by
    simp only [hrun, Cfg.Halted] at hfin ⊢
    simp [rightCfg, hfin]
  rw [runFrom_eq_of_halt _ _ (by omega) hhalt, hrun]

open Sequential in
/-- **Invariants of a sequential run.** If `tm₀` has halted in `mid` by step `t₀`, then a property
of the state-free part of a configuration holds throughout the run of the composed machine if it
holds before step `t₀` of the run of `tm₀` and throughout the run of `tm₁` started where `tm₀`
halted. -/
theorem forgetState_runFrom_seq {P : Cfg k Symbol Unit input → Prop}
    {cfg mid : Cfg k Symbol State₀ input} {t₀ : ℕ} (h₀ : tm₀.runFrom cfg t₀ = mid)
    (hmid : mid.Halted) (hP₀ : ∀ m < t₀, P (tm₀.runFrom cfg m).forgetState)
    (hP₁ : ∀ n, P (tm₁.runFrom (mid.withState (some tm₁.q₀)) n).forgetState) (m : ℕ) :
    P ((tm₀.seq tm₁).runFrom (leftCfg tm₁ cfg) m).forgetState := by
  obtain ⟨u, hu, hhaltsAt⟩ := exists_haltsAt (tm := tm₀) (cfg := cfg) (h₀ ▸ hmid)
  rcases Nat.lt_or_ge m u with hm | hm
  · rw [runFrom_leftCfg cfg m fun _ hr => hhaltsAt.not_halted (by lia), forgetState_leftCfg]
    exact hP₀ m (by lia)
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [hhaltsAt.runFrom_seq, ← hhaltsAt.runFrom_eq hu, h₀, forgetState_rightCfg]
    exact hP₁ n

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
  obtain ⟨ws', e₀, hrun₀, hQ₀, hspace₀⟩ := h₀ input ws out hP₀
  obtain ⟨ws'', e₁, hrun₁, hQ₁, hspace₁⟩ :=
    h₁ input ws' (out ++ e₀) (hmid input ws ws' e₀ hP₀ hQ₀)
  refine ⟨ws'', e₀ ++ e₁, ?_, ⟨ws', e₀, e₁, hQ₀, hQ₁, rfl⟩, fun p hp => ?_⟩
  · exact runFrom_seq hrun₀ rfl (by simpa using hrun₁) rfl
  -- every head position of the composed run is one of the first machine up to `t₀` or one of the
  -- second machine up to `t₁`, after which the second machine stays halted
  let p₀ : tm₀.RunPath input := .ofDeterministic tm₀ (wordsCfg input (some tm₀.q₀) ws out) t₀
  let p₁ : tm₁.RunPath input :=
    .ofDeterministic tm₁ (wordsCfg input (some tm₁.q₀) ws' (out ++ e₀)) t₁
  refine (p.space_le_sum_card (S := fun i => p₀.visitedByTapeHead i ∪ p₁.visitedByTapeHead i)
    fun c hc i => ?_).trans ?_
  · obtain ⟨m, rfl⟩ := hc
    rw [runPath_apply_eq_runFrom, hp]
    refine forgetState_runFrom_seq (P := fun c => c.workTapePos i ∈ _) hrun₀ rfl
      (fun m hm => Finset.mem_union_left _ (Finset.mem_image_of_mem _
        (Finset.mem_univ (⟨m, by omega⟩ : Fin (t₀ + 1))))) (fun n => Finset.mem_union_right _ ?_) m
    rcases le_total n t₁ with hn | hn
    · exact Finset.mem_image_of_mem _ (Finset.mem_univ (⟨n, by omega⟩ : Fin (t₁ + 1)))
    · rw [withState_wordsCfg, runFrom_eq_of_halt _ _ hn (by rw [hrun₁]; rfl)]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ (Fin.last t₁))
  · exact ((Finset.sum_le_sum fun i _ => Finset.card_union_le _ _).trans_eq
      Finset.sum_add_distrib).trans (Nat.add_le_add (hspace₀ p₀ rfl) (hspace₁ p₁ rfl))

end Turing.MultiTapeTM
