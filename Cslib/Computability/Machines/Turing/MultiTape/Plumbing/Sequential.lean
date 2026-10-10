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

* `Turing.MultiTapeNTM.seq`: the composed machine.
* `Turing.MultiTapeNTM.RunPath.exists_seq`: paths compose from arbitrary configurations, with
  time and space bounds adding; repeated halted configurations in the first path are discarded.
* `Turing.MultiTapeNTM.RunPath.exists_seq_of_invariant`: invariants of state-free configurations
  compose, allowing tighter space bounds when the phases revisit cells.
* `Turing.MultiTapeNTM.transformsTapes_seq`: transformations compose, bounds adding.
-/

@[expose] public section

namespace Turing.MultiTapeNTM

variable {k : ℕ} {Symbol State₀ State₁ : Type*} {input : List Symbol}

/-- The sequential composition of `tm₀` and `tm₁`: it behaves like `tm₀` until `tm₀` would halt,
at which point it switches to the initial state of `tm₁` and behaves like `tm₁`. The switch is
folded into the halting transition of `tm₀`, so it costs no step. -/
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

/-- A configuration of the first phase: a configuration of `tm₀`, with a halted state mapped to
the initial state of the second phase. Under this map, the whole first phase of `seq` mirrors the
run of `tm₀`, *including* its halting step. -/
def leftCfg (tm₁ : MultiTapeNTM k Symbol State₁) (cfg : Cfg k Symbol State₀ input) :
    Cfg k Symbol (State₀ ⊕ State₁) input :=
  cfg.mapState (fun st ↦ some (st.elim (.inr tm₁.q₀) .inl))

/-- A configuration of the second phase. Under this map, the second phase of `seq` mirrors the
run of `tm₁`. -/
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

@[simp]
lemma workTapePos_leftCfg (cfg : Cfg k Symbol State₀ input) :
    (leftCfg tm₁ cfg).workTapePos = cfg.workTapePos := rfl

@[simp]
lemma workTapePos_rightCfg (cfg : Cfg k Symbol State₁ input) :
    (rightCfg (State₀ := State₀) cfg).workTapePos = cfg.workTapePos := rfl

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
/-- **Invariants of sequential composition.** A property of the state-free configurations is
preserved when it holds before the first path halts and throughout the second path. The composed
path has the same endpoints, and its time and space are bounded by the sums of the two bounds. -/
theorem RunPath.exists_seq_of_invariant (p : tm₀.RunPath input) (q : tm₁.RunPath input)
    (hmid : p.last.Halted) (hq : q.head = p.last.withState (some tm₁.q₀))
    {P : Cfg k Symbol Unit input → Prop}
    (hp : ∀ c ∈ p, ¬c.Halted → P c.forgetState) (hq' : ∀ c ∈ q, P c.forgetState) :
    ∃ r : (tm₀.seq tm₁).RunPath input,
      r.head = leftCfg tm₁ p.head ∧ r.last = rightCfg q.last ∧
      r.length ≤ p.length + q.length ∧ r.space ≤ p.space + q.space ∧ ∀ c ∈ r, P c.forgetState := by
  obtain ⟨i, hi, hactive⟩ := p.exists_first_halt hmid
  let left : (tm₀.seq tm₁).RunPath input :=
    { length := i
      toFun n := leftCfg tm₁ (p.take i n)
      step n := step_leftCfg (hactive _ (by exact n.isLt)) ((p.take i).step n) }
  let right : (tm₀.seq tm₁).RunPath input := q.map ⟨rightCfg, step_rightCfg⟩
  have hjoin : left.last = right.head := by
    change leftCfg tm₁ (p.take i).last = rightCfg q.head
    rw [RelSeries.last_take, hi, leftCfg_of_halt hmid, hq]
  refine ⟨left.smash right hjoin, ?_, ?_, ?_, ?_, ?_⟩
  · rw [RelSeries.head_smash]
    exact congrArg (leftCfg tm₁) (RelSeries.head_take p i)
  · rw [RelSeries.last_smash]
    rfl
  · change i.val + q.length ≤ p.length + q.length
    exact Nat.add_le_add_right (Nat.le_of_lt_succ i.isLt) _
  · exact (space_smash_le left right hjoin).trans
      (Nat.add_le_add_right (space_take_le p i) _)
  · rintro _ ⟨n, rfl⟩
    induction n using Fin.addCases (m := i.val) (n := q.length + 1) with
    | left n =>
      simpa only [RelSeries.smash, left, right, RelSeries.map, Fin.addCases_left,
        Function.comp_apply, forgetState_leftCfg] using
        hp (p.take i n.castSucc) ⟨_, rfl⟩ (hactive _ n.isLt)
    | right n =>
      simpa only [RelSeries.smash, left, right, RelSeries.map, Fin.addCases_right,
        Function.comp_apply, forgetState_rightCfg] using hq' (q n) ⟨n, rfl⟩

open Sequential in
/-- **Sequential composition of paths.** If `p` halts, and `q` starts where `p` halted with the
second machine's initial state, the composed machine has a path with the same endpoints and
with time and space bounded by the sums of the two bounds. The first path may have halted before
its last step; repeated halted configurations are discarded before starting the second phase. -/
theorem RunPath.exists_seq (p : tm₀.RunPath input) (q : tm₁.RunPath input)
    (hmid : p.last.Halted) (hq : q.head = p.last.withState (some tm₁.q₀)) :
    ∃ r : (tm₀.seq tm₁).RunPath input,
      r.head = leftCfg tm₁ p.head ∧ r.last = rightCfg q.last ∧
      r.length ≤ p.length + q.length ∧ r.space ≤ p.space + q.space := by
  obtain ⟨r, hr, hr', ht, hs, _⟩ := p.exists_seq_of_invariant q hmid hq
    (P := fun _ ↦ True) (fun _ _ _ ↦ trivial) (fun _ _ ↦ trivial)
  exact ⟨r, hr, hr', ht, hs⟩

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
      (fun input ws ws'' e ↦ ∃ ws' e₀ e₁, Q₀ input ws ws' e₀ ∧ Q₁ input ws' ws'' e₁ ∧
        e = e₀ ++ e₁)
      (t₀ + t₁) (s₀ + s₁) := by
  intro input ws out hP₀
  obtain ⟨ws', e₀, p, hp, hlast, hQ₀, ht₀, hs₀⟩ := h₀ input ws out hP₀
  obtain ⟨ws'', e₁, q, hq, hlast', hQ₁, ht₁, hs₁⟩ :=
    h₁ input ws' (out ++ e₀) (hmid input ws ws' e₀ hP₀ hQ₀)
  obtain ⟨r, hr, hr', ht, hs⟩ := p.exists_seq q (by rw [hlast]; rfl)
    (by rw [hq, hlast]; rfl)
  refine ⟨ws'', e₀ ++ e₁, r, ?_, ?_, ⟨ws', e₀, e₁, hQ₀, hQ₁, rfl⟩,
    ht.trans (Nat.add_le_add ht₀ ht₁), hs.trans (Nat.add_le_add hs₀ hs₁)⟩
  · rw [hr, hp]
    rfl
  · rw [hr', hlast']
    simp [rightCfg, Cfg.mapState, wordsCfg, List.append_assoc]

end Turing.MultiTapeNTM
