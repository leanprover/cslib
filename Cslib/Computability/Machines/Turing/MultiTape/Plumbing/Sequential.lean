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
* `Turing.MultiTapeTM.exists_runPath_seq`: run paths compose, and the composed path visits only
  cells that the two paths visit.
* `Turing.MultiTapeTM.transformsTapes_seq`: transformations compose, bounds adding.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State₀ State₁ : Type*} {input : List Symbol}

/-- The state of the sequential composition while `tm₀` runs: halting hands over to `tm₁` in its
initial state. -/
def Sequential.leftState (tm₁ : MultiTapeTM k Symbol State₁) (state : Option State₀) :
    Option (State₀ ⊕ State₁) :=
  some (state.elim (.inr tm₁.q₀) .inl)

/-- The sequential composition of `tm₀` and `tm₁`: it behaves like `tm₀` until `tm₀` would halt,
at which point it switches to the initial state of `tm₁` and behaves like `tm₁`. The switch is
folded into the halting transition of `tm₀`, so it costs no step. -/
noncomputable def seq (tm₀ : MultiTapeTM k Symbol State₀) (tm₁ : MultiTapeTM k Symbol State₁) :
    MultiTapeTM k Symbol (State₀ ⊕ State₁) :=
  ofTr (.inl tm₀.q₀) fun q inp work =>
    match q with
    | .inl q₀ => (tm₀.tr q₀ inp work).mapState (Sequential.leftState tm₁)
    | .inr q₁ => (tm₁.tr q₁ inp work).mapState (Option.map .inr)

variable {tm₀ : MultiTapeTM k Symbol State₀} {tm₁ : MultiTapeTM k Symbol State₁}

namespace Sequential

/-- A configuration of the first phase: a configuration of `tm₀`, with a halted state mapped to
the initial state of the second phase. Under this map, the whole first phase of `seq` mirrors the
run of `tm₀`, *including* its halting step. -/
def leftCfg (tm₁ : MultiTapeTM k Symbol State₁) (cfg : Cfg k Symbol State₀ input) :
    Cfg k Symbol (State₀ ⊕ State₁) input :=
  cfg.mapState (leftState tm₁)

/-- A configuration of the second phase. Under this map, the second phase of `seq` mirrors the
run of `tm₁`. -/
def rightCfg (cfg : Cfg k Symbol State₁ input) :
    Cfg k Symbol (State₀ ⊕ State₁) input :=
  cfg.mapState (Option.map .inr)

/-- In its first phase, `seq tm₀ tm₁` follows `tm₀`, with halting handing over to `tm₁`. -/
lemma follows_left : (tm₀.seq tm₁).Follows tm₀ .inl (.mapState (leftState tm₁)) :=
  fun _ _ _ h => tr_iff.mp h ▸ rfl

/-- In its second phase, `seq tm₀ tm₁` follows `tm₁`. -/
lemma follows_right : (tm₀.seq tm₁).Follows tm₁ .inr (.mapState (Option.map .inr)) :=
  fun _ _ _ h => tr_iff.mp h ▸ rfl

/-- The first phase of `seq tm₀ tm₁` mirrors the running steps of `tm₀`. -/
@[simps! apply]
noncomputable def leftCfgHom : (tm₀.runningStepRel input).Hom ((tm₀.seq tm₁).stepRel input) :=
  follows_left.runningStepHom (leftCfg tm₁)
    (fun _ _ => congrArg (leftState tm₁)) (fun _ => rfl) fun _ _ => rfl

/-- The second phase of `seq tm₀ tm₁` mirrors the steps of `tm₁`. -/
@[simps! apply]
noncomputable def rightCfgHom : (tm₁.stepRel input).Hom ((tm₀.seq tm₁).stepRel input) :=
  follows_right.stepHom rightCfg (fun _ => rfl) (fun _ => rfl) fun _ _ => rfl

/-- A halted configuration of the first phase is the start of the second phase. -/
lemma leftCfg_of_halt {cfg : Cfg k Symbol State₀ input} (h : cfg.state = none) :
    leftCfg tm₁ cfg = rightCfg (cfg.withState (some tm₁.q₀)) := by
  simp [leftCfg, leftState, rightCfg, Cfg.withState, Cfg.mapState, h]

end Sequential

open Sequential in
/-- **Sequential composition of runs.** A run path of `tm₀` to a halted configuration, followed by a
run path of `tm₁` started where `tm₀` halted, gives a run path of `seq` of at most as many steps,
which visits only cells that the two paths visit. -/
theorem exists_runPath_seq {p₀ : tm₀.RunPath input} (h₀ : p₀.last.Halted)
    {p₁ : tm₁.RunPath input} (h₁ : p₁.head = p₀.last.withState (some tm₁.q₀)) :
    ∃ p : (tm₀.seq tm₁).RunPath input, p.head = leftCfg tm₁ p₀.head ∧
      p.last = rightCfg p₁.last ∧ p.length ≤ p₀.length + p₁.length ∧
      ∀ i, p.visitedByTapeHead i ⊆ p₀.visitedByTapeHead i ∪ p₁.visitedByTapeHead i := by
  -- `seq` takes the running steps of `tm₀`, then the steps of `tm₁`
  obtain ⟨q₀, hh₀, hl₀, hlen₀, hmem₀⟩ := p₀.exists_running h₀
  refine ⟨(q₀.map leftCfgHom).smash (p₁.map rightCfgHom)
    (by simp [hl₀, h₁, leftCfg_of_halt h₀]), by simp [hh₀], by simp, by simp; lia,
    fun i z hz => ?_⟩
  obtain ⟨c, hc, rfl⟩ := (MultiTapeNTM.RunPath.mem_visitedByTapeHead _).mp hz
  rcases RelSeries.mem_or_mem_of_mem_smash hc with hc | hc <;>
    obtain ⟨c', hc', rfl⟩ := RelSeries.exists_of_mem_map hc
  · exact Finset.mem_union_left _ (p₀.mem_visitedByTapeHead.mpr ⟨c', hmem₀ c' hc', rfl⟩)
  · exact Finset.mem_union_right _ (p₁.mem_visitedByTapeHead.mpr ⟨c', hc', rfl⟩)

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
  obtain ⟨p, hh, hl, ht, hvisited⟩ := exists_runPath_seq (p₀ := p₀) (p₁ := p₁)
    (by rw [hl₀]; rfl) (by simp [hh₁, hl₀])
  -- the composed run visits only cells that one of the two runs visits
  exact ⟨ws'', e₀ ++ e₁, ⟨ws', e₀, e₁, hQ₀, hQ₁, rfl⟩, p, by simp [hh, hh₀, leftCfg]; rfl,
    by simp [hl, hl₁, rightCfg], ht.trans (Nat.add_le_add ht₀ ht₁),
    ((Finset.sum_le_sum fun i _ => (Finset.card_le_card (hvisited i)).trans
      (Finset.card_union_le _ _)).trans_eq Finset.sum_add_distrib).trans (Nat.add_le_add hs₀ hs₁)⟩

end Turing.MultiTapeTM
