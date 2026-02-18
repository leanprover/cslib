/-
Copyright (c) 2025 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Automata.NA.Hist
public import Cslib.Computability.Automata.NA.Prod
public import Cslib.Foundations.Data.OmegaSequence.Temporal

@[expose] public section

/-! # Intersection of nondeterministic Buchi automata.

The intersection automaton consists of the product of the two automata to be intersected
plus a history state which is a pointer to one of the two automata. It waits for the
accepting condition of the automaton being pointed to by the history state. Once it sees that,
it toggles the history state to wait for the accepting condition of the other automaton.
The intersection automaton accepts iff the toggling happens infinitely many times.

The two automata to be intersected are indexed by the type `Bool`.  We choose `Bool`
simply because toggling can be easily modeled by the boolean operation `not`.
-/

namespace Cslib.Automata.NA.Buchi

open Set Prod Filter ωSequence ωAcceptor
open scoped LTS

variable {Symbol : Type*} {State : Bool → Type*}

/-- The initial history state. -/
@[scoped grind =, nolint unusedArguments]
def histStart (_ : Π i, State i) : Bool := false

/-- The two accepting conditions of the intersection automaton. -/
@[scoped grind =]
def interAcc (j : Bool) (acc : (i : Bool) → Set (State i)) : Set ((Π i, State i) × Bool) :=
  { (s, h) | s j ∈ acc j ∧ h = j }

open scoped Classical in
/-- The transition function of the history state. -/
@[scoped grind =, nolint unusedArguments]
noncomputable def histTrans (acc : (i : Bool) → Set (State i))
    (s : (Π i, State i) × Bool) (_ : Symbol) (_ : Π i, State i) : Bool :=
  if s ∈ interAcc false acc then true else
  if s ∈ interAcc true acc then false else s.snd

/-- The intersection automaton. -/
@[scoped grind =]
noncomputable def interNA (na : (i : Bool) → NA (State i) Symbol)
    (acc : (i : Bool) → Set (State i)) : NA ((Π i, State i) × Bool) Symbol :=
  (iProd na).addHist histStart (histTrans acc)

/-- The overall accepting conditon of the intersection automaton. -/
@[scoped grind =]
def interAccept (acc : (i : Bool) → Set (State i)) : Set ((Π i, State i) × Bool) :=
  interAcc false acc ∪ interAcc true acc

variable {na : (i : Bool) → NA (State i) Symbol} {acc : (i : Bool) → Set (State i)}

/-- If the intersection automaton sees one accepting condtion infinitely many times,
then it sees the other accepting condition infinitely many times as well. -/
lemma inter_freq_acc_freq_acc {xs : ωSequence Symbol} {ss : ωSequence ((Π i, State i) × Bool)}
    {i : Bool} (h_run : (interNA na acc).Run xs ss) (h_inf : ∃ᶠ k in atTop, ss k ∈ interAcc i acc) :
    ∃ᶠ k in atTop, ss k ∈ interAcc (!i) acc := by
  have (k : ℕ) := (h_run.trans k).right
  apply frequently_leadsTo_frequently h_inf
  apply leadsTo_trans (q := {s | s.snd = !i})
  · apply step_leadsTo
    grind
  · apply until_frequently_not_leadsTo
    · grind
    · apply Frequently.mono h_inf
      grind

/-- If the intersection automaton sees the accepting condtions of both component automata
infinitely many times, then its own accepting condition also happens infinitely many times. -/
lemma inter_freq_comp_acc_freq_acc {xs : ωSequence Symbol} {ss : ωSequence ((Π i, State i) × Bool)}
    (h_run : (interNA na acc).Run xs ss)
    (h_inf_f : ∃ᶠ k in atTop, ss k ∈ {s | s.fst false ∈ acc false})
    (h_inf_t : ∃ᶠ k in atTop, ss k ∈ {s | s.fst true ∈ acc true}) :
    ∃ᶠ k in atTop, ss k ∈ interAccept acc := by
  have (k : ℕ) := (h_run.trans k).right
  have h_univ : ∃ᶠ k in atTop, ss k ∈ univ := by simp [atTop_neBot]
  have (b : Bool) : interAcc b acc = {⟨_, b'⟩ | b' = b} ∩ {⟨p,_⟩ | p b ∈ acc b} := by
    ext; grind
  have : {⟨_, b⟩ : (Π i, State i) × Bool | b = false}ᶜ = {⟨_, b⟩ | b = true} := by
    ext; grind
  apply frequently_leadsTo_frequently h_univ
  apply leadsTo_cases_or (q := {⟨_, b⟩ | b = false}) <;>
  grind [until_frequently_leadsTo_and, univ_inter]

-- TODO: fix proof to work with backward.isDefEq.respectTransparency
set_option backward.isDefEq.respectTransparency false in
/-- The language accepted by the intersection automaton is the intersection of
the languages accepted by the two component automata. -/
@[simp, scoped grind =]
theorem inter_language_eq :
    language (Buchi.mk (interNA na acc) (interAccept acc)) =
    ⋂ i, language (Buchi.mk (na i) (acc i)) := by
  ext xs
  rw [mem_iInter]
  constructor
  · intro ⟨ss, h_run, h_inf⟩ i
    use ss.map (fun s ↦ s.fst i)
    constructor
    · apply iProd_run_iff.mp <| hist_run_proj h_run
    · simp only [interAccept, mem_union, frequently_or_distrib] at h_inf
      cases i
      · rcases h_inf with h_inf_f | h_inf_t
        · apply Frequently.mono h_inf_f
          grind
        · apply Frequently.mono <| inter_freq_acc_freq_acc h_run h_inf_t
          grind
      · rcases h_inf with h_inf_f | h_inf_t
        · apply Frequently.mono <| inter_freq_acc_freq_acc h_run h_inf_f
          grind
        · apply Frequently.mono h_inf_t
          grind
  · intro h
    choose ss_i h_ss_i using h
    let ss_p : ωSequence (Π i, State i) := fun k i ↦ ss_i i k
    have h_ss_p : (iProd na).Run xs ss_p := by grind [Run]
    have (k : ℕ) (i : Bool) : ss_p k i = ss_i i k := rfl
    obtain ⟨ss, h_run, _⟩ := hist_run_exists h_ss_p
    use ss, h_run
    apply inter_freq_comp_acc_freq_acc h_run
    · apply Frequently.mono (h_ss_i false).2
      grind
    · apply Frequently.mono (h_ss_i true).2
      grind

end Cslib.Automata.NA.Buchi
