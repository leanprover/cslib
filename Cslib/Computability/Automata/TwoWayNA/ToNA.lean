/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Automata.NA.Basic
public import Cslib.Computability.Automata.TwoWayNA.Basic
public import Cslib.Computability.Languages.RegularLanguage
public import Cslib.Foundations.Semantics.LTS.Relation

/-! # Two-way automata are not more powerful than one-way automata

Every language recognised by a nondeterministic two-way automaton (`TwoWayNA`) is also recognised by
a one-way nondeterministic automaton (`NA`). We follow Vardi's proof, which -- unlike
Shepherdson's classical crossing-sequence argument -- proceeds by characterising *non*-acceptance
in a way that can be checked by a single left-to-right sweep over the input.

## Vardi's condition of non-acceptance

Fix a `TwoWayNA` `a` and an input word `input` of length `n`. A *rejection certificate* is a family
of subsets `T i ⊆ State`, one for every head position `i ∈ {0, …, n}`, subject to three
conditions:

1. `T` contains every initial state at position `0` (`IsRejectionCert.start_mem`);
2. `T` is an invariant of the transitions of `a`: if the state `c.state` is in `T c.pos` and `a`
   can step from the configuration `c` to the configuration `c'`, then `c'.state` is in `T c'.pos`
   (`TwoWayNA.IsStepClosed`, `IsRejectionCert.step_closed`);
3. no state in `T n`, i.e. at the position just past the end of the input, is accepting
   (`IsRejectionCert.accept_notMem`).

Intuitively, `T i` over-approximates the set of states in which `a` can be while its head sits at
position `i`: conditions 1 and 2 make `T` an inductive invariant of the reachable configurations,
and condition 3 says that this invariant rules out acceptance -- being preserved by every step, it
holds at the end of every run (`LTS.mtrInv_of_trInv`). Conversely, the reachable states
(`TwoWayNA.reachable`) themselves form the least such family, so a certificate exists exactly when
`a` rejects (`TwoWayNA.not_accepts_iff_exists_isRejectionCert`).

## The one-way automaton

The point of the reformulation is locality: `TwoWayNA.isStepClosed_iff_localOK` turns condition 2
into a condition `TwoWayNA.LocalOK` relating only `T (i - 1)`, `T i` and `T (i + 1)` with the
symbol at position `i`. A one-way automaton can therefore guess the certificate while scanning
the input, keeping only the last two subsets in its state. This is `TwoWayNA.toNAComplement`, and
`TwoWayNA.accepts_toNAComplement_iff` shows that it accepts exactly the complement of the language
of `a`.

## Regular languages

Conversely, a one-way automaton is the special case of a two-way automaton that always moves its
head to the right (`NA.FinAcc.toTwoWayNA`). Rejection certificates play no role here: since the
head advances by exactly one symbol per step, the runs of the two-way automaton correspond directly
to multistep transitions of the one-way one (`NA.FinAcc.mTr_take_of_canReach` and
`NA.FinAcc.canReach_of_mTr`). Together with closure of regular languages under complement this
gives `Cslib.Language.IsRegular.iff_twoWayNA`: a language is regular if and only if
it is accepted by a two-way automaton with finitely many states.

## Implementation notes

A rejection certificate is indexed by `ℕ` rather than by `Fin (input.length + 1)`, the type of
`TwoWayNACfg.pos`: positions past the end of the input are simply left unconstrained, which avoids
casts when the certificate is compared along a run, whose configurations carry their own input.

Where a `List (Set State)` is more convenient is `TwoWayNA.exists_accepting_mTr_iff`, which is
proved by induction on the input word and prepends a subset to the certificate at each step.
`TwoWayNA.certOfList` and `TwoWayNA.certToList` translate between the two encodings, the latter
prefixing `Set.univ` for the missing position to the left of the input, mirroring
`TwoWayNA.prevSet`.

## References

* [M. Y. Vardi, *A note on the reduction of two-way automata to one-way automata*][Vardi1989]
-/

@[expose] public section

namespace List

/-- Dropping the head of a list shifts total indexing by one. -/
@[simp]
private theorem getI_tail {α : Type*} [Inhabited α] (l : List α) (i : ℕ) :
    l.tail.getI i = l.getI (i + 1) := by
  cases l <;> simp

end List

namespace Cslib.Automata

variable {State Symbol : Type*} {a : TwoWayNA State Symbol} {input : List Symbol}

namespace TwoWayNA

/-! ## Vardi's condition of non-acceptance -/

/-- Every step of `a` on `input` out of a state that `T` attaches to the head position lands in a
state that `T` attaches to the new head position. -/
def IsStepClosed (a : TwoWayNA State Symbol) (input : List Symbol) (T : ℕ → Set State) : Prop :=
  ∀ c c', c.input = input → (a.toCfgNAFinAcc input).UnlabelledTr c c' → c.state ∈ T c.pos →
    c'.state ∈ T c'.pos

/-- A family of subsets of the state set, one for every position of the input head on `input`,
which contains all initial states, is closed under the transitions of `a`, and contains no
accepting state at the position just past the end of the input. -/
structure IsRejectionCert (a : TwoWayNA State Symbol) (input : List Symbol)
    (T : ℕ → Set State) : Prop where
  /-- Every initial state occurs at the initial head position. -/
  start_mem : ∀ s ∈ a.start, s ∈ T 0
  /-- The family is an invariant of the transitions of `a`. -/
  step_closed : a.IsStepClosed input T
  /-- No accepting state occurs past the end of the input. -/
  accept_notMem : ∀ s ∈ T input.length, s ∉ a.accept

variable {T : ℕ → Set State}

/-- If a rejection certificate for `input` exists, then `a` does not accept `input`. -/
theorem IsRejectionCert.not_accepts (hT : a.IsRejectionCert input T) :
    ¬ Acceptor.Accepts a input := by
  rintro ⟨μs, c, ⟨hstart, hpos, hinput⟩, c', ⟨hacc, hlast⟩, hmtr⟩
  have hinv : (a.toCfgNAFinAcc input).MTrInv
      (fun d => d.input = input ∧ d.state ∈ T d.pos) := by
    apply LTS.mtrInv_of_trInv
    rintro d μ d' htr ⟨hd_input, hd_mem⟩
    exact ⟨a.toCfgNAFinAcc_input_eq input d μ d' htr hd_input,
      hT.step_closed d d' hd_input ⟨μ, htr⟩ hd_mem⟩
  obtain ⟨hinput', hmem⟩ :=
    hinv c μs c' hmtr ⟨hinput, by rw [hpos]; simpa using hT.start_mem c.state hstart⟩
  rw [hlast, Fin.val_last, hinput'] at hmem
  exact hT.accept_notMem c'.state hmem hacc

/-- The set of states that `a` can be in while its head sits at position `i` of `input`, having
started in an initial configuration. -/
def reachable (a : TwoWayNA State Symbol) (input : List Symbol) (i : ℕ) :
    Set State :=
  {q | ∃ c, c.IsInitialForInput a input ∧
      ∃ h : i < input.length + 1,
      (a.toCfgNAFinAcc input).CanReach c { input := input, pos := ⟨i, h⟩, state := q } }

/-- If `a` does not accept `input`, then its reachable states form a rejection certificate. -/
theorem isRejectionCert_reachable (h : ¬ Acceptor.Accepts a input) :
    a.IsRejectionCert input (a.reachable input) where
  start_mem s hs :=
    ⟨{ input := input, pos := ⟨0, Nat.succ_pos _⟩, state := s },
      ⟨hs, Fin.ext (by simp), rfl⟩, Nat.succ_pos _, LTS.CanReach.refl _ _⟩
  step_closed c c' hc_input htr hmem := by
    obtain ⟨c₀, hstart, hlt, hreach⟩ := hmem
    have hc'_input : c'.input = input := by
      obtain ⟨μ, htr⟩ := htr
      exact a.toCfgNAFinAcc_input_eq input c μ c' htr hc_input
    rw [TwoWayNACfg.eta hc_input hlt] at hreach
    refine ⟨c₀, hstart, by rw [← hc'_input]; exact c'.pos.isLt, ?_⟩
    rw [TwoWayNACfg.eta hc'_input]
    exact (LTS.reflTransGen_unlabelledTr_iff _).mp
      (((LTS.reflTransGen_unlabelledTr_iff _).mpr hreach).tail htr)
  accept_notMem s hs hacc := by
    obtain ⟨c₀, hstart, hlt, μs, hmtr⟩ := hs
    exact h ⟨μs, c₀, hstart, _, ⟨hacc, Fin.ext (by simp)⟩, hmtr⟩

/-- A two-way automaton rejects an input exactly when a rejection certificate for it exists. -/
theorem not_accepts_iff_exists_isRejectionCert (a : TwoWayNA State Symbol)
    (input : List Symbol) :
    ¬ Acceptor.Accepts a input ↔ ∃ T, a.IsRejectionCert input T :=
  ⟨fun h => ⟨_, isRejectionCert_reachable h⟩, by rintro ⟨_, hT⟩; exact hT.not_accepts⟩

/-! ## Localising the closure condition -/

/-- The subset that `T` attaches to the position to the left of `i`, and everything at position
`0`, which has no position to its left. -/
def prevSet (T : ℕ → Set State) : ℕ → Set State
  | 0 => Set.univ
  | i + 1 => T i

/-- Every move of `a` out of a state in `C` while reading `x` lands in `P`, in `C` or in `N`,
according to whether it moves the head to the left, keeps it in place, or moves it to the right. -/
def LocalOK (a : TwoWayNA State Symbol) (x : Symbol) (P C N : Set State) : Prop :=
  ∀ q ∈ C, ∀ m q', a.Tr q x m q' →
    q' ∈ match m with | .neg => P | .zero => C | .pos => N

/-- Closure of `T` under the transitions of `a` is the same as local consistency of `T` at every
position carrying an input symbol. -/
theorem isStepClosed_iff_localOK :
    a.IsStepClosed input T ↔
      ∀ i : Fin input.length, a.LocalOK input[i] (prevSet T i) (T i) (T (i + 1)) := by
  constructor
  · intro hcl i q hq m q' htr
    have hlt : (i : ℕ) < input.length := i.isLt
    cases m with
    | zero =>
      exact hcl ⟨input, q, ⟨i, by omega⟩⟩ ⟨input, q', ⟨i, by omega⟩⟩ rfl
        ⟨(input[i], SignType.zero), rfl, by simp, htr, by simp⟩ hq
    | pos =>
      exact hcl ⟨input, q, ⟨i, by omega⟩⟩ ⟨input, q', ⟨i + 1, by omega⟩⟩ rfl
        ⟨(input[i], SignType.pos), rfl, by simp, htr, by simp⟩ hq
    | neg =>
      obtain ⟨iv, hiv⟩ := i
      obtain _ | j := iv
      · exact Set.mem_univ q'
      · exact hcl ⟨input, q, ⟨j + 1, by omega⟩⟩ ⟨input, q', ⟨j, by omega⟩⟩ rfl
          ⟨(input[j + 1], SignType.neg), rfl, by simp, htr, by simp⟩ hq
  · rintro hloc c c' hc_input ⟨⟨x, m⟩, hstep⟩ hmem
    obtain ⟨hlt, rfl⟩ := getElem_of_tr hstep hc_input
    obtain ⟨-, -, htr, hpos⟩ := hstep
    have hthis := hloc ⟨(c.pos : ℕ), hlt⟩ c.state hmem m c'.state htr
    cases m with
    | zero =>
      rw [show (c'.pos : ℕ) = (c.pos : ℕ) by simp at hpos; omega]
      exact hthis
    | pos =>
      rw [show (c'.pos : ℕ) = (c.pos : ℕ) + 1 by simp at hpos; omega]
      exact hthis
    | neg =>
      simp only [SignType.neg_eq_neg_one, SignType.coe_neg_one] at hpos
      obtain ⟨j, hj⟩ : ∃ j, (c.pos : ℕ) = j + 1 := ⟨(c.pos : ℕ) - 1, by omega⟩
      rw [show (c'.pos : ℕ) = j by omega]
      rw [show ((⟨(c.pos : ℕ), hlt⟩ : Fin input.length) : ℕ) = j + 1 from hj] at hthis
      exact hthis

/-! ## The one-way automaton for the complement -/

/-- The one-way automaton that guesses a rejection certificate `T` for `a` while scanning the
input, keeping the pair `(T (i - 1), T i)` in its state after reading `i` symbols. Reading the
symbol at position `i` guesses `T (i + 1)` and checks local consistency at position `i`. -/
def toNAComplement (a : TwoWayNA State Symbol) : NA.FinAcc (Set State × Set State) Symbol where
  Tr PC x PC' := PC'.1 = PC.2 ∧ a.LocalOK x PC.1 PC.2 PC'.2
  start := {PC | PC.1 = Set.univ ∧ a.start ⊆ PC.2}
  accept := {PC | ∀ s ∈ PC.2, s ∉ a.accept}

/-- An accepting multistep transition of `a.toNAComplement` out of `(P, C)` over `xs` is the same
thing as a list of subsets starting with `P` and `C` that is locally consistent at every position
of `xs` and ends in a subset without accepting states. -/
theorem exists_accepting_mTr_iff (a : TwoWayNA State Symbol) (xs : List Symbol) (P C : Set State) :
    (∃ f ∈ a.toNAComplement.accept, a.toNAComplement.MTr (P, C) xs f) ↔
      ∃ T : List (Set State), T.getI 0 = P ∧ T.getI 1 = C ∧
        (∀ i, ∀ hi : i < xs.length, a.LocalOK xs[i] (T.getI i) (T.getI (i + 1)) (T.getI (i + 2))) ∧
        ∀ s ∈ T.getI (xs.length + 1), s ∉ a.accept := by
  induction xs generalizing P C with
  | nil =>
    constructor
    · rintro ⟨f, hf, hmtr⟩
      rw [LTS.MTr.nil_iff] at hmtr
      subst hmtr
      exact ⟨[P, C], by simp, by simp, by simp, by simpa [toNAComplement] using hf⟩
    · rintro ⟨T, h0, h1, -, hacc⟩
      exact ⟨(P, C), by rw [← h1]; simpa [toNAComplement] using hacc, by simp⟩
  | cons x xs ih =>
    constructor
    · rintro ⟨f, hf, hmtr⟩
      rw [LTS.MTr.cons_iff] at hmtr
      obtain ⟨⟨m₁, m₂⟩, ⟨rfl, hlocal⟩, hmtr⟩ := hmtr
      obtain ⟨T, h0, h1, hloc, hacc⟩ := (ih m₁ m₂).mp ⟨f, hf, hmtr⟩
      have hlocal' : a.LocalOK x P m₁ m₂ := hlocal
      have hstep : ∀ i, ∀ hi : i < (x :: xs).length,
          a.LocalOK (x :: xs)[i]
            ((P :: T).getI i) ((P :: T).getI (i + 1)) ((P :: T).getI (i + 2)) := by
        intro i hi
        obtain _ | i := i
        · simpa [h0, h1] using hlocal'
        · simpa using hloc i (by simpa using hi)
      exact ⟨P :: T, by simp, by simpa using h0, hstep, by simpa using hacc⟩
    · rintro ⟨T, h0, h1, hloc, hacc⟩
      have hstep : ∀ i, ∀ hi : i < xs.length,
          a.LocalOK xs[i] (T.tail.getI i) (T.tail.getI (i + 1)) (T.tail.getI (i + 2)) := by
        intro i hi
        have h := hloc (i + 1) (by simpa using hi)
        rw [List.getElem_cons_succ] at h
        simpa using h
      obtain ⟨f, hf, hmtr⟩ := (ih C (T.getI 2)).mpr
        ⟨T.tail, by simpa using h1, by simp, hstep, by simpa using hacc⟩
      have hlocal : a.LocalOK x P C (T.getI 2) := by
        have h := hloc 0 (by simp)
        rw [List.getElem_cons_zero] at h
        simpa [h0, h1] using h
      have htr : a.toNAComplement.Tr (P, C) x (C, T.getI 2) := ⟨rfl, hlocal⟩
      exact ⟨f, hf, LTS.MTr.cons_iff.mpr ⟨(C, T.getI 2), htr, hmtr⟩⟩

/-- The family of subsets carried by a list, which holds the subset for the position to the left
of `0` in front, so that position `i` is entry `i + 1` of the list. -/
def certOfList (T : List (Set State)) (i : ℕ) : Set State :=
  T.getI (i + 1)

/-- The subsets that `T` attaches to the positions of the input head, as a list, prefixed by
`Set.univ` for the position to the left of `0`. -/
def certToList (input : List Symbol) (T : ℕ → Set State) : List (Set State) :=
  Set.univ :: (List.range (input.length + 1)).map T

/-- Entry `i + 1` of `TwoWayNA.certToList` is the subset that `T` attaches to position `i`. -/
@[simp]
theorem getI_certToList {T : ℕ → Set State} {i : ℕ} (hi : i < input.length + 1) :
    (certToList input T).getI (i + 1) = T i := by
  rw [certToList, List.getI_cons_succ, List.getI_eq_getElem (hn := by simpa using hi)]
  simp

/-- `a.toNAComplement` accepts exactly the words that `a` rejects. -/
theorem accepts_toNAComplement_iff (a : TwoWayNA State Symbol) (input : List Symbol) :
    Acceptor.Accepts a.toNAComplement input ↔ ¬ Acceptor.Accepts a input := by
  rw [not_accepts_iff_exists_isRejectionCert]
  constructor
  · rintro ⟨s, ⟨hs, hstart⟩, f, hf, hmtr⟩
    obtain ⟨T, h0, h1, hloc, hacc⟩ := (exists_accepting_mTr_iff a input s.1 s.2).mp ⟨f, hf, hmtr⟩
    have hstep : ∀ i : Fin input.length,
        a.LocalOK input[i] (prevSet (certOfList T) i) (certOfList T i) (certOfList T (i + 1)) := by
      intro i
      obtain ⟨iv, hiv⟩ := i
      obtain _ | j := iv
      · simpa [prevSet, certOfList, h0, hs] using hloc 0 hiv
      · simpa [prevSet, certOfList] using hloc (j + 1) hiv
    exact ⟨certOfList T,
      { start_mem := by
          intro q hq
          simpa [certOfList, h1] using hstart hq
        step_closed := isStepClosed_iff_localOK.mpr hstep
        accept_notMem := by simpa [certOfList] using hacc }⟩
  · rintro ⟨T, hT⟩
    have hloc := isStepClosed_iff_localOK.mp hT.step_closed
    have hstep : ∀ i, ∀ hi : i < input.length, a.LocalOK input[i]
        ((certToList input T).getI i) ((certToList input T).getI (i + 1))
          ((certToList input T).getI (i + 2)) := by
      intro i hi
      have e0 : (certToList input T).getI i = prevSet T i := by
        obtain _ | j := i
        · rfl
        · exact getI_certToList (by omega)
      have e1 : (certToList input T).getI (i + 1) = T i := getI_certToList (by omega)
      have e2 : (certToList input T).getI (i + 2) = T (i + 1) := getI_certToList (by omega)
      rw [e0, e1, e2]
      exact hloc ⟨i, hi⟩
    obtain ⟨f, hf, hmtr⟩ := (exists_accepting_mTr_iff a input Set.univ (T 0)).mpr
      ⟨certToList input T, rfl, getI_certToList (by omega), hstep,
        by rw [getI_certToList (by omega)]; exact hT.accept_notMem⟩
    exact ⟨(Set.univ, T 0), ⟨rfl, hT.start_mem⟩, f, hf, hmtr⟩

/-- `a.toNAComplement` recognises the complement of the language of `a`. -/
theorem language_toNAComplement (a : TwoWayNA State Symbol) :
    Acceptor.language a.toNAComplement = (Acceptor.language a)ᶜ := by
  ext xs
  simp only [Acceptor.mem_language]
  exact accepts_toNAComplement_iff a xs

end TwoWayNA

/-! ## One-way automata as two-way automata -/

namespace NA.FinAcc

variable {n : NA.FinAcc State Symbol}

/-- The two-way automaton that performs the transitions of `n`, always moving its head one symbol
to the right. -/
def toTwoWayNA (n : NA.FinAcc State Symbol) : TwoWayNA State Symbol where
  Tr q x m q' := m = SignType.pos ∧ n.Tr q x q'
  start := n.start
  accept := n.accept

/-- A run of `n.toTwoWayNA` starting on `input` reads a multistep transition of `n` over the
prefix of `input` scanned so far. -/
theorem mTr_take_of_canReach {s : State} {c c' : TwoWayNACfg State Symbol}
    (hreach : (n.toTwoWayNA.toCfgNAFinAcc input).CanReach c c') (hc : c.input = input)
    (hmtr : n.MTr s (input.take c.pos) c.state) :
    c'.input = input ∧ n.MTr s (input.take c'.pos) c'.state := by
  obtain ⟨μs, hreach⟩ := hreach
  refine LTS.mtrInv_of_trInv
    (p := fun d => d.input = input ∧ n.MTr s (input.take d.pos) d.state) ?_ c μs c' hreach
    ⟨hc, hmtr⟩
  rintro d ⟨x, m⟩ d' hstep ⟨hd, hmtr⟩
  obtain ⟨hlt, rfl⟩ := TwoWayNA.getElem_of_tr hstep hd
  obtain ⟨hinput, -, ⟨rfl, htr⟩, hpos⟩ := hstep
  refine ⟨by rw [← hinput, hd], ?_⟩
  rw [show (d'.pos : ℕ) = (d.pos : ℕ) + 1 by simp at hpos; omega,
    List.take_succ_eq_append_getElem hlt]
  exact LTS.MTr.stepR _ hmtr htr

/-- A multistep transition of `n` over the part of `input` that starts at position `p` is read by
a run of `n.toTwoWayNA` taking its head from `p` to the end of the input. -/
theorem canReach_of_mTr {suf : List Symbol} {s s' : State} {p : ℕ}
    (hp : p < input.length + 1) (hdrop : input.drop p = suf) (hmtr : n.MTr s suf s') :
    (n.toTwoWayNA.toCfgNAFinAcc input).CanReach ⟨input, s, ⟨p, hp⟩⟩ ⟨input, s', Fin.last _⟩ := by
  induction suf generalizing s p with
  | nil =>
    rw [LTS.MTr.nil_iff] at hmtr
    subst hmtr
    obtain rfl : p = input.length := by grind [List.drop_eq_nil_iff]
    exact LTS.CanReach.refl _ _
  | cons x xs ih =>
    rw [LTS.MTr.cons_iff] at hmtr
    obtain ⟨t, htr, hmtr⟩ := hmtr
    have hlt : p < input.length := by
      by_contra hc
      grind [List.drop_eq_nil_iff]
    have hx : input[p]'hlt = x := by
      have h0 : (input.drop p)[0]? = some x := by rw [hdrop]; simp
      grind
    have hdrop' : input.drop (p + 1) = xs := by simp [← List.tail_drop, hdrop]
    have hstep : (n.toTwoWayNA.toCfgNAFinAcc input).Tr
        ⟨input, s, ⟨p, hp⟩⟩ (x, SignType.pos) ⟨input, t, ⟨p + 1, by omega⟩⟩ :=
      ⟨rfl, by rw [← hx]; simp, ⟨rfl, htr⟩, by simp⟩
    obtain ⟨μs, hmtr'⟩ := ih (by omega) hdrop' hmtr
    exact ⟨(x, SignType.pos) :: μs, LTS.MTr.cons_iff.mpr ⟨_, hstep, hmtr'⟩⟩

/-- A one-way automaton and its two-way rendering accept the same words. -/
theorem accepts_toTwoWayNA_iff (n : NA.FinAcc State Symbol) (input : List Symbol) :
    Acceptor.Accepts n.toTwoWayNA input ↔ Acceptor.Accepts n input := by
  constructor
  · rintro ⟨μs, c, ⟨hs, hpos, hinput⟩, c', ⟨hacc, hlast⟩, hmtr⟩
    have hstart : n.MTr c.state (input.take c.pos) c.state := by
      rw [hpos]
      simp
    obtain ⟨hinput', hmtr⟩ := mTr_take_of_canReach ⟨μs, hmtr⟩ hinput hstart
    rw [hlast, Fin.val_last, hinput', List.take_length] at hmtr
    exact ⟨c.state, hs, c'.state, hacc, hmtr⟩
  · rintro ⟨s, hs, s', hs', hmtr⟩
    obtain ⟨μs, hmtr⟩ :=
      canReach_of_mTr (suf := input) (by omega) List.drop_zero hmtr
    exact ⟨μs, ⟨input, s, ⟨0, by omega⟩⟩, ⟨hs, Fin.ext (by simp), rfl⟩,
      ⟨input, s', Fin.last _⟩, ⟨hs', rfl⟩, hmtr⟩

/-- A one-way automaton and its two-way rendering recognise the same language. -/
theorem language_toTwoWayNA (n : NA.FinAcc State Symbol) :
    Acceptor.language n.toTwoWayNA = Acceptor.language n := by
  ext xs
  simp only [Acceptor.mem_language]
  exact accepts_toTwoWayNA_iff n xs

end NA.FinAcc

end Cslib.Automata

namespace Cslib.Language

open Automata Acceptor

/-- A language is regular if and only if it is accepted by some two-way nondeterministic
automaton with finitely many states. -/
theorem IsRegular.iff_twoWayNA {Symbol : Type*} {l : Language Symbol} :
    l.IsRegular ↔ ∃ State : Type, ∃ _ : Finite State,
      ∃ a : Automata.TwoWayNA State Symbol, language a = l := by
  constructor
  · intro h
    rw [IsRegular.iff_nfa] at h
    obtain ⟨State, hfin, na, rfl⟩ := h
    exact ⟨State, hfin, na.toTwoWayNA, na.language_toTwoWayNA⟩
  · rintro ⟨State, hfin, a, rfl⟩
    have := hfin
    have hc : (language a)ᶜ.IsRegular := by
      rw [IsRegular.iff_nfa]
      exact ⟨Set State × Set State, inferInstance, a.toNAComplement, a.language_toNAComplement⟩
    simpa using hc.compl

end Cslib.Language
