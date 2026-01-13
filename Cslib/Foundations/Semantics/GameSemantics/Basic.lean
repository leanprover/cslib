/-
Copyright (c) 2026 Bashar Hamade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bashar Hamade
-/

import Cslib.Foundations.Semantics.LTS.Basic

/-!
# Reachability Games

This module formalizes reachability games, a fundamental concept in game theory with
applications in formal verification, concurrency theory, and logic.

A reachability game is played on a graph (represented as an LTS) between two players:
- **Defender** (also called Player 0), who wins if the play reaches a designated target set
- **Attacker** (also called Player 1), who tries to avoid the target set forever

These games are particularly useful for specifying and verifying properties of concurrent
systems, such as safety and liveness properties.

## Main definitions

- `ReachabilityGame` is a structure defining the game graph, consisting of positions,
  transition labels, a target set of positions for the Defender, an LTS representing
  possible moves, and an initial position.

- `Attacker` is the set of positions belonging to the Attacker (complement of the Defender's
  target set).

- `step` formalizes the existence of a valid move between two positions.

- `Play` is a structure representing a (potentially infinite) play in the game, with
  fields ensuring the play starts at the initial position and follows valid transitions.

- `DefenderWins` and `AttackerWins` define winning conditions for the respective players.

- `AttackerStrategy` and `DefenderStrategy` represent deterministic strategies for each player.

- `AttackerWinsFromPos` and `AttackerWinRegion` define the set of positions from which
  the Attacker can force a win.

## Main statements

- `disjoint_Gd_Attacker`: The Defender's target set and the Attacker positions are disjoint.

- `union_Gd_Attacker`: Every position is either in the Defender's target set or belongs to
  the Attacker.

- `finite_or_infinite`: Every play is either finite or infinite.

- `not_both_finite_infinite`: A play cannot be both finite and infinite.

- `Defender_or_Attacker_win`: Exactly one player wins each play.

- `AttackerStrategy.isDeterministic` and `DefenderStrategy.isDeterministic`:
  Characterizations of deterministic strategies.

## References

  * [B. Bisping, D. N. Jansen, and U. Nestmann,
  *Deciding All Behavioral Equivalences at Once:
  A Game for Linear-Time–Branching-Time Spectroscopy*][BispingEtAl2022]

-/

namespace Cslib

universe u v

/--
A ReachabilityGame consists of:
- `Label`: The type of transition labels
- `Pos`: The type of positions in the game graph
- `G_d`: The set of positions designated as the Defender's target set
- `GameMoves`: An LTS defining the valid moves in the game
- `g_0`: The initial position of the game

The game is played between a Defender (who tries to reach `G_d`) and an Attacker
(who tries to avoid `G_d` forever).
-/
structure ReachabilityGame where
  /-- The type of transition labels. -/
  Label : Type v
  /-- The type of positions in the game graph. -/
  Pos : Type u
  /-- The set of positions constituting the Defender's target set. -/
  G_d : Set Pos
  /-- The labelled transition system defining valid moves. -/
  GameMoves : LTS Pos Label
  /-- The initial position of the game. -/
  g_0 : Pos

namespace ReachabilityGame

variable {G : ReachabilityGame}

/--
The set of positions belonging to the Attacker.
A position belongs to the Attacker if it is not in the Defender's target set `G_d`.
-/
def Attacker : Set G.Pos := { p : G.Pos | ¬G.G_d p }

/-- The Defender's target set and the Attacker positions are disjoint. -/
theorem disjoint_Gd_Attacker : G.G_d ∩ G.Attacker = ∅ := by
  ext x; simp [Attacker]
  intro x_in_Gd
  trivial

/-- Every position is either in the Defender's target set or belongs to the Attacker. -/
theorem union_Gd_Attacker : G.G_d ∪ G.Attacker = Set.univ := by
  ext x; simp [Attacker]; apply Classical.em

/--
A step exists from position `p` to position `p'` if there is a transition
in the game LTS from `p` to `p'` with some label.
-/
def step (p p' : G.Pos) : Prop := ∃ (l : G.Label), G.GameMoves.Tr p l p'

/-!
## Plays

This section defines plays, which are (potentially infinite) sequences of positions
in a reachability game.
-/

/--
A Play is a (potentially infinite) sequence of positions in the game.

A play consists of:
- `π`: A partial function from natural numbers to positions, representing the
  position at each step of the play
- `start_eq_initial`: The play must start at the initial position `g_0`
- `continuous`: If a position exists at step n+1, then a position must exist at step n
- `coherent`: If a position exists at step n, all earlier positions must exist
- `is_path`: The sequence must follow valid transitions in the game
-/
structure Play where
  /-- Position at index i (partial function). -/
  π : ℕ → Option G.Pos
  /-- First position exists and equals `g_0`. -/
  start_eq_initial : π 0 = some G.g_0
  /-- Continuity: if position n+1 exists, then position n must exist. -/
  continuous : ∀ n, π (n + 1) ≠ none → π n ≠ none
  /-- Coherent: if position n exists, all earlier positions exist. -/
  coherent : ∀ n m, m < n → π n ≠ none → π m ≠ none
  /-- Path property: valid transitions between consecutive positions. -/
  is_path : ∀ n p p', π n = some p → π (n + 1) = some p' → step p p'

namespace Play


open Classical in
/--
The length of a finite play, or `none` if the play is infinite.
If the play terminates (some `π n = none`), returns `some (Nat.find h - 1)`,
which is the last index where a position exists.
-/
noncomputable def len (play : @Play G) : Option ℕ :=
  if h : ∃ n, play.π n = none
  then some (Nat.find h - 1)
  else none

/-!
### Finite and Infinite Plays

This section defines properties for classifying plays as finite or infinite.
-/

/-- A play is finite if there exists a position at step n but no position at step n+1. -/
def isFinite (play : @Play G) : Prop := ∃ n, play.π n ≠ none ∧ play.π (n + 1) = none

/-- A play is infinite if for every n, whenever a position exists at step n,
a position also exists at step n+1. -/
def isInfinite (play : @Play G) : Prop := ∀ n, play.π n ≠ none → play.π (n + 1) ≠ none

/-- The initial position π 0 always exists (never none). -/
lemma π_zero_not_none (play : @Play G) : play.π 0 ≠ none := by
  rw [play.start_eq_initial]
  simp

/-- Every play is either finite or infinite. -/
theorem finite_or_infinite (play : @Play G) : play.isFinite ∨ play.isInfinite := by
  by_cases h : ∃ n, play.π n = none
  · -- Case: There exists some n where π n = none
    left
    unfold isFinite
    -- Use Nat.find to get the minimal such n
    let n := Nat.find h
    have hn : play.π n = none := Nat.find_spec h
     -- Show that n > 0 (because π 0 ≠ none)
    have n_pos : n > 0 := by
      by_contra h_neg
      simp at h_neg
      have : play.π 0 = none := by rwa [h_neg] at hn
      exact π_zero_not_none play this
    -- So n - 1 exists and is a natural number
    use (n - 1)
    constructor
    · -- Show π (n-1) ≠ none
      have : n - 1 < n := by
        simp
        trivial
      exact Nat.find_min h this
    · -- Show π n = none (which equals π ((n-1)+1) when n > 0)
      have : n = (n - 1) + 1 := by omega
      rwa [← this]
  · -- Case: For all n, π n ≠ none
    right
    unfold isInfinite
    push_neg at h
    exact fun n _ => h (n + 1)

/-- A play cannot be both finite and infinite (these properties are mutually exclusive). -/
theorem not_both_finite_infinite (play : @Play G) : ¬(play.isFinite ∧ play.isInfinite) := by
  intro ⟨hfin, hinf⟩
  obtain ⟨n, hn_not_none, hn1_none⟩ := hfin
  have : play.π (n + 1) ≠ none := hinf n hn_not_none
  contradiction


open Classical in
/-- For a finite play, returns the index of the first `none` value in π. -/
def final_pos_index (play : @Play G) (h : play.isFinite) : ℕ :=
  -- Convert isFinite to the existential Nat.find expects
  let h' : ∃ n, play.π n = none := by
    obtain ⟨n, _, hn1⟩ := h
    exact ⟨n + 1, hn1⟩
  Nat.find h'

/-!
### Winning Conditions

This section defines winning conditions for the Defender and Attacker.
-/

/--
The Defender wins a play if either:
1. The play is infinite (Attacker cannot force termination), or
2. The play is finite and ends in a position belonging to `G_d` (the Defender's target set)
-/
def DefenderWins (play : @Play G) : Prop :=
  play.isInfinite ∨ (∃ h : play.isFinite,
    ∃ p, play.π (final_pos_index play h - 1) = some p ∧ p ∈ G.G_d)


/-- The Attacker wins a play if the Defender does not win. -/
def AttackerWins (play : @Play G) : Prop :=
  ¬ (DefenderWins play)

/-- Exactly one player wins each play (excluded middle for winning conditions). -/
theorem Defender_or_Attacker_win (play : @Play G) : DefenderWins play ∨ AttackerWins play := by
  have fin_or_infin := finite_or_infinite play
  cases fin_or_infin with
  | inl hfin =>
    -- Finite case
    by_cases h : ∃ p, play.π (final_pos_index play hfin - 1) = some p ∧ p ∈ G.G_d
    · -- Defender wins
      left
      right
      exact ⟨hfin, h⟩
    · -- Attacker wins
      right
      unfold AttackerWins DefenderWins
      push_neg
      constructor
      · unfold isInfinite
        push_neg
        exact hfin
      · intro h_fin p exists_some_p
        push_neg at h
        specialize h p
        apply h
        trivial
  | inr hinf =>
    -- Infinite case: Defender wins
    left
    left
    exact hinf


/-!
### Strategies

This section defines strategies for the Attacker and Defender players.
-/

/--
An AttackerStrategy is a function that, given an Attacker position `g` and proof that
`g` belongs to the Attacker, returns a next position `g'` along with a proof that
`step g g'` holds (i.e., there is a valid move from `g` to `g'`).
-/
def AttackerStrategy :=
  (g : G.Pos) → g ∈ Attacker → { g' : G.Pos // G.step g g' }

/--
A DefenderStrategy is a function that, given a Defender position `g` (i.e., `g ∈ G_d`)
and proof that `g` belongs to the Defender's target set, returns a next position `g'`
along with a proof that `step g g'` holds.
-/
def DefenderStrategy :=
  (g : G.Pos) → g ∈ G.G_d → { g' : G.Pos // G.step g g' }

/-!
#### Deterministic Strategies

This section characterizes when strategies are deterministic.
-/

/-- An AttackerStrategy is deterministic if it always selects the same next position
for the same input position (i.e., it is a function, not a relation). -/
def AttackerStrategy.isDeterministic (strategy : @AttackerStrategy G) : Prop :=
  ∀ (g : G.Pos) (hg : g ∈ Attacker),
    ∀ (g1 g2 : { g' : G.Pos // step g g' }),
    strategy g hg = g1 → strategy g hg = g2 → g1.val = g2.val


/-- A DefenderStrategy is deterministic if it always selects the same next position
for the same input position (i.e., it is a function, not a relation). -/
def DefenderStrategy.isDeterministic (strategy : @DefenderStrategy G) : Prop :=
  ∀ (g : G.Pos) (hg : g ∈ G.G_d),
    ∀ (g1 g2 : { g' : G.Pos // step g g' }),
    strategy g hg = g1 → strategy g hg = g2 → g1.val = g2.val

/--
A play follows an AttackerStrategy if, whenever the play is at an Attacker position,
the next position is the one prescribed by the strategy.
-/
def followsAttackerStrategy (play : @Play G) (σ : @AttackerStrategy G) : Prop :=
  ∀ n p, play.π n = some p →
    (hg : p ∈ Attacker) →
    play.π (n + 1) = some (σ p hg).val

/-!
### Winning Regions

This section defines the set of positions from which the Attacker can force a win.
-/

/--
AttackerWinsFromPos pos means the Attacker has a strategy that guarantees winning
from position `pos`, no matter how the Defender responds.
-/
def AttackerWinsFromPos (pos : G.Pos) : Prop :=
  ∃ (strategy : @AttackerStrategy G),
    ∀ (play : @Play G),
      play.π 0 = some pos →
      play.followsAttackerStrategy strategy →
      play.AttackerWins

/--
The AttackerWinRegion is the set of Attacker positions from which the Attacker
can force a win (i.e., positions in the winning region for the Attacker).
-/
def AttackerWinRegion : Set G.Pos :=
  { g : G.Pos | g ∈ Attacker ∧ AttackerWinsFromPos g }

end Play

end ReachabilityGame

end Cslib
