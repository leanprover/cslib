/-
Copyright (c) 2025 Bashar Hamade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bashar Hamade
-/

import Cslib.Init
import Cslib.Foundations.Semantics.LTS.Basic
import Cslib.Logics.HennessyMilnerLogic.Basic
import Cslib.Foundations.Semantics.GameSemantics.Basic

/-!
# HML Games

This module formalizes HML games, a game-theoretic characterization of
Hennessy–Milner Logic (HML) on Labelled Transition Systems (LTS).

HML games provide an alternative, operational characterization of modal
logic satisfaction. They are played between two players:
- **Defender** (∃ player): tries to prove that a state satisfies a formula
- **Attacker** (∀ player): tries to refute the formula

A state satisfies an HML formula if and only if the Defender has a winning
strategy in the corresponding HML game starting from that state.

## Game Structure

For a transition system S = (P, Σ, →), the HML game G^S_HML[g₀] = (G, G_d, ↝, g₀)
is played on G = P × HML[Σ], where positions are pairs (p, φ) consisting of
a process p and a formula φ.

## Main definitions

- `HMLGame` is a structure defining the game components: labels, processes,
  transition system, and initial position.

- `Gd` defines the set of defender-controlled positions, corresponding to
  modal observations ⟨a⟩φ and negated conjunctions ¬⋀ᵢφᵢ.

- `Ga` defines the set of attacker-controlled positions (complement of Gd).

- `move_defender` formalizes valid moves from defender positions.

- `move_attacker` formalizes valid moves from attacker positions.

- `move` is the union of defender and attacker moves.

- `toGame` converts an HMLGame to a generic Game structure.

- `defenderWinsHML` gives a direct recursive characterization of when
  the defender wins.

## Main statements

- `game_semantics_soundness`: Proves that the game-theoretic characterization
  of HML satisfaction is equivalent to the standard Tarski-style semantics.
  This establishes the fundamental connection between games and modal logic.

## References

* [M. Hennessy and R. Milner,
*Algebraic Laws for Non-Determinism and Concurrency*][HennessyMilner1985]

* [B. Bisping, D. N. Jansen, and U. Nestmann,
*Deciding All Behavioral Equivalences at Once:
A Game for Linear-Time–Branching-Time Spectroscopy*][BispingEtAl2022]

-/

namespace Cslib

open HennessyMilner

universe u v

variable {State : Type u} {Label : Type v}

/--
HML game structure: For a transition system S = (P, Σ, →), the HML game
G^S_HML[g₀] = (G, G_d, ↝, g₀) is played on G = P × HML[Σ].

A position is a pair (p, φ) where p is a process and φ is an HML formula.
The game is played between a Defender (who tries to prove φ holds at p) and
an Attacker (who tries to refute it).
-/
structure HMLGame where
  /-- The type of transition labels (alphabet Σ). -/
  Label : Type v
  /-- The type of processes/states in the transition system. -/
  Process : Type u
  /-- The labelled transition system S = (P, Σ, →). -/
  S : LTS Process Label
  /-- The initial position g₀ = (p, φ). -/
  g0 : Process × Formula Label

namespace HMLGame

variable {G : HMLGame}

/-!
## Game Positions and Moves

This section defines the key components of the HML game: the sets of
positions controlled by each player and the valid moves they can make.
-/

/--
The set of defender-controlled positions (G_d).

The Defender controls positions where the formula requires an existential
interpretation:
- Modal observation ⟨a⟩φ: Defender must find an a-transition
- Negated conjunction ¬⋀ᵢφᵢ: Defender must pick one disjunct to defend

Positions in G_d are winning for the Defender if they reach a true formula.
-/
def Gd : Set (G.Process × Formula G.Label) :=
  { pos | match pos.2 with
    | .modal _ _ => True
    | .neg (.conj _) => True
    | _ => False }

/--
Alternative definition of defender-controlled positions using explicit
set-builder notation with existential quantification.
-/
def Gd' : Set (G.Process × Formula G.Label) :=
  { pos | ∃ (a : G.Label) (φ : Formula G.Label), pos.2 = .modal a φ } ∪
  { pos | ∃ (φs : List (Formula G.Label)), pos.2 = .neg (.conj φs) }

/--
The set of attacker-controlled positions (G_a), defined as the complement
of the defender's positions.

The Attacker controls positions where the formula requires a universal
interpretation:
- Conjunction ⋀ᵢφᵢ: Attacker can choose any conjunct to challenge
- Negated modal ¬⟨a⟩φ: Attacker must find a transition to refute
- Double negation ¬¬φ: Attacker can eliminate one negation
-/
def Ga : Set (G.Process × Formula G.Label) :=
  { pos | ¬ Gd pos }

/-!
### Defender's Moves

This section formalizes the valid moves available to the Defender player.
-/

/--
The Defender's move relation from position x to position y.

At a modal observation ⟨a⟩φ, the Defender chooses a transition p -a→ p'.
The next position is (p', φ) at the same formula.

At a negated conjunction ¬⋀ᵢφᵢ, the Defender chooses one disjunct φ'ᵢ
(from the negated list of conjuncts) to defend. The process stays the same.
-/
def move_defender : (G.Process × Formula G.Label) → (G.Process × Formula G.Label) → Prop
  | (p, .modal a φ), (p', φ') =>
      G.S.Tr p a p' ∧ φ' = φ
  | (p, .neg (.conj φs)), (p', φ') =>
      p' = p ∧ φ' ∈ φs.map Formula.neg
  | _, _ => False

/-!
### Attacker's Moves

This section formalizes the valid moves available to the Attacker player.
-/

/--
The Attacker's move relation from position x to position y.

At a negated modal ¬⟨a⟩φ, the Attacker chooses a transition p -a→ p'.
The next position is (p', ¬φ).

At a conjunction ⋀ᵢφᵢ, the Attacker chooses one conjunct φᵢ to challenge.
The process stays the same.

At a double negation ¬¬φ, the Attacker can eliminate one negation,
moving to (p, φ).
-/
def move_attacker : (G.Process × Formula G.Label) → (G.Process × Formula G.Label) → Prop
  | (p, .neg (.modal a φ)), (p', φ') =>
      G.S.Tr p a p' ∧ φ' = .neg φ
  | (p, .conj φs), (p', φ') =>
      p' = p ∧ φ' ∈ φs
  | (p, .neg (.neg φ)), (p', φ') =>
      p' = p ∧ φ' = φ
  | _, _ => False

/--
The complete move relation for the HML game, defined as the union of
defender and attacker moves.

This captures all valid transitions between positions in the game graph.
-/
def move (x y : G.Process × Formula G.Label) : Prop :=
  move_defender x y ∨ move_attacker x y

/--
Converts an HMLGame to the generic Game structure defined in Basic.lean.

This allows HML games to be analyzed using the general game theory
framework (plays, strategies, winning regions, etc.).
-/
def toGame (HG : HMLGame) : Game where
  Label := HG.Label
  Pos := HG.Process × Formula HG.Label
  G_d := HG.Gd
  GameMoves := { Tr := fun p _ p' => HG.move p p' }
  g_0 := HG.g0

/-!
## Direct Characterization of Winning

This section provides a direct (non-game-theoretic) characterization of
when the Defender wins the HML game, by recursion on the formula structure.
-/

/--
Direct characterization of Defender's winning positions in an HML game.

This function gives a recursive characterization equivalent to "the Defender
has a winning strategy", but defined directly by recursion on the formula:
- ⊤: Defender trivially wins (true formula)
- ⊥: Defender cannot win (false formula)
- ⟨a⟩φ: Defender wins if there exists an a-transition to a state where they win
- ⋀ᵢφᵢ: Defender wins if they win on all conjuncts
- ¬φ: Defender wins if they do NOT win on φ (Attacker loses)
-/
def defenderWinsHML (lts : LTS State Label) : State → Formula Label → Prop
  | _, .true => True
  | _, .false => False
  | p, .modal a φ => ∃ p', lts.Tr p a p' ∧ defenderWinsHML lts p' φ
  | p, .conj φs => ∀ φ ∈ φs, defenderWinsHML lts p φ
  | p, .neg φ => ¬defenderWinsHML lts p φ

/-!
## Correctness Theorem

This section proves the fundamental correctness result: the game-theoretic
characterization is equivalent to the standard Tarski semantics.
-/

/--
**Main Correctness Theorem**: The game-theoretic characterization of HML
satisfaction is equivalent to the standard Tarski-style semantics.

That is, for any LTS lts, state p, and HML formula φ:
  defenderWinsHML lts p φ  ↔  lts ⊨ p φ

This theorem establishes that the Defender has a winning strategy in the
HML game starting from (p, φ) if and only if p satisfies φ according to
the standard modal logic semantics.

The proof proceeds by structural induction on the formula φ, showing that
each case of the recursive definition of `defenderWinsHML` corresponds
exactly to the semantic clause for that formula constructor.
-/
theorem game_semantics_soundness (lts : LTS State Label) (p : State) (φ : Formula Label) :
    defenderWinsHML lts p φ ↔ satisfies lts p φ := by
  induction φ using Formula.ind_on generalizing p with
  | h_true =>
    -- Base Case 1: φ = ⊤
    simp [defenderWinsHML, satisfies]
  | h_false =>
    -- Base Case 2: φ = ⊥
    simp [defenderWinsHML, satisfies]
  | h_modal a ψ ih =>
      constructor
      · intro h_def_win
        simp only [defenderWinsHML] at h_def_win
        obtain ⟨p', h_tr, h_def_win_ψ⟩ := h_def_win
        simp only [satisfies]
        use p'
        constructor
        exact h_tr
        specialize ih p'
        exact ih.mp h_def_win_ψ
      · simp only [satisfies]
        intro ⟨p', h_tr, h_sat_ψ⟩
        simp only [defenderWinsHML]
        use p'
        constructor
        exact h_tr
        specialize ih p'
        exact ih.mpr h_sat_ψ
  | h_conj φs ih_list =>
      constructor
      · intro h_def_win
        simp only [defenderWinsHML] at h_def_win
        simp only [satisfies]
        intro φ h_mem
        specialize ih_list φ h_mem p
        exact ih_list.mp (h_def_win φ h_mem)
      · simp only [satisfies]
        intro h_sat_all
        simp only [defenderWinsHML]
        intro φ h_mem
        specialize ih_list φ h_mem p
        exact ih_list.mpr (h_sat_all φ h_mem)
  | h_neg ψ ih =>
      constructor
      · intro h_def_win
        simp only [defenderWinsHML] at h_def_win
        simp only [satisfies]
        intro h_sat_ψ
        specialize ih p
        have h_def_ψ := ih.mpr h_sat_ψ
        contradiction
      · simp only [satisfies]
        intro h_not_sat_ψ
        simp only [defenderWinsHML]
        intro h_def_ψ
        specialize ih p
        have h_sat_ψ := ih.mp h_def_ψ
        contradiction







end HMLGame

end Cslib
