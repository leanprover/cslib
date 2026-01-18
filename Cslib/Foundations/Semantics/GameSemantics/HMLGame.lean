/-
Copyright (c) 2026 Bashar Hamade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bashar Hamade
-/

import Cslib.Foundations.Semantics.LTS.Basic
import Cslib.Logics.HennessyMilnerLogic.Basic

import Cslib.Foundations.Semantics.GameSemantics.Basic

namespace Cslib

open HennessyMilner

universe u v

/--
Definition 2.7 (HML game):
For a transition system S = (P, Σ, →), the HML game G^S_HML[g₀] = (G, G_d, ↝, g₀)
is played on G = P × HML[Σ].
-/
structure HMLGame where
  /-- The type of transition labels. -/
  Label : Type v

  /-- The type of processes/states. -/
  Process : Type u

  /-- The transition system S. -/
  S : LTS Process Label

  /-- The initial position g₀ = (p, φ). -/
  g0 : Process × Formula Label

namespace HMLGame

variable {G : HMLGame}

/--
The set of defender-controlled positions.
Defender controls positions where the formula is either:
- A modal observation ⟨a⟩φ
- A negated conjunction ¬⋀ᵢφᵢ
-/
def Gd : Set (G.Process × Formula G.Label) :=
  { pos | match pos.2 with
    | .modal _ _ => True
    | .neg (.conj _) => True
    | _ => False }

/--
Alternative definition using explicit pattern matching.
-/
def Gd' : Set (G.Process × Formula G.Label) :=
  { pos | ∃ (a : G.Label) (φ : Formula G.Label), pos.2 = .modal a φ } ∪
  { pos | ∃ (φs : List (Formula G.Label)), pos.2 = .neg (.conj φs) }

/-- The set of attacker-controlled positions (complement of Gd). -/
def Ga : Set (G.Process × Formula G.Label) :=
  { pos | ¬ Gd pos }

/--
The defender's moves.
-/
def move_defender : (G.Process × Formula G.Label) → (G.Process × Formula G.Label) → Prop
  | (p, .modal a φ), (p', φ') =>
      -- Defender chooses: pick an a-transition from p to p'
      G.S.Tr p a p' ∧ φ' = φ
  | (p, .neg (.conj φs)), (p', φ') =>
      -- Defender chooses: pick some i ∈ I
      p' = p ∧ φ' ∈ φs.map Formula.neg
  | _, _ => False

/--
The attacker's moves.
-/
def move_attacker : (G.Process × Formula G.Label) → (G.Process × Formula G.Label) → Prop
  | (p, .neg (.modal a φ)), (p', φ') =>
      -- Attacker chooses: pick an a-transition from p to p'
      G.S.Tr p a p' ∧ φ' = .neg φ
  | (p, .conj φs), (p', φ') =>
      -- Attacker chooses: pick some i ∈ I
      p' = p ∧ φ' ∈ φs
  | (p, .neg (.neg φ)), (p', φ') =>
      -- Attacker moves: double negation elimination
      p' = p ∧ φ' = φ
  | _, _ => False

/--
The move relation for the HML game (Definition 2.7).
This is the union of defender and attacker moves.
-/
def move (x y : G.Process × Formula G.Label) : Prop :=
  move_defender x y ∨ move_attacker x y


def toGame (HG : HMLGame) : Game where
  Label := HG.Label
  Pos := HG.Process × Formula HG.Label
  G_d := HG.Gd
  GameMoves := { Tr := fun p _ p' => HG.move p p' }
  g_0 := HG.g0


/--
Definition 2.8: p ⊨ φ iff Attacker wins G_HML^S[(p,φ)].
The Attacker winning means the formula is satisfied.
-/
def attackerWinsHML (G : HMLGame) : Prop :=
  @Game.Play.AttackerWinsFromPos G.toGame G.g0

/--
The Defender wins G_HML^S[(p,φ)] iff p ⊭ φ.
-/
def defenderWinsHML (G : HMLGame) : Prop :=
  @Game.Play.DefenderWinsFromPos G.toGame G.g0



end HMLGame

end Cslib
