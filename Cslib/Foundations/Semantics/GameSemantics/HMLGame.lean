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

variable {State : Type u} {Label : Type v}

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


def defenderWinsHML (lts : LTS State Label) : State → Formula Label → Prop
  | _, .true => True
  | _, .false => False
  | p, .modal a φ => ∃ p', lts.Tr p a p' ∧ defenderWinsHML lts p' φ
  | p, .conj φs => ∀ φ ∈ φs, defenderWinsHML lts p φ
  | p, .neg φ => ¬defenderWinsHML lts p φ


theorem game_semantics_correct (lts : LTS State Label) (p : State) (φ : Formula Label) :
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
