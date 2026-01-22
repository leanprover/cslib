import Cslib.Foundations.Semantics.GameSemantics.Basic
import Cslib.Foundations.Semantics.GameSemantics.HMLGame

namespace CslibTests

open Cslib
open Cslib.HennessyMilner
open Cslib.HMLGame

/-!
## Example 2.9 from Bisping et al.

Testing that ⟦⟨a⟩¬⟨d⟩⊤⟧^CCS_{P₂} is false.
-/

/-- Actions for the CCS processes -/
inductive Action where
  | a : Action
  | b : Action
  | c : Action
  | d : Action
  deriving DecidableEq, Repr

/-- States for process P₁ -/
inductive StateP1 where
  | P1 : StateP1       -- Initial state
  | bc : StateP1       -- b + c
  | d : StateP1        -- d
  | zero : StateP1     -- 0 (terminated)
  deriving DecidableEq, Repr

/-- States for process P₂ -/
inductive StateP2 where
  | P2 : StateP2       -- Initial state
  | bd : StateP2       -- b + d
  | cd : StateP2       -- c + d
  | zero : StateP2     -- 0 (terminated)
  deriving DecidableEq, Repr

/-- Transition relation for P₁ -/
inductive TrP1 : StateP1 → Action → StateP1 → Prop where
  | p1_a_bc : TrP1 .P1 .a .bc
  | p1_a_d  : TrP1 .P1 .a .d
  | bc_b_0  : TrP1 .bc .b .zero
  | bc_c_0  : TrP1 .bc .c .zero
  | d_d_0   : TrP1 .d  .d .zero

/-- Transition relation for P₂ -/
inductive TrP2 : StateP2 → Action → StateP2 → Prop where
  | p2_a_bd : TrP2 .P2 .a .bd
  | p2_a_cd : TrP2 .P2 .a .cd
  | bd_b_0  : TrP2 .bd .b .zero
  | bd_d_0  : TrP2 .bd .d .zero
  | cd_c_0  : TrP2 .cd .c .zero
  | cd_d_0  : TrP2 .cd .d .zero

/-- LTS for process P₁ -/
def ltsP1 : LTS StateP1 Action := ⟨TrP1⟩

/-- LTS for process P₂ -/
def ltsP2 : LTS StateP2 Action := ⟨TrP2⟩

/-!
### Formula: ⟨a⟩¬⟨d⟩⊤

This formula says: "there exists an a-transition to a state where
there is no d-transition to any state satisfying ⊤"

Since ⊤ is always true, ¬⟨d⟩⊤ means "there is no d-transition".
-/

/-- The formula ⊤ (empty conjunction) -/
def formulaTrue : Formula Action := .conj []

/-- The formula ⟨d⟩⊤ -/
def formulaDiamondD : Formula Action := .modal .d formulaTrue

/-- The formula ¬⟨d⟩⊤ -/
def formulaNegDiamondD : Formula Action := .neg formulaDiamondD

/-- The formula ⟨a⟩¬⟨d⟩⊤ -/
def formulaExample : Formula Action := .modal .a formulaNegDiamondD

/-!
### Example 2.9: ⟦⟨a⟩¬⟨d⟩⊤⟧^CCS_{P₂} is false

From P₂, the defender can move via 'a' to either (b+d) or (c+d).
In both cases, there IS a d-transition to 0, so ¬⟨d⟩⊤ is false.
Therefore ⟨a⟩¬⟨d⟩⊤ is false at P₂.
-/

/-- Helper: 0 satisfies ⊤ -/
theorem zero_satisfies_true : satisfies ltsP2 .zero formulaTrue := by
  simp [formulaTrue, satisfies]

/-- Helper: b+d has a d-transition -/
theorem bd_has_d_transition : ltsP2.Tr .bd .d .zero := TrP2.bd_d_0

/-- Helper: c+d has a d-transition -/
theorem cd_has_d_transition : ltsP2.Tr .cd .d .zero := TrP2.cd_d_0

/-- Helper: b+d satisfies ⟨d⟩⊤ -/
theorem bd_satisfies_diamondD : satisfies ltsP2 .bd formulaDiamondD := by
  simp only [formulaDiamondD, formulaTrue, satisfies]
  simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exists .zero
  constructor


/-- Helper: c+d satisfies ⟨d⟩⊤ -/
theorem cd_satisfies_diamondD : satisfies ltsP2 .cd formulaDiamondD := by
  simp only [formulaDiamondD, formulaTrue, satisfies, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true]
  exact ⟨.zero, by constructor⟩

/-- Helper: b+d does NOT satisfy ¬⟨d⟩⊤ -/
theorem bd_not_satisfies_negDiamondD : ¬ satisfies ltsP2 .bd formulaNegDiamondD := by
  simp only [formulaNegDiamondD, satisfies, not_not]
  exact bd_satisfies_diamondD

/-- Helper: c+d does NOT satisfy ¬⟨d⟩⊤ -/
theorem cd_not_satisfies_negDiamondD : ¬ satisfies ltsP2 .cd formulaNegDiamondD := by
  simp only [formulaNegDiamondD, satisfies, not_not]
  exact cd_satisfies_diamondD

/--
Example 2.9: P₂ does NOT satisfy ⟨a⟩¬⟨d⟩⊤

The defender cannot win because both a-successors (b+d and c+d)
have d-transitions, so ¬⟨d⟩⊤ fails at both.
-/
theorem example_2_9 : ¬ satisfies ltsP2 .P2 formulaExample := by
  simp only [formulaExample, formulaNegDiamondD, formulaDiamondD, formulaTrue, satisfies]
  intro ⟨p', h_tr, h_neg⟩
  -- p' must be either bd or cd (the only a-successors of P2)
  cases h_tr with
  | p2_a_bd =>
    -- p' = bd, but bd has a d-transition to zero
    apply h_neg
    simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
    exact ⟨.zero, by constructor⟩
  | p2_a_cd =>
    -- p' = cd, but cd has a d-transition to zero
    apply h_neg
    simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
    exact ⟨.zero,  by constructor⟩

/--
Using the game semantics theorem to show the same result:
The defender does NOT win G^S_HML[(P₂, ⟨a⟩¬⟨d⟩⊤)]
-/
theorem example_2_9_game : ¬ defenderWinsHML ltsP2 .P2 formulaExample := by
  rw [game_semantics_soundness]
  exact example_2_9


end CslibTests
