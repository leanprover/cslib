/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Logics.LTL.Basic
import Cslib.Logics.Modal.Denotation

namespace Cslib.Logic.Modal.LTL

open scoped InferenceSystem Modal.Proposition Modal.Satisfies

-- States differ from their positions, so interpreting atoms on positions would fail these tests.
private def trace : ωSequence ℕ := ⟨fun n => n + 10⟩
private def model : Model ℕ (StateAtom ℕ) where
  seq := trace
  v s P := P s

private def before : Proposition (StateAtom ℕ) := .atom (· < 12)
private def reached : Proposition (StateAtom ℕ) := .atom (· = 12)
private def later : Proposition (StateAtom ℕ) := .atom (fun s => 12 ≤ s)

-- Raw auxiliary modalities cannot be passed to the LTL judgement.
private def rawBetween : RawProposition (StateAtom ℕ) := d[Operator.between]⊥

#guard_msgs (drop info) in
#check_failure LTL[model ⊨ rawBetween]

example : ⇓LTL[model ⊨ before] := by
  change 10 < 12
  omega

-- Predicate atoms are coerced into the standard fragment automatically.
example : ⇓LTL[model,2 ⊨ (fun s : ℕ => s = 12)] := by
  rfl

-- Boolean connectives preserve the fragment and use the generic modal semantics.
example : ⇓LTL[model ⊨ (before ∧ ¬reached) ∨ ⊥] := by
  rw [Satisfies.at_or_iff model 0 (before ∧ ¬reached) ⊥]
  left
  rw [Satisfies.at_and_iff model 0 before (¬reached),
    Satisfies.at_not_iff model 0 reached]
  constructor
  · change 10 < 12
    omega
  · change ¬(10 = 12)
    omega

example : ⇓LTL[model ⊨ ((before ∧ ¬reached) → before) ↔ ⊤] := by
  rw [Satisfies.at_iff_iff model 0 ((before ∧ ¬reached) → before) ⊤,
    Satisfies.at_imp_iff model 0 (before ∧ ¬reached) before]
  constructor
  · intro _
    exact Modal.Satisfies.true
  · intro _ h
    exact (Satisfies.at_and_iff model 0 before (¬reached)).mp h |>.1

example : ⇓LTL[model,1 ⊨ X reached] := by
  rw [Satisfies.at_next_iff]
  rfl

-- The position API uses the sequence state and hides the interval anchor at nonzero positions.
example : ⇓LTL[model,1 ⊨ before U reached] := by
  rw [Satisfies.at_until_iff model 1 before reached]
  refine ⟨2, by omega, rfl, ?_⟩
  intro j _ hj
  change j + 10 < 12
  omega

-- Until includes the current position and excludes its witness from the left operand's interval.
example : ⇓Modal[(Model.ofTracePredicates trace).toModal,⟨0, 7⟩ ⊨ before U reached] := by
  rw [Satisfies.until_iff (Model.ofTracePredicates trace) 0 7 before reached]
  refine ⟨2, by omega, ?_, ?_⟩
  · rfl
  · intro j _ hj
    change j + 10 < 12
    omega

-- Nested temporal operators quantify over the future of each current position.
example : ⇓LTL[model ⊨ G F later] := by
  rw [Satisfies.at_always_iff model 0 later.eventually]
  intro k _
  rw [Satisfies.at_eventually_iff model k later]
  refine ⟨k + 2, by omega, ?_⟩
  change 12 ≤ k + 2 + 10
  omega

-- An immediate witness does not require the left operand.
example : ⇓Modal[(Model.ofTracePredicates trace).toModal,⟨2, 7⟩ ⊨
    (⊥ : Proposition (StateAtom ℕ)) U reached] := by
  rw [Satisfies.until_iff (Model.ofTracePredicates trace) 2 7 ⊥ reached]
  exact ⟨2, by omega, rfl, by omega⟩

-- Strong until requires a witness even when the left operand always holds.
example : ¬⇓Modal[(Model.ofTracePredicates trace).toModal,⟨0, 7⟩ ⊨
    (⊤ : Proposition (StateAtom ℕ)) U ⊥] := by
  rw [Satisfies.until_iff (Model.ofTracePredicates trace) 0 7 ⊤ ⊥]
  rintro ⟨k, _, hk, _⟩
  exact hk

-- Release allows its right operand to hold forever without the left operand ever holding.
example : ⇓Modal[(Model.ofTracePredicates trace).toModal,⟨0, 7⟩ ⊨
    (⊥ : Proposition (StateAtom ℕ)) R ⊤] := by
  rw [Satisfies.release_iff (Model.ofTracePredicates trace) 0 7 ⊥ ⊤]
  exact fun _ _ => Or.inl Modal.Satisfies.true

-- The right operand of release must hold at the releasing position as well.
example : ¬⇓Modal[(Model.ofTracePredicates trace).toModal,⟨2, 7⟩ ⊨ reached R before] := by
  rw [Satisfies.release_iff (Model.ofTracePredicates trace) 2 7 reached before]
  intro h
  rcases h 2 (by omega) with h | ⟨j, hj, hk, _⟩
  · change 12 < 12 at h
    omega
  · omega

-- Nested untils reset their own anchors without affecting an enclosing interval.
example : ⇓LTL[model ⊨ (before U reached) U reached] := by
  rw [Satisfies.at_until_iff model 0 (before.until reached) reached]
  refine ⟨2, by omega, rfl, ?_⟩
  intro j _ hj
  rw [Satisfies.at_until_iff model j before reached]
  refine ⟨2, by omega, rfl, ?_⟩
  intro i _ hi
  change i + 10 < 12
  omega

example (m : Model State Atom) (p q r : Atom) (n a b : ℕ) :
    ⇓Modal[m.toModal,⟨n, a⟩ ⊨
      Proposition.until (Proposition.until (.atom p) (.atom q)) (.atom r)] ↔
    ⇓Modal[m.toModal,⟨n, b⟩ ⊨
      Proposition.until (Proposition.until (.atom p) (.atom q)) (.atom r)] :=
  Satisfies.anchor_iff m (Proposition.until (Proposition.until (.atom p) (.atom q)) (.atom r))
    n a b

-- Generic modal denotation applies directly to temporal propositions.
example (m : Model State Atom) (φ : Proposition Atom) (n a : ℕ) :
    (⟨n, a⟩ : Point) ∈ φ.next.val.denotation m.toModal ↔
      ⇓Modal[m.toModal,⟨n + 1, a⟩ ⊨ φ] := by
  rw [satisfies_mem_denotation, Satisfies.next_iff m n a φ]

end Cslib.Logic.Modal.LTL
