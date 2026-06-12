/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Temporal.Semantics.Model

/-! # Temporal Satisfaction Relation

This module defines the recursive satisfaction relation `Satisfies` for temporal
logic formulas evaluated in a `TemporalModel` on a linear order.

## Burgess Convention (Event, Guard)

The `untl` and `snce` operators follow the Burgess convention where the first
argument is the EVENT (holds at the witness point) and the second is the GUARD
(holds at all intermediate points):

- `untl φ ψ` at `t`: there exists `s > t` such that `φ` holds at `s` (event)
  and `ψ` holds at all `r` strictly between `t` and `s` (guard).
- `snce φ ψ` at `t`: there exists `s < t` such that `φ` holds at `s` (event)
  and `ψ` holds at all `r` strictly between `s` and `t` (guard).

This matches the abstract typeclass expansion in `Axioms.lean` and the `Formula.someFuture`
definition (`someFuture φ = untl φ top`, where φ is the event and ⊤ is the trivial guard).

## Main Definitions

- `Temporal.Satisfies`: Recursive truth evaluation for all formula constructors.

## Main Results

- `bot_false`, `atom_iff`, `imp_iff`, `untl_iff`, `snce_iff`: Constructor lemmas.
- `neg_iff`, `top_true`: Derived connective lemmas.
- `someFuture_iff`, `somePast_iff`: Existential temporal operator characterizations.
- `allFuture_iff`, `allPast_iff`: Universal temporal operator characterizations.
-/

@[expose] public section

namespace Cslib.Logic.Temporal

variable {D : Type*} [LinearOrder D] {Atom : Type*}

/-- Truth of a temporal formula at a time point in a model.

The evaluation is defined recursively on formula structure:
- Atoms: true iff the valuation assigns true at this time.
- Bot (⊥): always false.
- Implication: standard material conditional.
- Until U(φ,ψ): ∃ s > t, φ(s) ∧ ∀ r ∈ (t,s), ψ(r).  (φ=EVENT, ψ=GUARD)
- Since S(φ,ψ): ∃ s < t, φ(s) ∧ ∀ r ∈ (s,t), ψ(r).  (φ=EVENT, ψ=GUARD)
-/
def Satisfies (M : TemporalModel D Atom) (t : D) : Formula Atom → Prop
  | .atom p => M.valuation t p
  | .bot => False
  | .imp φ ψ => Satisfies M t φ → Satisfies M t ψ
  | .untl φ ψ =>
    ∃ s, t < s ∧ Satisfies M s φ ∧
      ∀ r, t < r → r < s → Satisfies M r ψ
  | .snce φ ψ =>
    ∃ s, s < t ∧ Satisfies M s φ ∧
      ∀ r, s < r → r < t → Satisfies M r ψ

namespace Satisfies

/-! ## Constructor Lemmas -/

/-- Bot (⊥) is false everywhere. -/
theorem bot_false (M : TemporalModel D Atom) (t : D) :
    ¬ Satisfies M t .bot :=
  id

/-- Truth of an atom is determined by the valuation. -/
@[simp]
theorem atom_iff (M : TemporalModel D Atom) (t : D) (p : Atom) :
    Satisfies M t (.atom p) ↔ M.valuation t p :=
  Iff.rfl

/-- Truth of implication is material conditional. -/
@[simp]
theorem imp_iff (M : TemporalModel D Atom) (t : D)
    (φ ψ : Formula Atom) :
    Satisfies M t (.imp φ ψ) ↔
      (Satisfies M t φ → Satisfies M t ψ) :=
  Iff.rfl

/-- Characterization of Until: ∃ s > t with event φ at s and guard ψ between. -/
@[simp]
theorem untl_iff (M : TemporalModel D Atom) (t : D)
    (φ ψ : Formula Atom) :
    Satisfies M t (.untl φ ψ) ↔
      ∃ s, t < s ∧ Satisfies M s φ ∧
        ∀ r, t < r → r < s → Satisfies M r ψ :=
  Iff.rfl

/-- Characterization of Since: ∃ s < t with event φ at s and guard ψ between. -/
@[simp]
theorem snce_iff (M : TemporalModel D Atom) (t : D)
    (φ ψ : Formula Atom) :
    Satisfies M t (.snce φ ψ) ↔
      ∃ s, s < t ∧ Satisfies M s φ ∧
        ∀ r, s < r → r < t → Satisfies M r ψ :=
  Iff.rfl

/-! ## Derived Connective Lemmas -/

/-- Negation: ¬φ holds iff φ does not hold. -/
theorem neg_iff (M : TemporalModel D Atom) (t : D)
    (φ : Formula Atom) :
    Satisfies M t (¬φ) ↔ ¬ Satisfies M t φ := by
  simp only [Satisfies]

/-- Top (⊤) is true everywhere. -/
theorem top_true (M : TemporalModel D Atom) (t : D) :
    Satisfies M t Formula.top := by
  intro h
  exact h

/-! ## Temporal Operator Lemmas -/

/-- Some future (F φ): there exists a future time where φ holds. -/
theorem someFuture_iff (M : TemporalModel D Atom) (t : D)
    (φ : Formula Atom) :
    Satisfies M t (𝐅φ) ↔
      ∃ s, t < s ∧ Satisfies M s φ := by
  simp only [Satisfies]
  constructor
  · rintro ⟨s, hlt, hevent, _⟩
    exact ⟨s, hlt, hevent⟩
  · rintro ⟨s, hlt, hs⟩
    exact ⟨s, hlt, hs, fun _ _ _ h => h⟩

/-- Some past (P φ): there exists a past time where φ holds. -/
theorem somePast_iff (M : TemporalModel D Atom) (t : D)
    (φ : Formula Atom) :
    Satisfies M t (𝐏φ) ↔
      ∃ s, s < t ∧ Satisfies M s φ := by
  simp only [Satisfies]
  constructor
  · rintro ⟨s, hlt, hevent, _⟩
    exact ⟨s, hlt, hevent⟩
  · rintro ⟨s, hlt, hs⟩
    exact ⟨s, hlt, hs, fun _ _ _ h => h⟩

/-- All future (G φ): φ holds at all future times. -/
theorem allFuture_iff (M : TemporalModel D Atom) (t : D)
    (φ : Formula Atom) :
    Satisfies M t (𝐆φ) ↔
      ∀ s, t < s → Satisfies M s φ := by
  simp only [Satisfies]
  constructor
  · intro h s hlt
    by_contra hns
    exact h ⟨s, hlt, hns, fun _ _ _ h => h⟩
  · intro h ⟨s, hlt, hevent, _⟩
    exact hevent (h s hlt)

/-- All past (H φ): φ holds at all past times. -/
theorem allPast_iff (M : TemporalModel D Atom) (t : D)
    (φ : Formula Atom) :
    Satisfies M t (𝐇φ) ↔
      ∀ s, s < t → Satisfies M s φ := by
  simp only [Satisfies]
  constructor
  · intro h s hlt
    by_contra hns
    exact h ⟨s, hlt, hns, fun _ _ _ h => h⟩
  · intro h ⟨s, hlt, hevent, _⟩
    exact hevent (h s hlt)

end Satisfies

end Cslib.Logic.Temporal
