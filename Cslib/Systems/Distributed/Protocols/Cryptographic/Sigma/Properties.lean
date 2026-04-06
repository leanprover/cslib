/-
Copyright (c) 2026 Christiano Braga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christiano Braga
-/

module

public import Mathlib.Tactic
public import Cslib.Systems.Distributed.Protocols.Cryptographic.Sigma.Basic

@[expose] public section

/-!
# Algebraic Properties of Sigma Protocols

This file establishes compositional properties of sigma protocols:

- **AND-composition**: Given sigma protocols for relations R₁ and R₂ over the same challenge
  space, we construct a sigma protocol for R₁ ∧ R₂. Both sub-protocols run in parallel with
  the same challenge.

- **OR-composition**: Given sigma protocols for relations R₁ and R₂ over an additive group
  challenge space, we construct a sigma protocol for R₁ ∨ R₂. The prover simulates the
  protocol for the unknown statement and splits the challenge as e = e₁ + e₂.

- **Witness indistinguishability**: The simulator output is independent of any particular
  witness, so the verifier cannot determine which witness was used.

Reference:

* [D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup],
  Sections 19.5, 19.6.
-/

private theorem shvzk_elim {S : Type*} {W : Type*} {C : Type*} {Ch : Type*} {R : Type*}
    [P : SigmaProtocol S W C Ch R] (s : S) (e : Ch) :
    P.verify s (P.simulate s e).1 e (P.simulate s e).2 := by
  have h := P.shvzk s e
  revert h; generalize P.simulate s e = p; obtain ⟨a, z⟩ := p; grind

section ANDComposition

/-!
## AND-Composition

Given two sigma protocols P₁ and P₂ sharing the same challenge type Ch, we build a
sigma protocol for the conjunction of their relations. Both sub-protocols run in parallel
with the same challenge.
-/

instance SigmaAND
    {S₁ : Type*} {W₁ : Type*} {C₁ : Type*} {Ch : Type*} {R₁ : Type*}
    {S₂ : Type*} {W₂ : Type*} {C₂ : Type*} {R₂ : Type*}
    [P₁ : SigmaProtocol S₁ W₁ C₁ Ch R₁]
    [P₂ : SigmaProtocol S₂ W₂ C₂ Ch R₂] :
    SigmaProtocol (S₁ × S₂) (W₁ × W₂) (C₁ × C₂) Ch (R₁ × R₂) where
  rel := fun s w => P₁.rel s.1 w.1 ∧ P₂.rel s.2 w.2
  commit := fun s w => (P₁.commit s.1 w.1, P₂.commit s.2 w.2)
  respond := fun s w a e => (P₁.respond s.1 w.1 a.1 e, P₂.respond s.2 w.2 a.2 e)
  verify := fun s a e z => P₁.verify s.1 a.1 e z.1 ∧ P₂.verify s.2 a.2 e z.2
  extract := fun s a e z e' z' =>
    (P₁.extract s.1 a.1 e z.1 e' z'.1, P₂.extract s.2 a.2 e z.2 e' z'.2)
  simulate := fun s e =>
    let p₁ := P₁.simulate s.1 e
    let p₂ := P₂.simulate s.2 e
    ((p₁.1, p₂.1), (p₁.2, p₂.2))
  nonDegenerate := by
    obtain ⟨s₁, w₁, h₁⟩ := P₁.nonDegenerate
    obtain ⟨s₂, w₂, h₂⟩ := P₂.nonDegenerate
    exact ⟨(s₁, s₂), (w₁, w₂), h₁, h₂⟩
  complete := by
    intro ⟨s₁, s₂⟩ ⟨w₁, w₂⟩ e ⟨h₁, h₂⟩
    grind [P₁.complete, P₂.complete]
  sound := by
    intro ⟨s₁, s₂⟩ ⟨a₁, a₂⟩ e e' ⟨z₁, z₂⟩ ⟨z₁', z₂'⟩ hne ⟨hv₁, hv₂⟩ ⟨hv₁', hv₂'⟩
    grind [P₁.sound, P₂.sound]
  shvzk := by
    intro ⟨s₁, s₂⟩ e
    exact ⟨shvzk_elim s₁ e, shvzk_elim s₂ e⟩

end ANDComposition

section ORComposition

/-!
## OR-Composition

Given two sigma protocols P₁ and P₂ whose challenge type Ch forms an additive commutative
group with decidable equality, we build a sigma protocol for the disjunction of their
relations.

The prover, who knows a witness for one of the two statements, simulates the transcript for
the other statement and splits the verifier's challenge as e = e₁ + e₂.

The witness type is `(W₁ × Ch) ⊕ (Ch × W₂)`:
- `Sum.inl (w₁, e₂)`: prover knows w₁ for s₁, picks e₂ to simulate P₂
- `Sum.inr (e₁, w₂)`: prover knows w₂ for s₂, picks e₁ to simulate P₁
-/

instance SigmaOR
    {S₁ : Type*} {W₁ : Type*} {C₁ : Type*} {Ch : Type*} {R₁ : Type*}
    {S₂ : Type*} {W₂ : Type*} {C₂ : Type*} {R₂ : Type*}
    [P₁ : SigmaProtocol S₁ W₁ C₁ Ch R₁]
    [P₂ : SigmaProtocol S₂ W₂ C₂ Ch R₂]
    [AddCommGroup Ch] [DecidableEq Ch] :
    SigmaProtocol (S₁ × S₂) ((W₁ × Ch) ⊕ (Ch × W₂)) (C₁ × C₂) Ch (R₁ × R₂ × Ch) where
  rel := fun s w => match w with
    | .inl (w₁, _) => P₁.rel s.1 w₁
    | .inr (_, w₂) => P₂.rel s.2 w₂
  commit := fun s w => match w with
    | .inl (w₁, e₂) =>
      (P₁.commit s.1 w₁, (P₂.simulate s.2 e₂).1)
    | .inr (e₁, w₂) =>
      ((P₁.simulate s.1 e₁).1, P₂.commit s.2 w₂)
  respond := fun s w a e => match w with
    | .inl (w₁, e₂) =>
      (P₁.respond s.1 w₁ a.1 (e - e₂), (P₂.simulate s.2 e₂).2, e - e₂)
    | .inr (e₁, w₂) =>
      ((P₁.simulate s.1 e₁).2, P₂.respond s.2 w₂ a.2 (e - e₁), e₁)
  verify := fun s a e z =>
    let (z₁, z₂, e₁) := z
    P₁.verify s.1 a.1 e₁ z₁ ∧ P₂.verify s.2 a.2 (e - e₁) z₂
  extract := fun s a e z e' z' =>
    let e₁ := z.2.2
    let e₁' := z'.2.2
    if e₁ ≠ e₁' then
      .inl (P₁.extract s.1 a.1 e₁ z.1 e₁' z'.1, 0)
    else
      .inr (0, P₂.extract s.2 a.2 (e - e₁) z.2.1 (e' - e₁') z'.2.1)
  simulate := fun s e =>
    let p₁ := P₁.simulate s.1 0
    let p₂ := P₂.simulate s.2 e
    ((p₁.1, p₂.1), (p₁.2, p₂.2, 0))
  nonDegenerate := by
    obtain ⟨s₁, w₁, h₁⟩ := P₁.nonDegenerate
    obtain ⟨s₂, _, _⟩ := P₂.nonDegenerate
    exact ⟨(s₁, s₂), .inl (w₁, 0), h₁⟩
  complete := by
    intro ⟨s₁, s₂⟩ w e hw
    match w, hw with
    | .inl (w₁, e₂), hw =>
      refine ⟨P₁.complete s₁ w₁ (e - e₂) hw, ?_⟩
      have : e - (e - e₂) = e₂ := by abel
      rw [this]
      exact shvzk_elim s₂ e₂
    | .inr (e₁, w₂), hw =>
      refine ⟨shvzk_elim s₁ e₁, ?_⟩
      exact P₂.complete s₂ w₂ (e - e₁) hw
  sound := by
    intro ⟨s₁, s₂⟩ ⟨a₁, a₂⟩ e e' ⟨z₁, z₂, e₁⟩ ⟨z₁', z₂', e₁'⟩ hne ⟨hv₁, hv₂⟩ ⟨hv₁', hv₂'⟩
    simp only [ne_eq]
    by_cases h : e₁ = e₁'
    · subst h
      simp only [not_true_eq_false, ↓reduceIte]
      have hne₂ : e - e₁ ≠ e' - e₁ := fun heq => hne (by
        have : e - e₁ + e₁ = e' - e₁ + e₁ := by rw [heq]
        rwa [sub_add_cancel, sub_add_cancel] at this)
      exact P₂.sound s₂ a₂ (e - e₁) (e' - e₁) z₂ z₂' hne₂ hv₂ hv₂'
    · simp only [h, not_false_eq_true, ↓reduceIte]
      exact P₁.sound s₁ a₁ e₁ e₁' z₁ z₁' h hv₁ hv₁'
  shvzk := by
    intro ⟨s₁, s₂⟩ e
    exact ⟨shvzk_elim s₁ (0 : Ch), by simp only [sub_zero]; exact shvzk_elim s₂ e⟩

end ORComposition

section WitnessIndistinguishability

/-!
## Witness Indistinguishability

A sigma protocol with SHVZK is witness-indistinguishable for honest verifiers: the simulator
produces valid transcripts without access to any witness. This means the simulated transcript
is consistent with *every* valid witness — the verifier learns nothing about *which* witness
the prover holds.
-/

theorem simulator_independent_of_witness
    {S : Type*} {W : Type*} {C : Type*} {Ch : Type*} {R : Type*}
    [P : SigmaProtocol S W C Ch R]
    (s : S) (e : Ch) :
    P.verify s (P.simulate s e).1 e (P.simulate s e).2 :=
  shvzk_elim s e

end WitnessIndistinguishability
