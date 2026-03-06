/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Cryptography.Protocols.SigmaProtocol

@[expose] public section

/-!
# AND and OR Combinators for Sigma Protocols

Sigma protocols can be combined to prove compound statements:

- **AND**: given protocols for `R₀` and `R₁`, construct a protocol
  for `R₀ ∧ R₁` (the prover knows witnesses for both)
- **OR**: given protocols for `R₀` and `R₁`, construct a protocol
  for `R₀ ∨ R₁` (the prover knows a witness for at least one)

## Main Definitions

* `SigmaProtocol.AND` — the AND combinator
* `SigmaProtocol.AND.specialSoundness` — AND preserves special soundness
* `SigmaProtocol.OR` — the OR combinator with challenge splitting
* `SigmaProtocol.OR.specialSoundness` — OR preserves special soundness
* `SigmaProtocol.OR.specialHVZK` — OR preserves special HVZK

## References

* Boneh-Shoup, *A Graduate Course in Applied Cryptography*, §19.7
* [R. Cramer, I. Damgård, B. Schoenmakers, *Proofs of Partial
  Knowledge*][CDS1994]
-/

private theorem ne_of_cast_ne {α β : Type} (h : α = β) {a b : α}
    (hne : a ≠ b) : h ▸ a ≠ h ▸ b := by subst h; exact hne

/-! ### AND Combinator -/

/-- The **AND relation**: `(w₀, w₁)` is a witness for `(y₀, y₁)`
when `w₀` witnesses `y₀` in `R₀` and `w₁` witnesses `y₁` in `R₁`. -/
def EffectiveRelation.AND (R₀ R₁ : EffectiveRelation) :
    EffectiveRelation where
  Witness n := R₀.Witness n × R₁.Witness n
  Statement n := R₀.Statement n × R₁.Statement n
  relation n w y := R₀.relation n w.1 y.1 ∧ R₁.relation n w.2 y.2

/-- The **AND combinator** for Sigma protocols: run both protocols
in parallel with the same challenge.

Given protocols `P₀` for `R₀` and `P₁` for `R₁` sharing the same
challenge type, the combined protocol for `R₀ ∧ R₁`:
- Commitment: `(t₀, t₁)`
- Challenge: `c` (same challenge sent to both)
- Response: `(z₀, z₁)`
- Verify: both sub-protocols accept -/
noncomputable def SigmaProtocol.AND
    {R₀ R₁ : EffectiveRelation}
    (P₀ : SigmaProtocol R₀) (P₁ : SigmaProtocol R₁)
    -- Shared challenge type
    (hChallenge : ∀ n, P₀.Challenge n = P₁.Challenge n) :
    SigmaProtocol (R₀.AND R₁) where
  Commitment n := P₀.Commitment n × P₁.Commitment n
  Challenge := P₀.Challenge
  Response n := P₀.Response n × P₁.Response n
  ProverRandomness n := P₀.ProverRandomness n × P₁.ProverRandomness n
  commitmentFintype := fun n => inferInstance
  commitmentNonempty := fun n => inferInstance
  commitmentDecEq := fun n => inferInstance
  challengeFintype := P₀.challengeFintype
  challengeNonempty := P₀.challengeNonempty
  challengeDecEq := P₀.challengeDecEq
  responseFintype := fun n => inferInstance
  responseNonempty := fun n => inferInstance
  proverRandomnessFintype := fun n => inferInstance
  proverRandomnessNonempty := fun n => inferInstance
  commit n w y r :=
    (P₀.commit n w.1 y.1 r.1, P₁.commit n w.2 y.2 r.2)
  respond n w y r c :=
    (P₀.respond n w.1 y.1 r.1 c,
     P₁.respond n w.2 y.2 r.2 (hChallenge n ▸ c))
  verify n y t c z :=
    P₀.verify n y.1 t.1 c z.1 &&
    P₁.verify n y.2 t.2 (hChallenge n ▸ c) z.2
  completeness n w y r c hrel := by
    simp only [Bool.and_eq_true]
    exact ⟨P₀.completeness n w.1 y.1 r.1 c hrel.1,
           P₁.completeness n w.2 y.2 r.2 _ hrel.2⟩

/-- The AND combinator **preserves special soundness**: if both
sub-protocols have special soundness, so does the AND protocol.
The extractor runs both sub-extractors independently. -/
noncomputable def SigmaProtocol.AND.specialSoundness
    {R₀ R₁ : EffectiveRelation}
    {P₀ : SigmaProtocol R₀} {P₁ : SigmaProtocol R₁}
    {hChallenge : ∀ n, P₀.Challenge n = P₁.Challenge n}
    (ss₀ : P₀.SpecialSoundness) (ss₁ : P₁.SpecialSoundness) :
    (SigmaProtocol.AND P₀ P₁ hChallenge).SpecialSoundness where
  extract n y t c z c' z' :=
    (ss₀.extract n y.1 t.1 c z.1 c' z'.1,
     ss₁.extract n y.2 t.2 (hChallenge n ▸ c) z.2
       (hChallenge n ▸ c') z'.2)
  soundness n y t c z c' z' hne hv1 hv2 := by
    simp only [SigmaProtocol.AND, Bool.and_eq_true] at hv1 hv2
    constructor
    · exact ss₀.soundness n y.1 t.1 c z.1 c' z'.1 hne hv1.1 hv2.1
    · exact ss₁.soundness n y.2 t.2 _ z.2 _ z'.2
        (ne_of_cast_ne (hChallenge n) hne) hv1.2 hv2.2

/-! ### OR Combinator -/

/-- The **OR relation**: `w` is a witness for `(y₀, y₁)` when
`w` witnesses `y₀` in `R₀` or `y₁` in `R₁`. The witness is
tagged with `Sum` to indicate which side it proves. -/
def EffectiveRelation.OR (R₀ R₁ : EffectiveRelation) :
    EffectiveRelation where
  Witness n := R₀.Witness n ⊕ R₁.Witness n
  Statement n := R₀.Statement n × R₁.Statement n
  relation n w y :=
    match w with
    | .inl w₀ => R₀.relation n w₀ y.1
    | .inr w₁ => R₁.relation n w₁ y.2

/-- The **OR combinator** for Sigma protocols. The prover knows a
witness for one side and simulates the other using the HVZK
simulator.

Challenge splitting: the overall challenge `c` is split as
`c = c₀ + c₁`. The prover chooses the simulated side's challenge
and derives the honest side's challenge after receiving `c`.

The prover randomness includes randomness for both sub-protocols,
a simulated challenge, and simulator randomness for both sides.
Depending on which witness the prover holds, the appropriate
components are used. -/
noncomputable def SigmaProtocol.OR
    {R₀ R₁ : EffectiveRelation}
    (P₀ : SigmaProtocol R₀) (P₁ : SigmaProtocol R₁)
    [∀ n, AddCommGroup (P₀.Challenge n)]
    [∀ n, DecidableEq (P₀.Challenge n)]
    (hvzk₀ : P₀.SpecialHVZK) (hvzk₁ : P₁.SpecialHVZK)
    -- Challenges must be the same type for splitting
    (challengeEq : ∀ n, P₀.Challenge n = P₁.Challenge n) :
    SigmaProtocol (R₀.OR R₁) where
  Commitment n := P₀.Commitment n × P₁.Commitment n
  Challenge := P₀.Challenge
  Response n := P₀.Response n × P₁.Response n ×
    P₀.Challenge n  -- c₀ is included so verifier can reconstruct c₁
  -- Prover randomness: both protocols' randomness + simulated challenge + both simulator randomness
  ProverRandomness n :=
    P₀.ProverRandomness n × P₁.ProverRandomness n ×
    P₀.Challenge n ×
    hvzk₀.SimRandomness n × hvzk₁.SimRandomness n
  commitmentFintype := fun n => inferInstance
  commitmentNonempty := fun n => inferInstance
  commitmentDecEq := fun n => inferInstance
  challengeFintype := P₀.challengeFintype
  challengeNonempty := P₀.challengeNonempty
  challengeDecEq := inferInstance
  responseFintype := fun n => inferInstance
  responseNonempty := fun n => inferInstance
  proverRandomnessFintype := fun n => by
    haveI := hvzk₀.simRandomnessFintype n
    haveI := hvzk₁.simRandomnessFintype n
    exact inferInstance
  proverRandomnessNonempty := fun n => by
    haveI := hvzk₀.simRandomnessNonempty n
    haveI := hvzk₁.simRandomnessNonempty n
    exact inferInstance
  commit n w y r :=
    let (r₀, r₁, simC, s₀, s₁) := r
    match w with
    | .inl w₀ =>
      -- Know w₀: commit honestly to P₀, simulate P₁
      let t₀ := P₀.commit n w₀ y.1 r₀
      let (t₁, _) := hvzk₁.simulate n y.2 (challengeEq n ▸ simC) s₁
      (t₀, t₁)
    | .inr w₁ =>
      -- Know w₁: simulate P₀, commit honestly to P₁
      let (t₀, _) := hvzk₀.simulate n y.1 simC s₀
      let t₁ := P₁.commit n w₁ y.2 r₁
      (t₀, t₁)
  respond n w y r c :=
    let (r₀, r₁, simC, s₀, s₁) := r
    match w with
    | .inl w₀ =>
      -- c₀ = c - simC, simC is the P₁ simulated challenge
      let c₀ := c - simC
      let z₀ := P₀.respond n w₀ y.1 r₀ c₀
      let (_, z₁) := hvzk₁.simulate n y.2 (challengeEq n ▸ simC) s₁
      (z₀, z₁, c₀)
    | .inr w₁ =>
      -- c₁ = c - simC, simC is the P₀ simulated challenge
      let c₁ := c - simC
      let z₁ := P₁.respond n w₁ y.2 r₁ (challengeEq n ▸ c₁)
      let (_, z₀) := hvzk₀.simulate n y.1 simC s₀
      (z₀, z₁, simC)
  verify n y t c z :=
    let (z₀, z₁, c₀) := z
    let c₁ := c - c₀
    P₀.verify n y.1 t.1 c₀ z₀ && P₁.verify n y.2 t.2 (challengeEq n ▸ c₁) z₁
  completeness n w y r c hrel := by
    simp only [Bool.and_eq_true]
    obtain ⟨r₀, r₁, simC, s₀, s₁⟩ := r
    match w, hrel with
    | .inl w₀, hrel₀ =>
      constructor
      · -- P₀: honest execution with c₀ = c - simC
        exact P₀.completeness n w₀ y.1 r₀ (c - simC) hrel₀
      · -- P₁: simulated, always accepting by sim_accepting
        have hsim := hvzk₁.sim_accepting n y.2 (challengeEq n ▸ simC) s₁
        -- c₁ = c - c₀ = c - (c - simC) = simC
        have : c - (c - simC) = simC := by abel
        rw [this]
        exact hsim
    | .inr w₁, hrel₁ =>
      constructor
      · -- P₀: simulated, always accepting
        exact hvzk₀.sim_accepting n y.1 simC s₀
      · -- P₁: honest execution with c₁ = c - simC
        exact P₁.completeness n w₁ y.2 r₁ _ hrel₁

/-- The OR combinator **preserves special soundness** (CDS94):
from two accepting conversations `(t, c, z)` and `(t, c', z')` with the
same commitment but different challenges, extract a witness for at least
one side of the OR relation.

**Extractor**: case split on whether the P₀ sub-challenges `c₀` and `c₀'` differ.
- If `c₀ ≠ c₀'`: extract from P₀
- If `c₀ = c₀'`: then `c₁ ≠ c₁'` (since `c ≠ c'` and `c₀ = c₀'`), extract from P₁ -/
noncomputable def SigmaProtocol.OR.specialSoundness
    {R₀ R₁ : EffectiveRelation}
    {P₀ : SigmaProtocol R₀} {P₁ : SigmaProtocol R₁}
    [∀ n, AddCommGroup (P₀.Challenge n)]
    [∀ n, DecidableEq (P₀.Challenge n)]
    {hvzk₀ : P₀.SpecialHVZK} {hvzk₁ : P₁.SpecialHVZK}
    {challengeEq : ∀ n, P₀.Challenge n = P₁.Challenge n}
    (ss₀ : P₀.SpecialSoundness) (ss₁ : P₁.SpecialSoundness) :
    (SigmaProtocol.OR P₀ P₁ hvzk₀ hvzk₁ challengeEq).SpecialSoundness where
  extract n y t c z c' z' := by
    let ch : P₀.Challenge n := c
    let ch' : P₀.Challenge n := c'
    let c₀ := z.2.2
    let c₀' := z'.2.2
    exact if _ : c₀ = c₀' then
      .inr (ss₁.extract n y.2 t.2
        (challengeEq n ▸ (ch - c₀)) z.2.1
        (challengeEq n ▸ (ch' - c₀')) z'.2.1)
    else
      .inl (ss₀.extract n y.1 t.1 c₀ z.1 c₀' z'.1)
  soundness n y t c z c' z' hne hv1 hv2 := by
    simp only [SigmaProtocol.OR, Bool.and_eq_true] at hv1 hv2
    simp only
    split
    case isTrue h =>
      -- c₀ = c₀', so c₁ ≠ c₁'
      simp only [EffectiveRelation.OR]
      apply ss₁.soundness
      · apply ne_of_cast_ne (challengeEq n)
        rw [← h]
        intro heq
        exact hne (by
          have := congr_arg (· + z.2.2) heq
          simp only [sub_add_cancel] at this
          exact this)
      · exact hv1.2
      · exact hv2.2
    case isFalse h =>
      simp only [EffectiveRelation.OR]
      exact ss₀.soundness n y.1 t.1 _ z.1 _ z'.1 h hv1.1 hv2.1

/-- The OR combinator **preserves special HVZK** (CDS94):
given HVZK simulators for both sub-protocols, construct an HVZK
simulator for the OR protocol.

The OR simulator runs both sub-protocol simulators with a random
challenge split `c₀ + c₁ = c`, without needing any witness. -/
noncomputable def SigmaProtocol.OR.specialHVZK
    {R₀ R₁ : EffectiveRelation}
    {P₀ : SigmaProtocol R₀} {P₁ : SigmaProtocol R₁}
    [∀ n, AddCommGroup (P₀.Challenge n)]
    [∀ n, DecidableEq (P₀.Challenge n)]
    (hvzk₀ : P₀.SpecialHVZK) (hvzk₁ : P₁.SpecialHVZK)
    (challengeEq : ∀ n, P₀.Challenge n = P₁.Challenge n) :
    (SigmaProtocol.OR P₀ P₁ hvzk₀ hvzk₁ challengeEq).SpecialHVZK where
  SimRandomness n := hvzk₀.SimRandomness n × hvzk₁.SimRandomness n × P₀.Challenge n
  simRandomnessFintype n := by
    haveI := hvzk₀.simRandomnessFintype n
    haveI := hvzk₁.simRandomnessFintype n
    exact inferInstance
  simRandomnessNonempty n := by
    haveI := hvzk₀.simRandomnessNonempty n
    haveI := hvzk₁.simRandomnessNonempty n
    exact inferInstance
  simulate n y c s :=
    (((hvzk₀.simulate n y.1 s.2.2 s.1).1,
      (hvzk₁.simulate n y.2
        (challengeEq n ▸ (@id (P₀.Challenge n) c - s.2.2)) s.2.1).1),
     ((hvzk₀.simulate n y.1 s.2.2 s.1).2,
      (hvzk₁.simulate n y.2
        (challengeEq n ▸ (@id (P₀.Challenge n) c - s.2.2)) s.2.1).2,
      s.2.2))
  sim_accepting n y c s := by
    simp only [SigmaProtocol.OR]
    simp only [Bool.and_eq_true]
    exact ⟨hvzk₀.sim_accepting n y.1 s.2.2 s.1,
           hvzk₁.sim_accepting n y.2 _ s.2.1⟩
  sim_distribution n w y c hrel f := by
    open Cslib.Probability in
    match w, hrel with
    | .inl w₀, hrel₀ =>
      letI := hvzk₀.simRandomnessFintype n
      letI := hvzk₁.simRandomnessFintype n
      letI := hvzk₀.simRandomnessNonempty n
      letI := hvzk₁.simRandomnessNonempty n
      dsimp only [SigmaProtocol.OR]
      -- Step 1: Factor out unused r₁ (P₁.ProverRandomness) and s₀ (hvzk₀.SimRandomness)
      -- Provide g explicitly to bypass higher-order matching
      let ch : P₀.Challenge n := c
      have step1 := uniformExpect_prod5_ignore_bd
        (B := P₁.ProverRandomness n) (D := hvzk₀.SimRandomness n)
        (fun a simC s₁ =>
          f ((P₀.commit n w₀ y.1 a,
              (hvzk₁.simulate n y.2 (challengeEq n ▸ simC) s₁).1),
             (P₀.respond n w₀ y.1 a (ch - simC),
              (hvzk₁.simulate n y.2 (challengeEq n ▸ simC) s₁).2,
              ch - simC)))
      erw [step1]
      -- Now: E_{(r₀, simC, s₁)}[body] = E_{(s₀', s₁', c₀)}[body']
      -- Step 2: Decompose both sides into individual expectations
      rw [uniformExpect_prod]
      simp_rw [uniformExpect_prod]
      -- Step 3: Swap order on LHS so r₀ is innermost
      rw [uniformExpect_comm]
      simp_rw [uniformExpect_comm (P₀.ProverRandomness n)]
      -- LHS: E_{simC}[E_{s₁}[E_{r₀}[body(r₀,simC,s₁)]]]
      -- Step 4: Apply sim_distribution to inner E_{r₀}
      conv_lhs =>
        arg 2; ext simC
        arg 2; ext s₁
        erw [hvzk₀.sim_distribution n w₀ y.1 (ch - simC) hrel₀
          (fun pair =>
            f ((pair.1, (hvzk₁.simulate n y.2 (challengeEq n ▸ simC) s₁).1),
               (pair.2, (hvzk₁.simulate n y.2 (challengeEq n ▸ simC) s₁).2,
                ch - simC)))]
      -- Step 5: Reorder expectations to match RHS
      -- LHS: E_{simC}[E_{s₁}[E_{s₀'}[...]]]
      -- Need: E_{s₀'}[E_{s₁}[E_{simC}[...]]]
      rw [uniformExpect_comm]
      simp_rw [uniformExpect_comm (P₀.Challenge n)]
      rw [uniformExpect_comm]
      -- Step 6: Drill down to inner expectation
      congr 1; ext s₀'; congr 1; ext s₁'
      -- Goal: E_{simC}[body_lhs(simC)] = E_{c₀}[body_rhs(c₀)]
      -- Step 7: Reindex c₀ ↦ ch - c₀ on RHS
      let σ : P₀.Challenge n ≃ P₀.Challenge n :=
        { toFun := fun x => ch - x
          invFun := fun x => ch - x
          left_inv := fun x => by simp [sub_sub_cancel]
          right_inv := fun x => by simp [sub_sub_cancel] }
      rw [← uniformExpect_equiv _ _ σ]
      -- Goal: E_{simC}[body_lhs(simC)] = E_{c₀}[body_rhs(ch - c₀)]
      congr 1; ext simC
      -- Body equality: need c - (ch - simC) = simC, ch - simC = ch - simC
      simp only [σ, Equiv.coe_fn_mk, sub_sub_cancel, id]; rfl
    | .inr w₁, hrel₁ =>
      letI := hvzk₀.simRandomnessFintype n
      letI := hvzk₁.simRandomnessFintype n
      letI := hvzk₀.simRandomnessNonempty n
      letI := hvzk₁.simRandomnessNonempty n
      dsimp only [SigmaProtocol.OR]
      -- Step 1: Factor out unused r₀ (P₀.ProverRandomness) and s₁ (hvzk₁.SimRandomness)
      let ch : P₀.Challenge n := c
      have step1 := uniformExpect_prod5_ignore_ae
        (A := P₀.ProverRandomness n) (E := hvzk₁.SimRandomness n)
        (fun r₁ simC s₀ =>
          f (((hvzk₀.simulate n y.1 simC s₀).1,
              P₁.commit n w₁ y.2 r₁),
             ((hvzk₀.simulate n y.1 simC s₀).2,
              P₁.respond n w₁ y.2 r₁ (challengeEq n ▸ (ch - simC)),
              simC)))
      erw [step1]
      -- Now: E_{(r₁, simC, s₀)}[body] = E_{(s₀', s₁', c₀)}[body']
      -- Step 2: Decompose both sides into individual expectations
      rw [uniformExpect_prod]
      simp_rw [uniformExpect_prod]
      -- Step 3: Swap order on LHS so r₁ is innermost
      rw [uniformExpect_comm]
      simp_rw [uniformExpect_comm (P₁.ProverRandomness n)]
      -- LHS: E_{simC}[E_{s₀}[E_{r₁}[body(r₁, simC, s₀)]]]
      -- Step 4: Apply hvzk₁.sim_distribution to inner E_{r₁}
      conv_lhs =>
        arg 2; ext simC
        arg 2; ext s₀
        erw [hvzk₁.sim_distribution n w₁ y.2
          (challengeEq n ▸ (ch - simC)) hrel₁
          (fun pair =>
            f (((hvzk₀.simulate n y.1 simC s₀).1, pair.1),
               ((hvzk₀.simulate n y.1 simC s₀).2, pair.2,
                simC)))]
      -- LHS: E_{simC}[E_{s₀}[E_{s₁'}[...]]]
      -- Step 5: Reorder to match RHS: E_{s₀'}[E_{s₁'}[E_{c₀}[...]]]
      rw [uniformExpect_comm]
      simp_rw [uniformExpect_comm (P₀.Challenge n)]
      -- Now: E_{s₀}[E_{s₁'}[E_{simC}[...]]] = E_{s₀'}[E_{s₁'}[E_{c₀}[...]]]
      -- Step 6: Bodies are equal pointwise
      congr 1

end
