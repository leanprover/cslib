/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Probability.ForkingLemma
public import Cslib.Cryptography.Foundations.RandomOracle

@[expose] public section

/-!
# Fiat-Shamir ROM Security Reduction

The central security theorem for Fiat-Shamir signatures: if the
underlying Sigma protocol has **special soundness** and **special
HVZK**, and the relation is hard, then the Fiat-Shamir signature
scheme is **EUF-CMA secure** in the **random oracle model**.

## Main Results

* `fiatShamir_ROM_bound` — concrete security bound:
  `ROM-EUF-CMA advantage ≤ √(q · Adv_R + q/|Ch|) + q² · δ`
* `fiatShamirReduction` — the relation solver constructed from the
  EUF-CMA adversary via the forking lemma and special soundness
* `fiatShamir_ROM_secure` — asymptotic security: negligible advantage
  under computational hardness of the relation (`SecureAgainst`),
  super-polynomial challenge space, negligible `δ`-unpredictable
  commitments, and polynomial query bound

## Proof Architecture (Boneh-Shoup §19.6)

The reduction proceeds through a chain of game hops:

### Game-hop chain: ROM → LazyROM → MapGame_Real → MapGame1_HVZK

1. **ROM → LazyROM** (`rom_eq_lazy_rom`): The real ROM game samples
   `Fin q → (Msg × Commitment → Challenge)` (per-step random functions).
   By `uniformExpect_eval_at_point`, evaluating a random function at a
   point is equivalent to sampling a uniform value directly. This
   gives exact equality with the lazy-sampling game that uses
   `Fin q → Challenge` as its randomness.

2. **LazyROM → MapGame_Real** (`lazy_le_mapGame_real`): The lazy ROM
   oracle checks the association-list map before using its fresh
   challenge `ch_i` at signing steps. MapGame_Real always uses `ch_i`
   and inserts into the map without checking. The two games differ
   only when a signing query hits a key already in the map, which
   requires a commitment collision. By the union bound over
   `≤ q²` pairs, the gap is at most `q² · δ`
   (`lazyCommitReuse_bound`, via `lazyPairCommitReuse_pair_bound`).

3. **MapGame_Real → MapGame1_HVZK** (`mapGame_real_eq_mapGame1_hvzk`):
   The real prover `(commit, respond)` and the HVZK simulator produce
   the same marginal distribution at each step (by `sim_distribution`).
   The `runWithState_uniformExpect_oracle_eq` lemma lifts this per-step
   equivalence to the full interaction, giving exact equality.

### Combining the game hops

`rom_eq_mapGame1_hvzk_bound` assembles the chain:
  `ROM.adv ≤ MapGame1_HVZK.adv + q² · δ`

### Forking step: MapGame1_HVZK → relation advantage

In MapGame1_HVZK, the signing oracle uses the HVZK simulator and
does **not** use the witness. The forking lemma (`forking_lemma`)
applied to the adversary's interaction yields the quadratic bound:
  `acc²/q ≤ frk + acc/|Ch|`

When forking succeeds, two accepting transcripts with different
challenges at the same forgery index yield a witness via special
soundness (`forkExtraction_le_advR_map`). Thus `frk ≤ Adv_R(B)`.

Inverting the quadratic gives:
  `acc ≤ √(q · Adv_R(B) + q/|Ch|)`

This is `mapGame1_hvzk_forking_bound`.

### Infrastructure lemmas

The file also develops infrastructure for reasoning about stateful
oracle interactions:

* `run_uniformExpect_oracle_eq` / `runWithState_uniformExpect_oracle_eq`:
  per-step marginal equivalence lifts to full interaction expected values
* `queryAtWithState` / `stateBeforeWithState`: access the `k`-th query
  and the state just before it, enabling prefix-independence arguments
* `queryAtWithState_eq_of_prefix`: changing the oracle at indices `≥ k`
  does not affect the `k`-th query
* `mapGameRealOracle_finalMap_lookup`: traces the forgery key through
  the association list to establish which challenge the final map binds
* `lazy_run_stmt_eq_mapGame_real_run_stmt_of_no_reuse`: conditioned on
  no commitment reuse, the lazy and MapGame_Real runs are identical
* `runWithState_eq_of_oracle_agree_on_trace`: two oracles that agree
  on the actual trace produce the same `runWithState` result

## References

* Boneh-Shoup, *A Graduate Course in Applied Cryptography*, §19.6
* [M. Bellare, G. Neven, *Multi-Signatures in the Plain Public-Key Model
  and a General Forking Lemma*][BellareNeven2006]
-/

open Cslib.Probability

/-- If two oracle families, parameterized by per-step randomness types
`S₁` and `S₂`, produce the same marginal distribution at each step
(for all queries and all test functions), then the expected value of
any function of the `run` result is the same.

This is the key tool for proving that swapping per-step randomness
(e.g., real prover randomness ↔ simulator randomness in HVZK)
preserves the interaction's expected outcome. The proof is by
induction on `fuel`: at each step, we factor the expectation into
the head component (which we swap using `h_marginal`) and the tail
(which we swap using the inductive hypothesis). -/
private theorem run_uniformExpect_oracle_eq
    {Q R A : Type} {S₁ S₂ : Type}
    [Fintype S₁] [Nonempty S₁] [Fintype S₂] [Nonempty S₂]
    (fuel : ℕ)
    (interaction : OracleInteraction Q R A)
    (oracle₁ : Fin fuel → S₁ → Q → R)
    (oracle₂ : Fin fuel → S₂ → Q → R)
    (h_marginal : ∀ (i : Fin fuel) (q : Q) (g : R → ℝ),
      uniformExpect S₁ (fun s => g (oracle₁ i s q)) =
      uniformExpect S₂ (fun s => g (oracle₂ i s q)))
    (f : Option (List Q × A) → ℝ) :
    uniformExpect (Fin fuel → S₁)
      (fun ss => f (interaction.run fuel (fun i => oracle₁ i (ss i)))) =
    uniformExpect (Fin fuel → S₂)
      (fun ss => f (interaction.run fuel (fun i => oracle₂ i (ss i)))) := by
  induction fuel generalizing interaction f with
  | zero =>
    -- Fin 0 → S is a singleton; run at fuel 0 doesn't use the oracle.
    cases interaction with
    | done a =>
      -- run (.done a) 0 _ = some ([], a)
      change uniformExpect _ (fun _ => f (some ([], a))) =
             uniformExpect _ (fun _ => f (some ([], a)))
      rw [uniformExpect_const, uniformExpect_const]
    | query q k =>
      -- run (.query q k) 0 _ = none
      change uniformExpect _ (fun _ => f none) =
             uniformExpect _ (fun _ => f none)
      rw [uniformExpect_const, uniformExpect_const]
  | succ n ih =>
    cases interaction with
    | done a =>
      change uniformExpect _ (fun _ => f (some ([], a))) =
             uniformExpect _ (fun _ => f (some ([], a)))
      rw [uniformExpect_const, uniformExpect_const]
    | query q k =>
      -- Shifted oracles for the IH
      let shifted₁ : Fin n → S₁ → Q → R :=
        fun j => oracle₁ ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
      let shifted₂ : Fin n → S₂ → Q → R :=
        fun j => oracle₂ ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
      have h_shifted : ∀ (j : Fin n) (q' : Q) (g : R → ℝ),
          uniformExpect S₁ (fun s => g (shifted₁ j s q')) =
          uniformExpect S₂ (fun s => g (shifted₂ j s q')) :=
        fun j => h_marginal ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
      -- Post-processing: wraps result with q :: prefix
      let postF : Option (List Q × A) → ℝ := fun result =>
        f (match result with | none => none | some (qs, a) => some (q :: qs, a))
      -- Step 1: Convert Fin(n+1) → S to S × (Fin n → S) using Fin.consEquiv,
      -- then factor with uniformExpect_prod.
      -- LHS conversion
      have lhs_conv :
          uniformExpect (Fin (n + 1) → S₁)
            (fun ss => f (OracleInteraction.run (.query q k) (n + 1)
              (fun i => oracle₁ i (ss i)))) =
          uniformExpect S₁ (fun s₀ =>
            uniformExpect (Fin n → S₁) (fun ss' =>
              postF ((k (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ s₀ q)).run n
                (fun j => shifted₁ j (ss' j))))) := by
        rw [show (fun ss : Fin (n + 1) → S₁ =>
                f (OracleInteraction.run (.query q k) (n + 1)
                  (fun i => oracle₁ i (ss i)))) =
              ((fun p : S₁ × (Fin n → S₁) =>
                postF ((k (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ p.1 q)).run n
                  (fun j => shifted₁ j (p.2 j)))) ∘
              (Fin.consEquiv (fun _ : Fin (n + 1) => S₁)).symm) from by
            funext ss; rfl
          , uniformExpect_congr, uniformExpect_prod]
      -- RHS conversion
      have rhs_conv :
          uniformExpect (Fin (n + 1) → S₂)
            (fun ss => f (OracleInteraction.run (.query q k) (n + 1)
              (fun i => oracle₂ i (ss i)))) =
          uniformExpect S₂ (fun s₀ =>
            uniformExpect (Fin n → S₂) (fun ss' =>
              postF ((k (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ s₀ q)).run n
                (fun j => shifted₂ j (ss' j))))) := by
        rw [show (fun ss : Fin (n + 1) → S₂ =>
                f (OracleInteraction.run (.query q k) (n + 1)
                  (fun i => oracle₂ i (ss i)))) =
              ((fun p : S₂ × (Fin n → S₂) =>
                postF ((k (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ p.1 q)).run n
                  (fun j => shifted₂ j (p.2 j)))) ∘
              (Fin.consEquiv (fun _ : Fin (n + 1) => S₂)).symm) from by
            funext ss; rfl
          , uniformExpect_congr, uniformExpect_prod]
      rw [lhs_conv, rhs_conv]
      -- Step 2: Apply IH to rewrite inner expectation
      -- For each s₀, the inner expectation over Fin n → S₁ equals Fin n → S₂
      conv_lhs =>
        arg 2; ext s₀
        rw [ih (k (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ s₀ q)) shifted₁ shifted₂
          h_shifted postF]
      -- Step 3: Apply h_marginal for the outer expectation
      -- Goal: E_{s₀:S₁}[G(oracle₁ 0 s₀ q)] = E_{s₀:S₂}[G(oracle₂ 0 s₀ q)]
      exact h_marginal ⟨0, Nat.zero_lt_succ n⟩ q
        (fun r => uniformExpect (Fin n → S₂) (fun ss' =>
          postF ((k r).run n (fun j => shifted₂ j (ss' j)))))

/-- Stateful version of `run_uniformExpect_oracle_eq`. If two oracle
families, parameterized by per-step randomness types `S₁` and `S₂` and
threading state of type `State`, produce the same marginal distribution
at each step (for all states, queries, and test functions), then the
expected value of any function of the `runWithState` result is the same.

The proof mirrors `run_uniformExpect_oracle_eq` by induction on `fuel`. -/
private theorem runWithState_uniformExpect_oracle_eq
    {Q R A State : Type} {S₁ S₂ : Type}
    [Fintype S₁] [Nonempty S₁] [Fintype S₂] [Nonempty S₂]
    (fuel : ℕ)
    (interaction : OracleInteraction Q R A)
    (oracle₁ : Fin fuel → S₁ → State → Q → (R × State))
    (oracle₂ : Fin fuel → S₂ → State → Q → (R × State))
    (h_marginal : ∀ (i : Fin fuel) (st : State) (q : Q)
      (g : R × State → ℝ),
      uniformExpect S₁ (fun s => g (oracle₁ i s st q)) =
      uniformExpect S₂ (fun s => g (oracle₂ i s st q)))
    (initState : State)
    (f : Option (List Q × A × State) → ℝ) :
    uniformExpect (Fin fuel → S₁)
      (fun ss => f (interaction.runWithState fuel
        (fun i st q => oracle₁ i (ss i) st q) initState)) =
    uniformExpect (Fin fuel → S₂)
      (fun ss => f (interaction.runWithState fuel
        (fun i st q => oracle₂ i (ss i) st q) initState)) := by
  induction fuel generalizing interaction initState f with
  | zero =>
    cases interaction with
    | done a =>
      change uniformExpect _ (fun _ => f (some ([], a, initState))) =
             uniformExpect _ (fun _ => f (some ([], a, initState)))
      rw [uniformExpect_const, uniformExpect_const]
    | query q k =>
      change uniformExpect _ (fun _ => f none) =
             uniformExpect _ (fun _ => f none)
      rw [uniformExpect_const, uniformExpect_const]
  | succ n ih =>
    cases interaction with
    | done a =>
      change uniformExpect _ (fun _ => f (some ([], a, initState))) =
             uniformExpect _ (fun _ => f (some ([], a, initState)))
      rw [uniformExpect_const, uniformExpect_const]
    | query q k =>
      -- Shifted oracles for the IH
      let shifted₁ : Fin n → S₁ → State → Q → (R × State) :=
        fun j => oracle₁ ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
      let shifted₂ : Fin n → S₂ → State → Q → (R × State) :=
        fun j => oracle₂ ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
      have h_shifted : ∀ (j : Fin n) (st : State) (q' : Q)
          (g : R × State → ℝ),
          uniformExpect S₁ (fun s => g (shifted₁ j s st q')) =
          uniformExpect S₂ (fun s => g (shifted₂ j s st q')) :=
        fun j => h_marginal ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
      -- Post-processing: wraps result with q :: prefix
      let postF : Option (List Q × A × State) → ℝ := fun result =>
        f (match result with
           | none => none
           | some (qs, a, sf) => some (q :: qs, a, sf))
      -- Step 1: Factor Fin(n+1) → S into S × (Fin n → S) via Fin.consEquiv
      -- LHS conversion
      have lhs_conv :
          uniformExpect (Fin (n + 1) → S₁)
            (fun ss => f (OracleInteraction.runWithState (.query q k) (n + 1)
              (fun i st q' => oracle₁ i (ss i) st q') initState)) =
          uniformExpect S₁ (fun s₀ =>
            uniformExpect (Fin n → S₁) (fun ss' =>
              postF ((k (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ s₀ initState q).1).runWithState n
                (fun j st q' => shifted₁ j (ss' j) st q')
                (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ s₀ initState q).2))) := by
        rw [show (fun ss : Fin (n + 1) → S₁ =>
                f (OracleInteraction.runWithState (.query q k) (n + 1)
                  (fun i st q' => oracle₁ i (ss i) st q') initState)) =
              ((fun p : S₁ × (Fin n → S₁) =>
                postF ((k (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ p.1 initState q).1).runWithState n
                  (fun j st q' => shifted₁ j (p.2 j) st q')
                  (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ p.1 initState q).2)) ∘
              (Fin.consEquiv (fun _ : Fin (n + 1) => S₁)).symm) from by
            funext ss; rfl
          , uniformExpect_congr, uniformExpect_prod]
      -- RHS conversion
      have rhs_conv :
          uniformExpect (Fin (n + 1) → S₂)
            (fun ss => f (OracleInteraction.runWithState (.query q k) (n + 1)
              (fun i st q' => oracle₂ i (ss i) st q') initState)) =
          uniformExpect S₂ (fun s₀ =>
            uniformExpect (Fin n → S₂) (fun ss' =>
              postF ((k (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ s₀ initState q).1).runWithState n
                (fun j st q' => shifted₂ j (ss' j) st q')
                (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ s₀ initState q).2))) := by
        rw [show (fun ss : Fin (n + 1) → S₂ =>
                f (OracleInteraction.runWithState (.query q k) (n + 1)
                  (fun i st q' => oracle₂ i (ss i) st q') initState)) =
              ((fun p : S₂ × (Fin n → S₂) =>
                postF ((k (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ p.1 initState q).1).runWithState n
                  (fun j st q' => shifted₂ j (p.2 j) st q')
                  (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ p.1 initState q).2)) ∘
              (Fin.consEquiv (fun _ : Fin (n + 1) => S₂)).symm) from by
            funext ss; rfl
          , uniformExpect_congr, uniformExpect_prod]
      rw [lhs_conv, rhs_conv]
      -- Step 2: Apply IH to rewrite inner expectation
      conv_lhs =>
        arg 2; ext s₀
        rw [ih (k (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ s₀ initState q).1)
          shifted₁ shifted₂ h_shifted
          (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ s₀ initState q).2
          postF]
      -- Step 3: Apply h_marginal for the outer expectation
      exact h_marginal ⟨0, Nat.zero_lt_succ n⟩ initState q
        (fun p => uniformExpect (Fin n → S₂) (fun ss' =>
          postF ((k p.1).runWithState n
            (fun j st q' => shifted₂ j (ss' j) st q') p.2)))

/-- **Evaluate-at-point under a uniform random function**:
`E_{H : X → Y}[g(H x₀)] = E_{y : Y}[g(y)]`. -/
private theorem uniformExpect_eval_at_point
    {X Y : Type*} [Fintype X] [Nonempty X] [DecidableEq X]
    [Fintype Y] [Nonempty Y]
    (x₀ : X) (g : Y → ℝ) :
    uniformExpect (X → Y) (fun H => g (H x₀)) =
    uniformExpect Y g := by
  let e := Equiv.funSplitAt x₀ Y
  have h_comp :
      (fun H : X → Y => g (H x₀)) =
      (fun p : Y × ({x : X // x ≠ x₀} → Y) => g p.1) ∘ e := by
    funext H
    simp [e, Equiv.funSplitAt, Equiv.piSplitAt]
  rw [h_comp, uniformExpect_congr]
  exact uniformExpect_prod_ignore_snd g

/-- For a single pair `(i, j)` of distinct indices, the probability (over
uniform prover randomness) that the signing commitments collide is `≤ δ`.
This adapts `uniformExpect_collision_pair` to the `UnpredictableCommitments`
setting: we split `rs` at coordinate `j` via `Equiv.funSplitAt`, fix the
remaining coordinates (which determines the target `t₀ = commit(w, y, rs i)`),
and apply the unpredictability bound. -/
private theorem uniformExpect_commit_collision_pair {R : EffectiveRelation}
    (P : SigmaProtocol R)
    (kg : R.WithKeyGen)
    (n : ℕ) (q : ℕ) (w : R.Witness n)
    (δ : ℕ → ℝ)
    (h_unpred : P.UnpredictableCommitments δ)
    [inst_ft : Fintype (P.ProverRandomness n)]
    [inst_ne : Nonempty (P.ProverRandomness n)]
    (i j : Fin q) (hij : i ≠ j) :
    uniformExpect (Fin q → P.ProverRandomness n)
      (fun rs => if P.commit n w (kg.keyOf n w) (rs i) =
        P.commit n w (kg.keyOf n w) (rs j) then (1 : ℝ) else 0) ≤ δ n := by
  -- Align instances with the protocol's canonical instances so h_unpred applies
  have h_ft : inst_ft = P.proverRandomnessFintype n := Subsingleton.elim _ _
  have h_ne : inst_ne = P.proverRandomnessNonempty n := Subsingleton.elim _ _
  subst h_ft; subst h_ne
  -- Split at coordinate j: (Fin q → PR) ≃ PR × ({k // k ≠ j} → PR)
  -- Flip equality direction so it matches UnpredictableCommitments (commit(rj) = t₀)
  have h_comp : (fun rs : Fin q → P.ProverRandomness n =>
      if P.commit n w (kg.keyOf n w) (rs i) =
        P.commit n w (kg.keyOf n w) (rs j) then (1 : ℝ) else 0) =
    (fun p : P.ProverRandomness n × ({k : Fin q // k ≠ j} → P.ProverRandomness n) =>
      if P.commit n w (kg.keyOf n w) p.1 =
        P.commit n w (kg.keyOf n w) (p.2 ⟨i, hij⟩) then 1 else 0) ∘
    Equiv.funSplitAt j (P.ProverRandomness n) := by
    ext rs; simp [Equiv.funSplitAt, Equiv.piSplitAt, eq_comm]
  rw [h_comp, uniformExpect_congr]
  haveI : Nonempty ({k : Fin q // k ≠ j} → P.ProverRandomness n) :=
    ⟨fun _ => (P.proverRandomnessNonempty n).some⟩
  rw [uniformExpect_prod, uniformExpect_comm]
  -- E_{rest}[E_{rj}[1{commit(rj) = commit(rest[i])}]] ≤ δ
  have h_bound : ∀ rest : {k : Fin q // k ≠ j} → P.ProverRandomness n,
      uniformExpect (P.ProverRandomness n) (fun rj =>
        if P.commit n w (kg.keyOf n w) rj =
          P.commit n w (kg.keyOf n w) (rest ⟨i, hij⟩) then 1 else 0) ≤ δ n :=
    fun rest => h_unpred n w (kg.keyOf n w)
      (P.commit n w (kg.keyOf n w) (rest ⟨i, hij⟩)) (kg.keyOf_valid n w)
  exact le_trans (uniformExpect_mono _ h_bound) (le_of_eq (uniformExpect_const _ _))

/-- The probability that any two signing commitments collide, over uniform
witness and prover randomness, is at most `q² · δ`.

This is the generalized birthday bound for `δ`-unpredictable commitments:
union bound over `≤ q²` pairs, each contributing `≤ δ` by
`uniformExpect_commit_collision_pair`. -/
private theorem commitment_collision_bound {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, Nonempty (Msg n)]
    [∀ n, Fintype (R.Witness n)] [∀ n, Nonempty (R.Witness n)]
    (kg : R.WithKeyGen)
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    (δ : ℕ → ℝ)
    (h_unpred : P.UnpredictableCommitments δ) :
    uniformExpect (R.Witness n × (Fin (A.numQueries n) → P.ProverRandomness n))
      (fun ⟨w, rs⟩ => if ∃ (i j : Fin (A.numQueries n)), i.val < j.val ∧
        P.commit n w (kg.keyOf n w) (rs i) = P.commit n w (kg.keyOf n w) (rs j)
        then 1 else 0) ≤ (A.numQueries n : ℝ) ^ 2 * δ n := by
  let q := A.numQueries n
  letI := P.proverRandomnessFintype n
  letI := P.proverRandomnessNonempty n
  -- Factor: E_{w,rs}[f(w,rs)] = E_w[E_rs[f(w,rs)]]
  rw [uniformExpect_prod]
  -- Per-w bound: E_rs[collision_indicator(w,rs)] ≤ q²·δ
  -- Step 1: Union bound — indicator of ∃ ≤ sum of indicators over pairs
  have h_union : ∀ (w : R.Witness n) (rs : Fin q → P.ProverRandomness n),
      (if ∃ (i j : Fin q), i.val < j.val ∧
        P.commit n w (kg.keyOf n w) (rs i) = P.commit n w (kg.keyOf n w) (rs j)
        then (1 : ℝ) else 0) ≤
      ∑ p : Fin q × Fin q,
        if p.1.val < p.2.val ∧
          P.commit n w (kg.keyOf n w) (rs p.1) = P.commit n w (kg.keyOf n w) (rs p.2)
          then 1 else 0 := by
    intro w rs
    split
    · next h =>
      obtain ⟨i, j, hij, heq⟩ := h
      let f : Fin q × Fin q → ℝ := fun p =>
        if p.1.val < p.2.val ∧
          P.commit n w (kg.keyOf n w) (rs p.1) =
          P.commit n w (kg.keyOf n w) (rs p.2) then 1 else 0
      have hf_nonneg : ∀ p ∈ Finset.univ, (0 : ℝ) ≤ f p :=
        fun p _ => ite_nonneg zero_le_one (le_refl 0)
      have h_single := Finset.single_le_sum hf_nonneg (Finset.mem_univ (i, j))
      have hfi : f (i, j) = 1 := if_pos ⟨hij, heq⟩
      linarith
    · exact Finset.sum_nonneg fun p _ =>
        show (0 : ℝ) ≤ _ from ite_nonneg zero_le_one (le_refl 0)
  -- Step 2: Per-pair bound ≤ δ
  have h_pair_bound : ∀ (w : R.Witness n) (p : Fin q × Fin q),
      uniformExpect (Fin q → P.ProverRandomness n) (fun rs =>
        if p.1.val < p.2.val ∧
          P.commit n w (kg.keyOf n w) (rs p.1) = P.commit n w (kg.keyOf n w) (rs p.2)
          then (1 : ℝ) else 0) ≤ δ n := by
    intro w ⟨i, j⟩
    by_cases hij : i.val < j.val
    · simp only [hij, true_and]
      exact uniformExpect_commit_collision_pair P kg n q w δ
        h_unpred i j (Fin.ne_of_lt hij)
    · have : (fun rs : Fin q → P.ProverRandomness n =>
          if i.val < j.val ∧
            P.commit n w (kg.keyOf n w) (rs i) = P.commit n w (kg.keyOf n w) (rs j)
            then (1 : ℝ) else 0) = fun _ => 0 := by
        ext rs; simp [hij]
      rw [this, uniformExpect_const]
      exact le_trans (le_refl 0) (le_trans
        (uniformExpect_nonneg _ fun _ => ite_nonneg zero_le_one (le_refl 0))
        (h_unpred n w (kg.keyOf n w)
          (P.commit n w (kg.keyOf n w) (‹Nonempty (P.ProverRandomness n)›.some))
          (kg.keyOf_valid n w)))
  -- Step 3: Assemble
  have h_per_w : ∀ w : R.Witness n,
      uniformExpect (Fin q → P.ProverRandomness n) (fun rs =>
        if ∃ (i j : Fin q), i.val < j.val ∧
          P.commit n w (kg.keyOf n w) (rs i) = P.commit n w (kg.keyOf n w) (rs j)
          then (1 : ℝ) else 0) ≤ (q : ℝ) ^ 2 * δ n := by
    intro w
    calc uniformExpect (Fin q → P.ProverRandomness n) (fun rs =>
          if ∃ (i j : Fin q), i.val < j.val ∧
            P.commit n w (kg.keyOf n w) (rs i) = P.commit n w (kg.keyOf n w) (rs j)
            then (1 : ℝ) else 0)
      ≤ uniformExpect (Fin q → P.ProverRandomness n) (fun rs =>
            ∑ p : Fin q × Fin q,
              if p.1.val < p.2.val ∧
                P.commit n w (kg.keyOf n w) (rs p.1) = P.commit n w (kg.keyOf n w) (rs p.2)
                then 1 else 0) :=
          uniformExpect_mono _ (h_union w)
      _ = ∑ p : Fin q × Fin q, uniformExpect (Fin q → P.ProverRandomness n)
              (fun rs => if p.1.val < p.2.val ∧
                P.commit n w (kg.keyOf n w) (rs p.1) = P.commit n w (kg.keyOf n w) (rs p.2)
                then 1 else 0) :=
          uniformExpect_finset_sum _
      _ ≤ ∑ _p : Fin q × Fin q, δ n :=
          Finset.sum_le_sum (fun p _ => h_pair_bound w p)
      _ = (Fintype.card (Fin q × Fin q) : ℝ) * δ n := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ (q : ℝ) ^ 2 * δ n := by
          simp [Fintype.card_prod, Fintype.card_fin]; ring_nf; exact le_refl _
  exact le_trans (uniformExpect_mono _ h_per_w) (le_of_eq (uniformExpect_const _ _))

/-! ## Map-Based Intermediate Games (Boneh-Shoup §19.6)

The following definitions implement the Map-based game hop chain:
- **MapGame0** ≡ ROM (via lazy sampling)
- **MapGame1** differs from MapGame0 only in that signing always uses fresh
  `ch_i` (ignoring Map). Gap bounded by commitment collision probability.
- **MapGame1_HVZK** replaces real prover with HVZK simulator. Same advantage
  as MapGame1 by `sim_distribution`.

The forking lemma is applied to MapGame1_HVZK. -/

/-- Map state type: association list from `(Msg × Commitment)` to `Challenge`. -/
private abbrev MapState {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type) (n : ℕ) :=
  List ((Msg n × P.Commitment n) × P.Challenge n)

/-- Oracle for MapGame_Real: signing uses the real prover (commit/respond)
with per-query challenge `ch_i`, and inserts into Map. Hash oracle checks
Map for consistency. This is the intermediate game between ROM and
MapGame1_HVZK. -/
private noncomputable def mapGameRealOracle {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    (n : ℕ) (q : ℕ)
    (w : R.Witness n) (y : R.Statement n)
    (rs : Fin q → P.ProverRandomness n)
    (ch : Fin q → P.Challenge n) :
    Fin q → MapState P Msg n →
      (Msg n ⊕ (Msg n × P.Commitment n)) →
      (((P.Commitment n × P.Response n) ⊕ P.Challenge n) × MapState P Msg n) :=
  fun i map qry =>
    letI := P.commitmentDecEq n
    match qry with
    | .inl m =>
      let t := P.commit n w y (rs i)
      let z := P.respond n w y (rs i) (ch i)
      (.inl (t, z), ((m, t), ch i) :: map)
    | .inr (m, t) =>
      match assocLookup (m, t) map with
      | some c => (.inr c, map)
      | none => (.inr (ch i), ((m, t), ch i) :: map)

/-- Execute MapGame_Real: run the adversary with the Map-based real oracle,
then post-process to extract forgery and check verification. -/
private noncomputable def mapGame_real_run_stmt {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    (w : R.Witness n) (y : R.Statement n)
    (rs : Fin (A.numQueries n) → P.ProverRandomness n)
    (ch : Fin (A.numQueries n) → P.Challenge n) :
    Option (Fin (A.numQueries n) × (Msg n × P.Commitment n × P.Response n)) :=
  let q := A.numQueries n
  letI := P.commitmentDecEq n
  match (A.interact n y).runWithState q
      (mapGameRealOracle P Msg n q w y rs ch) [] with
  | none => none
  | some (queries, (mf, tf, zf), _) =>
    let j := queries.findIdx (fun x => decide (x = .inr (mf, tf)))
    if hj : j < q then
      if j < queries.length then
        let signMsgs := queries.filterMap (fun q => match q with
          | .inl m => some m | .inr _ => none)
        if P.verify n y tf (ch ⟨j, hj⟩) zf && !(signMsgs.contains mf) then
          some (⟨j, hj⟩, (mf, tf, zf))
        else
          none
      else
        none
    else
      none

/-- Wrap `mapGame_real_run_stmt` for the `forkAcceptProb` framework. -/
private noncomputable def mapGame_real_run {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    (kg : R.WithKeyGen)
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ) :
    (R.Witness n × (Fin (A.numQueries n) → P.ProverRandomness n)) →
    (Fin (A.numQueries n) → P.Challenge n) →
    Option (Fin (A.numQueries n) × (Msg n × P.Commitment n × P.Response n)) :=
  fun ⟨w, rs⟩ ch =>
    mapGame_real_run_stmt P Msg A n w (kg.keyOf n w) rs ch

/-- **MapGame_Real advantage**: acceptance probability of the Map-based
real-prover game in the forking framework. -/
private noncomputable def mapGame_real_advantage {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    [∀ n, Fintype (R.Witness n)] [∀ n, Nonempty (R.Witness n)]
    (kg : R.WithKeyGen)
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ) : ℝ :=
  let q := A.numQueries n
  letI := P.proverRandomnessFintype n
  letI := P.proverRandomnessNonempty n
  letI := P.challengeFintype n
  letI := P.challengeNonempty n
  forkAcceptProb
    (R.Witness n × (Fin q → P.ProverRandomness n))
    (P.Challenge n) q
    (mapGame_real_run P Msg kg A n)

/-- Oracle for LazyROM (= MapGame0 in Boneh-Shoup §19.6): like
`mapGameRealOracle` but checks the Map at signing steps before using
`ch_i`. When the key `(m, commit(w,y,rs_i))` is already cached, uses
the cached challenge for consistency (faithfully simulating a random
function). When the key is fresh, behaves identically to
`mapGameRealOracle`. -/
private noncomputable def lazyRomOracle {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    (n : ℕ) (q : ℕ)
    (w : R.Witness n) (y : R.Statement n)
    (rs : Fin q → P.ProverRandomness n)
    (ch : Fin q → P.Challenge n) :
    Fin q → MapState P Msg n →
      (Msg n ⊕ (Msg n × P.Commitment n)) →
      (((P.Commitment n × P.Response n) ⊕ P.Challenge n) × MapState P Msg n) :=
  fun i map qry =>
    letI := P.commitmentDecEq n
    match qry with
    | .inl m =>
      let t := P.commit n w y (rs i)
      match assocLookup (m, t) map with
      | some c => (.inl (t, P.respond n w y (rs i) c), map)
      | none => (.inl (t, P.respond n w y (rs i) (ch i)),
                 ((m, t), ch i) :: map)
    | .inr (m, t) =>
      match assocLookup (m, t) map with
      | some c => (.inr c, map)
      | none => (.inr (ch i), ((m, t), ch i) :: map)

/-- LazyROM oracle variant where each step receives a random function
`Hᵢ : Msg × Comm → Ch` and uses `Hᵢ(key)` when the key is fresh.
Map lookups still enforce consistency on repeated keys. -/
private noncomputable def lazyRomHOracle {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    (n : ℕ) (q : ℕ)
    (w : R.Witness n) (y : R.Statement n)
    (rs : Fin q → P.ProverRandomness n) :
    Fin q → (Msg n × P.Commitment n → P.Challenge n) →
      MapState P Msg n →
      (Msg n ⊕ (Msg n × P.Commitment n)) →
      (((P.Commitment n × P.Response n) ⊕ P.Challenge n) × MapState P Msg n) :=
  fun i H map qry =>
    letI := P.commitmentDecEq n
    match qry with
    | .inl m =>
      let t := P.commit n w y (rs i)
      match assocLookup (m, t) map with
      | some c => (.inl (t, P.respond n w y (rs i) c), map)
      | none =>
        let c := H (m, t)
        (.inl (t, P.respond n w y (rs i) c), ((m, t), c) :: map)
    | .inr (m, t) =>
      match assocLookup (m, t) map with
      | some c => (.inr c, map)
      | none =>
        let c := H (m, t)
        (.inr c, ((m, t), c) :: map)

/-- One-step marginal equivalence:
sampling a fresh value via `Hᵢ(key)` (uniform random function) matches
sampling a fresh uniform challenge directly. -/
private theorem lazyRomHOracle_marginal_eq {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    [∀ n, Fintype (Msg n)] [∀ n, Nonempty (Msg n)]
    (n : ℕ) (q : ℕ)
    (w : R.Witness n) (y : R.Statement n)
    (rs : Fin q → P.ProverRandomness n)
    (i : Fin q) (map : MapState P Msg n)
    (qry : Msg n ⊕ (Msg n × P.Commitment n))
    (g : (((P.Commitment n × P.Response n) ⊕ P.Challenge n) ×
      MapState P Msg n) → ℝ) :
    uniformExpect (Msg n × P.Commitment n → P.Challenge n)
      (fun H => g (lazyRomHOracle P Msg n q w y rs i H map qry)) =
    uniformExpect (P.Challenge n)
      (fun c => g (lazyRomOracle P Msg n q w y rs (fun _ => c) i map qry)) := by
  letI := P.commitmentDecEq n
  cases qry with
  | inl m =>
    let t := P.commit n w y (rs i)
    cases h_lookup : assocLookup (m, t) map with
    | some c0 =>
      simpa [lazyRomHOracle, lazyRomOracle, t, h_lookup] using
        (show uniformExpect (Msg n × P.Commitment n → P.Challenge n)
            (fun _ => g (.inl (t, P.respond n w y (rs i) c0), map)) =
          uniformExpect (P.Challenge n)
            (fun _ => g (.inl (t, P.respond n w y (rs i) c0), map)) from by
          rw [uniformExpect_const, uniformExpect_const])
    | none =>
      let g' : P.Challenge n → ℝ := fun c =>
        g (.inl (t, P.respond n w y (rs i) c), ((m, t), c) :: map)
      have h_eval :=
        uniformExpect_eval_at_point (x₀ := (m, t)) (g := g')
      simpa [lazyRomHOracle, lazyRomOracle, t, h_lookup, g'] using h_eval
  | inr mt =>
    rcases mt with ⟨m, t⟩
    cases h_lookup : assocLookup (m, t) map with
    | some c0 =>
      simpa [lazyRomHOracle, lazyRomOracle, h_lookup] using
        (show uniformExpect (Msg n × P.Commitment n → P.Challenge n)
            (fun _ => g (.inr c0, map)) =
          uniformExpect (P.Challenge n)
            (fun _ => g (.inr c0, map)) from by
          rw [uniformExpect_const, uniformExpect_const])
    | none =>
      let g' : P.Challenge n → ℝ := fun c => g (.inr c, ((m, t), c) :: map)
      have h_eval :=
        uniformExpect_eval_at_point (x₀ := (m, t)) (g := g')
      simpa [lazyRomHOracle, lazyRomOracle, h_lookup, g'] using h_eval

/-- Run-level oracle swap for LazyROM:
replacing per-step random functions `Hᵢ` with per-step uniform challenges
preserves the expected value of any post-processing of `runWithState`. -/
private theorem lazyRomH_runWithState_uniform_eq {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    [∀ n, Fintype (Msg n)] [∀ n, Nonempty (Msg n)]
    (n : ℕ) (q : ℕ)
    (interaction : OracleInteraction
      (Msg n ⊕ (Msg n × P.Commitment n))
      ((P.Commitment n × P.Response n) ⊕ P.Challenge n)
      (Msg n × P.Commitment n × P.Response n))
    (w : R.Witness n) (y : R.Statement n)
    (rs : Fin q → P.ProverRandomness n)
    (f : Option
      (List (Msg n ⊕ (Msg n × P.Commitment n)) ×
        (Msg n × P.Commitment n × P.Response n) ×
        MapState P Msg n) → ℝ) :
    uniformExpect (Fin q → (Msg n × P.Commitment n → P.Challenge n))
      (fun Hs =>
        f (interaction.runWithState q
          (fun i st qry => lazyRomHOracle P Msg n q w y rs i (Hs i) st qry) [])) =
    uniformExpect (Fin q → P.Challenge n)
      (fun ch =>
        f (interaction.runWithState q
          (lazyRomOracle P Msg n q w y rs ch) [])) := by
  have h_oracle_lazy :
      ∀ (ch : Fin q → P.Challenge n),
        lazyRomOracle P Msg n q w y rs ch =
        fun i st qry => (fun i s st qry =>
          lazyRomOracle P Msg n q w y rs (fun _ => s) i st qry) i (ch i) st qry := by
    intro ch
    funext i st qry
    rfl
  conv_rhs =>
    arg 2
    ext ch
    rw [h_oracle_lazy ch]
    dsimp only []
  exact runWithState_uniformExpect_oracle_eq q interaction
    (fun i s => lazyRomHOracle P Msg n q w y rs i s)
    (fun i s => lazyRomOracle P Msg n q w y rs (fun _ => s) i)
    (by
      intro i st qry g
      exact lazyRomHOracle_marginal_eq P Msg n q w y rs i st qry g)
    [] f

/-- Execute LazyROM: run the adversary with the lazy ROM oracle,
then post-process to extract forgery and check verification.
Mirrors `mapGame_real_run_stmt` exactly, substituting `lazyRomOracle`
for `mapGameRealOracle`. -/
private noncomputable def lazyRom_run_stmt {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    (w : R.Witness n) (y : R.Statement n)
    (rs : Fin (A.numQueries n) → P.ProverRandomness n)
    (ch : Fin (A.numQueries n) → P.Challenge n) :
    Option (Fin (A.numQueries n) × (Msg n × P.Commitment n × P.Response n)) :=
  let q := A.numQueries n
  letI := P.commitmentDecEq n
  match (A.interact n y).runWithState q
      (lazyRomOracle P Msg n q w y rs ch) [] with
  | none => none
  | some (queries, (mf, tf, zf), finalMap) =>
    let j := queries.findIdx (fun x => decide (x = .inr (mf, tf)))
    if hj : j < q then
      let signMsgs := queries.filterMap (fun q => match q with
        | .inl m => some m | .inr _ => none)
      match assocLookup (mf, tf) finalMap with
      | some c =>
        if P.verify n y tf c zf && !(signMsgs.contains mf) then
          some (⟨j, hj⟩, (mf, tf, zf))
        else
          none
      | none => none
    else
      none

/-- Wrap `lazyRom_run_stmt` for the `forkAcceptProb` framework. -/
private noncomputable def lazyRom_run {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    (kg : R.WithKeyGen)
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ) :
    (R.Witness n × (Fin (A.numQueries n) → P.ProverRandomness n)) →
    (Fin (A.numQueries n) → P.Challenge n) →
    Option (Fin (A.numQueries n) × (Msg n × P.Commitment n × P.Response n)) :=
  fun ⟨w, rs⟩ ch =>
    lazyRom_run_stmt P Msg A n w (kg.keyOf n w) rs ch

/-- **LazyROM advantage**: acceptance probability of the lazy ROM game
in the forking framework. -/
private noncomputable def lazyRom_advantage {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    [∀ n, Fintype (R.Witness n)] [∀ n, Nonempty (R.Witness n)]
    (kg : R.WithKeyGen)
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ) : ℝ :=
  let q := A.numQueries n
  letI := P.proverRandomnessFintype n
  letI := P.proverRandomnessNonempty n
  letI := P.challengeFintype n
  letI := P.challengeNonempty n
  forkAcceptProb
    (R.Witness n × (Fin q → P.ProverRandomness n))
    (P.Challenge n) q
    (lazyRom_run P Msg kg A n)

/-- Oracle for MapGame1_HVZK: signing uses HVZK simulator, always uses
`ch_i`, and inserts into Map. Hash oracle checks Map for consistency. -/
private noncomputable def mapGame1HvzkOracle {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    (hvzk : P.SpecialHVZK) (n : ℕ) (q : ℕ)
    (y : R.Statement n)
    (sr : Fin q → hvzk.SimRandomness n)
    (ch : Fin q → P.Challenge n) :
    Fin q → MapState P Msg n →
      (Msg n ⊕ (Msg n × P.Commitment n)) →
      (((P.Commitment n × P.Response n) ⊕ P.Challenge n) × MapState P Msg n) :=
  fun i map qry =>
    letI := P.commitmentDecEq n
    match qry with
    | .inl m =>
      let (t, z) := hvzk.simulate n y (ch i) (sr i)
      (.inl (t, z), ((m, t), ch i) :: map)
    | .inr (m, t) =>
      match assocLookup (m, t) map with
      | some c => (.inr c, map)
      | none => (.inr (ch i), ((m, t), ch i) :: map)

/-- Execute MapGame1_HVZK: run the adversary with the Map-based HVZK oracle,
then post-process to extract forgery and check verification. -/
private noncomputable def mapGame1_hvzk_run_stmt {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    (hvzk : P.SpecialHVZK)
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    (y : R.Statement n)
    (sr : Fin (A.numQueries n) → hvzk.SimRandomness n)
    (ch : Fin (A.numQueries n) → P.Challenge n) :
    Option (Fin (A.numQueries n) × (Msg n × P.Commitment n × P.Response n)) :=
  let q := A.numQueries n
  letI := P.commitmentDecEq n
  match (A.interact n y).runWithState q
      (mapGame1HvzkOracle P Msg hvzk n q y sr ch) [] with
  | none => none
  | some (queries, (mf, tf, zf), _) =>
    let j := queries.findIdx (fun x => decide (x = .inr (mf, tf)))
    if hj : j < q then
      if j < queries.length then
        let signMsgs := queries.filterMap (fun q => match q with
          | .inl m => some m | .inr _ => none)
        if P.verify n y tf (ch ⟨j, hj⟩) zf && !(signMsgs.contains mf) then
          some (⟨j, hj⟩, (mf, tf, zf))
        else
          none
      else
        none
    else
      none

/-- Wrap `mapGame1_hvzk_run_stmt` for the `forkAcceptProb` framework. -/
private noncomputable def mapGame1_hvzk_run {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    (kg : R.WithKeyGen)
    (hvzk : P.SpecialHVZK)
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ) :
    (R.Witness n × (Fin (A.numQueries n) → hvzk.SimRandomness n)) →
    (Fin (A.numQueries n) → P.Challenge n) →
    Option (Fin (A.numQueries n) × (Msg n × P.Commitment n × P.Response n)) :=
  fun ⟨w, sr⟩ ch =>
    mapGame1_hvzk_run_stmt P Msg hvzk A n (kg.keyOf n w) sr ch

/-- **MapGame1_HVZK advantage**: acceptance probability of the Map-based
HVZK game in the forking framework. -/
private noncomputable def mapGame1_hvzk_advantage {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    [∀ n, Fintype (R.Witness n)] [∀ n, Nonempty (R.Witness n)]
    (kg : R.WithKeyGen)
    (hvzk : P.SpecialHVZK)
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ) : ℝ :=
  let q := A.numQueries n
  letI := hvzk.simRandomnessFintype n
  letI := hvzk.simRandomnessNonempty n
  letI := P.challengeFintype n
  letI := P.challengeNonempty n
  forkAcceptProb
    (R.Witness n × (Fin q → hvzk.SimRandomness n))
    (P.Challenge n) q
    (mapGame1_hvzk_run P Msg kg hvzk A n)

/-- If two `forkAcceptProb` computations with different coin types produce
the same expected payoff for every challenge assignment, they are equal. -/
private theorem forkAcceptProb_coins_eq
    {α : Type} {C₁ C₂ R : Type}
    [Fintype C₁] [Nonempty C₁] [Fintype C₂] [Nonempty C₂]
    [Fintype R] [Nonempty R] (q : ℕ)
    (run₁ : C₁ → (Fin q → R) → Option (Fin q × α))
    (run₂ : C₂ → (Fin q → R) → Option (Fin q × α))
    (h : ∀ (ch : Fin q → R) (f : Option (Fin q × α) → ℝ),
      uniformExpect C₁ (fun c => f (run₁ c ch)) =
      uniformExpect C₂ (fun c => f (run₂ c ch))) :
    forkAcceptProb C₁ R q run₁ = forkAcceptProb C₂ R q run₂ := by
  simp only [forkAcceptProb]
  conv_lhs => rw [uniformExpect_prod, uniformExpect_comm]
  conv_rhs => rw [uniformExpect_prod, uniformExpect_comm]
  congr 1; ext ch
  exact h ch (fun o => match o with | none => 0 | some _ => 1)

/-- **HVZK switch**: the MapGame_Real advantage equals the MapGame1_HVZK
advantage. The real prover `(commit, respond)` produces the same marginal
distribution as the HVZK simulator at each step (by `sim_distribution`),
so the overall interaction's expected payoff is preserved. -/
private theorem mapGame_real_eq_mapGame1_hvzk {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    [∀ n, Fintype (R.Witness n)] [∀ n, Nonempty (R.Witness n)]
    (kg : R.WithKeyGen)
    (hvzk : P.SpecialHVZK)
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ) :
    mapGame_real_advantage P Msg kg A n =
    mapGame1_hvzk_advantage P Msg kg hvzk A n := by
  set q := A.numQueries n with hq
  letI := P.proverRandomnessFintype n
  letI := P.proverRandomnessNonempty n
  letI := hvzk.simRandomnessFintype n
  letI := hvzk.simRandomnessNonempty n
  letI := P.challengeFintype n
  letI := P.challengeNonempty n
  simp only [mapGame_real_advantage, mapGame1_hvzk_advantage]
  apply forkAcceptProb_coins_eq
  intro ch f_payoff
  simp only [mapGame_real_run, mapGame1_hvzk_run]
  rw [uniformExpect_prod, uniformExpect_prod]
  congr 1; ext w; dsimp only []
  -- For fixed w and ch, show the inner expectations over per-step randomness are equal
  set y := kg.keyOf n w
  -- Post-processing function applied after runWithState (same in both games)
  let pp : Option (List (Msg n ⊕ (Msg n × P.Commitment n)) ×
      (Msg n × P.Commitment n × P.Response n) × MapState P Msg n) →
      Option (Fin q × (Msg n × P.Commitment n × P.Response n)) :=
    fun result =>
    letI := P.commitmentDecEq n
    match result with
    | none => none
    | some (queries, (mf, tf, zf), _) =>
      let j := queries.findIdx (fun x => decide (x = Sum.inr (mf, tf)))
      if hj : j < q then
        if j < queries.length then
          let signMsgs := queries.filterMap (fun q => match q with
            | Sum.inl m => some m | Sum.inr _ => none)
          if P.verify n y tf (ch ⟨j, hj⟩) zf && !(signMsgs.contains mf) then
            some (⟨j, hj⟩, (mf, tf, zf))
          else none
        else none
      else none
  -- Factoring: run_stmt = pp ∘ runWithState ∘ oracle
  have h_run_real : ∀ rs,
      mapGame_real_run_stmt P Msg A n w y rs ch =
      pp ((A.interact n y).runWithState q (mapGameRealOracle P Msg n q w y rs ch) []) := by
    intro rs; rfl
  have h_run_hvzk : ∀ sr,
      mapGame1_hvzk_run_stmt P Msg hvzk A n y sr ch =
      pp ((A.interact n y).runWithState q (mapGame1HvzkOracle P Msg hvzk n q y sr ch) []) := by
    intro sr; rfl
  -- Oracle factoring: oracle(rs)(i) = oracle₁(i)(rs i) where oracle₁ doesn't depend on rs
  have h_oracle_real : ∀ (rs : Fin q → P.ProverRandomness n),
      mapGameRealOracle P Msg n q w y rs ch =
      fun i st qry => (fun i s st qry =>
        mapGameRealOracle P Msg n q w y (fun _ => s) ch i st qry) i (rs i) st qry := by
    intro rs; funext i st qry; rfl
  have h_oracle_hvzk : ∀ (sr : Fin q → hvzk.SimRandomness n),
      mapGame1HvzkOracle P Msg hvzk n q y sr ch =
      fun i st qry => (fun i s st qry =>
        mapGame1HvzkOracle P Msg hvzk n q y (fun _ => s) ch i st qry) i (sr i) st qry := by
    intro sr; funext i st qry; rfl
  conv_lhs => arg 2; ext rs; rw [h_run_real, h_oracle_real]; dsimp only []
  conv_rhs => arg 2; ext sr; rw [h_run_hvzk, h_oracle_hvzk]; dsimp only []
  -- Normalize Fin (A.numQueries n) to Fin q for unification
  change uniformExpect (Fin q → P.ProverRandomness n) (fun rs =>
      f_payoff (pp ((A.interact n y).runWithState q
        (fun i st qry => mapGameRealOracle P Msg n q w y (fun _ => rs i) ch i st qry) []))) =
    uniformExpect (Fin q → hvzk.SimRandomness n) (fun sr =>
      f_payoff (pp ((A.interact n y).runWithState q
        (fun i st qry => mapGame1HvzkOracle P Msg hvzk n q y (fun _ => sr i) ch i st qry) [])))
  -- Apply the stateful oracle swap lemma
  exact runWithState_uniformExpect_oracle_eq q (A.interact n y)
    (fun i s => mapGameRealOracle P Msg n q w y (fun _ => s) ch i)
    (fun i s => mapGame1HvzkOracle P Msg hvzk n q y (fun _ => s) ch i)
    (by
      intro i st qry g
      cases qry with
      | inr mt =>
        -- Hash query: result is independent of per-step randomness s
        simp only [mapGameRealOracle, mapGame1HvzkOracle]
        rw [uniformExpect_const, uniformExpect_const]
      | inl m =>
        -- Sign query: real prover ↔ HVZK simulator by sim_distribution
        simp only [mapGameRealOracle, mapGame1HvzkOracle]
        exact hvzk.sim_distribution n w y (ch i) (kg.keyOf_valid n w)
          (fun ⟨t, z⟩ => g (Sum.inl (t, z), ((m, t), ch i) :: st)))
    [] (fun result => f_payoff (pp result))

/-- Return the `idx`-th query issued by a stateful interaction, if it exists,
without requiring the whole `runWithState` call to terminate successfully.

This is useful for prefix-dependence arguments: `queryAtWithState ... idx`
only depends on oracle indices `< idx + 1`. -/
private def queryAtWithState {Q R A S : Type}
    : (interaction : OracleInteraction Q R A) →
      (fuel : Nat) →
      (oracle : Fin fuel → S → Q → R × S) →
      (initState : S) →
      (idx : Nat) →
      Option Q
  | .done _, _, _, _, _ => none
  | .query _ _, 0, _, _, _ => none
  | .query q k, fuel + 1, oracle, s, idx =>
    match idx with
    | 0 => some q
    | idx + 1 =>
      let (response, s') := oracle ⟨0, Nat.zero_lt_succ fuel⟩ s q
      let shiftedOracle : Fin fuel → S → Q → R × S :=
        fun i => oracle ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
      queryAtWithState (k response) fuel shiftedOracle s' idx

/-- State just before processing query `idx` (if that query exists), for a
stateful interaction run with fixed fuel and oracle. -/
private def stateBeforeWithState {Q R A S : Type}
    : (interaction : OracleInteraction Q R A) →
      (fuel : Nat) →
      (oracle : Fin fuel → S → Q → R × S) →
      (initState : S) →
      (idx : Nat) →
      Option S
  | .done _, _, _, s, 0 => some s
  | .done _, _, _, _, _ + 1 => none
  | .query _ _, 0, _, s, 0 => some s
  | .query _ _, 0, _, _, _ + 1 => none
  | .query _ _, _fuel + 1, _, s, 0 => some s
  | .query q k, fuel + 1, oracle, s, idx + 1 =>
    let (response, s') := oracle ⟨0, Nat.zero_lt_succ fuel⟩ s q
    let shiftedOracle : Fin fuel → S → Q → R × S :=
      fun i => oracle ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
    stateBeforeWithState (k response) fuel shiftedOracle s' idx

/-- `queryAtWithState` depends only on the oracle prefix `≤ idx`. -/
private theorem queryAtWithState_eq_of_prefix
    {Q R A S : Type}
    (interaction : OracleInteraction Q R A)
    (fuel : Nat)
    (oracle₁ oracle₂ : Fin fuel → S → Q → R × S)
    (s : S)
    (idx : Nat)
    (h_agree : ∀ (i : Fin fuel), i.val < idx → oracle₁ i = oracle₂ i) :
    queryAtWithState interaction fuel oracle₁ s idx =
    queryAtWithState interaction fuel oracle₂ s idx := by
  induction idx generalizing interaction fuel oracle₁ oracle₂ s with
  | zero =>
    cases interaction with
    | done a =>
      cases fuel <;> rfl
    | query q k =>
      cases fuel <;> rfl
  | succ idx ih =>
    cases interaction with
    | done a =>
      cases fuel <;> rfl
    | query q k =>
      cases fuel with
      | zero =>
        rfl
      | succ fuel =>
        simp only [queryAtWithState]
        have h0 : oracle₁ ⟨0, Nat.zero_lt_succ fuel⟩ s q =
            oracle₂ ⟨0, Nat.zero_lt_succ fuel⟩ s q := by
          exact congrFun (congrFun
            (h_agree ⟨0, Nat.zero_lt_succ fuel⟩ (Nat.zero_lt_succ _)) s) q
        let shifted₁ : Fin fuel → S → Q → R × S :=
          fun i => oracle₁ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
        let shifted₂ : Fin fuel → S → Q → R × S :=
          fun i => oracle₂ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
        have h_shift : ∀ (i : Fin fuel), i.val < idx → shifted₁ i = shifted₂ i := by
          intro i hi
          exact h_agree ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ (Nat.succ_lt_succ hi)
        have h_tail := ih
          (k (oracle₁ ⟨0, Nat.zero_lt_succ fuel⟩ s q).1)
          fuel shifted₁ shifted₂
          (oracle₁ ⟨0, Nat.zero_lt_succ fuel⟩ s q).2
          h_shift
        have h_rhs :
            queryAtWithState
              (k (oracle₁ ⟨0, Nat.zero_lt_succ fuel⟩ s q).1)
              fuel shifted₂
              (oracle₁ ⟨0, Nat.zero_lt_succ fuel⟩ s q).2 idx =
            queryAtWithState
              (k (oracle₂ ⟨0, Nat.zero_lt_succ fuel⟩ s q).1)
              fuel shifted₂
              (oracle₂ ⟨0, Nat.zero_lt_succ fuel⟩ s q).2 idx :=
          congrArg
            (fun p : R × S => queryAtWithState (k p.1) fuel shifted₂ p.2 idx) h0
        exact (by
          simpa [shifted₁, shifted₂] using h_tail.trans h_rhs)

/-- If `assocLookup key map = some v`, then the pair `(key, v)` occurs in
the association list. -/
private lemma assocLookup_some_mem {α β : Type} [DecidableEq α]
    (key : α) (map : List (α × β)) (v : β)
    (h : assocLookup key map = some v) :
    (key, v) ∈ map := by
  induction map with
  | nil =>
    simp [assocLookup] at h
  | cons kv rest ih =>
    rcases kv with ⟨k, v'⟩
    by_cases hk : k = key
    · subst hk
      have hv : v' = v := by
        simpa [assocLookup] using h
      subst hv
      exact List.mem_cons.mpr (Or.inl rfl)
    · have hrest : assocLookup key rest = some v := by
        simpa [assocLookup, hk] using h
      exact List.mem_cons.mpr (Or.inr (ih hrest))

/-- The `idx`-th query in the LazyROM interaction. -/
private noncomputable def lazyQueryAt {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    (w : R.Witness n) (y : R.Statement n)
    (rs : Fin (A.numQueries n) → P.ProverRandomness n)
    (ch : Fin (A.numQueries n) → P.Challenge n)
    (idx : Nat) :
    Option (Msg n ⊕ (Msg n × P.Commitment n)) :=
  queryAtWithState (A.interact n y) (A.numQueries n)
    (lazyRomOracle P Msg n (A.numQueries n) w y rs ch) [] idx

/-- LazyROM map state just before query index `idx` (if that query exists). -/
private noncomputable def lazyMapBefore {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    (w : R.Witness n) (y : R.Statement n)
    (rs : Fin (A.numQueries n) → P.ProverRandomness n)
    (ch : Fin (A.numQueries n) → P.Challenge n)
    (idx : Nat) :
    Option (MapState P Msg n) :=
  stateBeforeWithState (A.interact n y) (A.numQueries n)
    (lazyRomOracle P Msg n (A.numQueries n) w y rs ch) [] idx

/-- Prefix-independence for `lazyQueryAt`: changing prover randomness at
indices `≥ idx` does not change the `idx`-th query. -/
private theorem lazyQueryAt_eq_of_rs_prefix {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    (w : R.Witness n) (y : R.Statement n)
    (rs₁ rs₂ : Fin (A.numQueries n) → P.ProverRandomness n)
    (ch : Fin (A.numQueries n) → P.Challenge n)
    (idx : Nat)
    (h_prefix : ∀ i : Fin (A.numQueries n), i.val < idx → rs₁ i = rs₂ i) :
    lazyQueryAt P Msg A n w y rs₁ ch idx =
    lazyQueryAt P Msg A n w y rs₂ ch idx := by
  apply queryAtWithState_eq_of_prefix (interaction := A.interact n y)
  intro i hi
  funext st qry
  cases qry with
  | inr mt =>
    simp [lazyRomOracle]
  | inl m =>
    simp [lazyRomOracle, h_prefix i hi]

/-- Commitment inserted into the LazyROM map at query index `i`, if any.

At a signing query this is `commit(w, y, rs i)`, while at a hash query it is
the queried commitment. -/
private noncomputable def lazyInsertedCommitAt {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    (w : R.Witness n) (y : R.Statement n)
    (rs : Fin (A.numQueries n) → P.ProverRandomness n)
    (ch : Fin (A.numQueries n) → P.Challenge n)
    (i : Fin (A.numQueries n)) :
    Option (P.Commitment n) :=
  match lazyQueryAt P Msg A n w y rs ch i.val with
  | some (.inl _) => some (P.commit n w y (rs i))
  | some (.inr (_, t)) => some t
  | none => none

/-- Pair event at `(i,j)`: the `j`-th query is a signing query and its
commitment matches a commitment already inserted at index `i < j`. -/
private noncomputable def lazyPairCommitReuse {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    (w : R.Witness n) (y : R.Statement n)
    (rs : Fin (A.numQueries n) → P.ProverRandomness n)
    (ch : Fin (A.numQueries n) → P.Challenge n)
    (i j : Fin (A.numQueries n)) : Bool :=
  match lazyInsertedCommitAt P Msg A n w y rs ch i,
      lazyQueryAt P Msg A n w y rs ch j.val with
  | some ti, some (.inl _) =>
      decide (ti = P.commit n w y (rs j))
  | _, _ => false

/-- If two prover-randomness vectors agree on indices `< j`, then for any
`i < j` they induce the same inserted commitment at index `i`. -/
private theorem lazyInsertedCommitAt_eq_of_rs_prefix_lt {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    (w : R.Witness n) (y : R.Statement n)
    (rs₁ rs₂ : Fin (A.numQueries n) → P.ProverRandomness n)
    (ch : Fin (A.numQueries n) → P.Challenge n)
    (i j : Fin (A.numQueries n))
    (hij : i.val < j.val)
    (h_prefix : ∀ k : Fin (A.numQueries n), k.val < j.val → rs₁ k = rs₂ k) :
    lazyInsertedCommitAt P Msg A n w y rs₁ ch i =
    lazyInsertedCommitAt P Msg A n w y rs₂ ch i := by
  unfold lazyInsertedCommitAt
  have hq : lazyQueryAt P Msg A n w y rs₁ ch i.val =
      lazyQueryAt P Msg A n w y rs₂ ch i.val := by
    apply lazyQueryAt_eq_of_rs_prefix
    intro k hk
    exact h_prefix k (lt_trans hk hij)
  rw [hq]
  simp [h_prefix i hij]

/-- Per-pair bound: for `i < j`, the probability that LazyROM has a
commitment reuse at `(i,j)` is at most `δ`. -/
private theorem lazyPairCommitReuse_pair_bound {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    [∀ n, Fintype (R.Witness n)] [∀ n, Nonempty (R.Witness n)]
    (kg : R.WithKeyGen)
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    (δ : ℕ → ℝ)
    (h_unpred : P.UnpredictableCommitments δ)
    (i j : Fin (A.numQueries n))
    (hij : i.val < j.val) :
    uniformExpect
      ((R.Witness n × (Fin (A.numQueries n) → P.ProverRandomness n)) ×
        (Fin (A.numQueries n) → P.Challenge n))
  (fun ⟨⟨w, rs⟩, ch⟩ =>
    if lazyPairCommitReuse P Msg A n w (kg.keyOf n w) rs ch i j then (1 : ℝ) else 0)
  ≤ δ n := by
  classical
  let q := A.numQueries n
  -- Reorder expectations as E_w E_ch E_rs
  have h_reorder :
      uniformExpect ((R.Witness n × (Fin q → P.ProverRandomness n)) ×
        (Fin q → P.Challenge n))
        (fun ⟨⟨w, rs⟩, ch⟩ =>
          if lazyPairCommitReuse P Msg A n w (kg.keyOf n w) rs ch i j then (1 : ℝ) else 0) =
      uniformExpect (R.Witness n) (fun w =>
        uniformExpect (Fin q → P.Challenge n) (fun ch =>
          uniformExpect (Fin q → P.ProverRandomness n) (fun rs =>
            if lazyPairCommitReuse P Msg A n w (kg.keyOf n w) rs ch i j
              then (1 : ℝ) else 0))) := by
    rw [uniformExpect_prod, uniformExpect_prod]
    congr 1
    ext w
    exact uniformExpect_comm
      (Fin q → P.ProverRandomness n) (Fin q → P.Challenge n)
      (fun rs ch =>
        if lazyPairCommitReuse P Msg A n w (kg.keyOf n w) rs ch i j then (1 : ℝ) else 0)
  rw [h_reorder]
  -- Inner bound for fixed (w, ch)
  have h_inner : ∀ (w : R.Witness n) (ch : Fin q → P.Challenge n),
      uniformExpect (Fin q → P.ProverRandomness n) (fun rs =>
        if lazyPairCommitReuse P Msg A n w (kg.keyOf n w) rs ch i j then (1 : ℝ) else 0)
      ≤ δ n := by
    intro w ch
    let y := kg.keyOf n w
    let e := Equiv.funSplitAt j (P.ProverRandomness n)
    let g : (Fin (A.numQueries n) → P.ProverRandomness n) → ℝ := fun rs =>
      if lazyPairCommitReuse P Msg A n w y rs ch i j then (1 : ℝ) else 0
    have h_split :
        uniformExpect (Fin (A.numQueries n) → P.ProverRandomness n) g =
        uniformExpect
          (P.ProverRandomness n × ({k : Fin (A.numQueries n) // k ≠ j} → P.ProverRandomness n))
          (fun p => g (e.symm p)) := by
      have h_tmp := uniformExpect_congr e
        (fun p : P.ProverRandomness n ×
            ({k : Fin (A.numQueries n) // k ≠ j} → P.ProverRandomness n) =>
          g (e.symm p))
      have h_left : ((fun p : P.ProverRandomness n ×
          ({k : Fin (A.numQueries n) // k ≠ j} → P.ProverRandomness n) =>
          g (e.symm p)) ∘ e) = g := by
        funext rs
        exact congrArg g (e.left_inv rs)
      simpa [h_left] using h_tmp
    rw [h_split, uniformExpect_prod]
    rw [uniformExpect_comm]
    -- For each fixed `rest`, the only remaining randomness is `rj`
    have h_rest :
        ∀ rest : {k : Fin (A.numQueries n) // k ≠ j} → P.ProverRandomness n,
        uniformExpect (P.ProverRandomness n) (fun rj =>
          g (e.symm (rj, rest))) ≤ δ n := by
      intro rest
      let r0 : P.ProverRandomness n := (P.proverRandomnessNonempty n).some
      let rs0 : Fin (A.numQueries n) → P.ProverRandomness n := e.symm (r0, rest)
      have h_prefix_of_rj :
          ∀ (rj : P.ProverRandomness n) (k : Fin (A.numQueries n)), k.val < j.val →
            (e.symm (rj, rest)) k = rs0 k := by
        intro rj k hk
        have hk_ne : k ≠ j := Fin.ne_of_lt hk
        have h_left : (e.symm (rj, rest)) k = rest ⟨k, hk_ne⟩ := by
          simp [e, Equiv.funSplitAt, Equiv.piSplitAt, hk_ne]
        have h_right : rs0 k = rest ⟨k, hk_ne⟩ := by
          simp [rs0, e, Equiv.funSplitAt, Equiv.piSplitAt, hk_ne]
        exact h_left.trans h_right.symm
      have hδ_nonneg : 0 ≤ δ n := by
        have htmp := h_unpred n w y (P.commit n w y r0) (kg.keyOf_valid n w)
        exact le_trans (uniformExpect_nonneg _ (fun _ => by split <;> norm_num)) htmp
      cases h_ins0 : lazyInsertedCommitAt P Msg A n w y rs0 ch i with
      | none =>
        have h_point : ∀ rj : P.ProverRandomness n, g (e.symm (rj, rest)) = 0 := by
          intro rj
          have h_ins_rj :
              lazyInsertedCommitAt P Msg A n w y (e.symm (rj, rest)) ch i =
              lazyInsertedCommitAt P Msg A n w y rs0 ch i := by
            apply lazyInsertedCommitAt_eq_of_rs_prefix_lt P Msg A n w y
              (e.symm (rj, rest)) rs0 ch i j hij
            intro k hk
            exact h_prefix_of_rj rj k hk
          unfold g lazyPairCommitReuse
          rw [h_ins_rj, h_ins0]
          simp
        rw [show (fun rj => g (e.symm (rj, rest))) = fun _ => (0 : ℝ) from by
              funext rj; exact h_point rj,
            uniformExpect_const]
        exact hδ_nonneg
      | some ti =>
        cases h_qj0 : lazyQueryAt P Msg A n w y rs0 ch j.val with
        | none =>
          have h_point : ∀ rj : P.ProverRandomness n, g (e.symm (rj, rest)) = 0 := by
            intro rj
            have h_ins_rj :
                lazyInsertedCommitAt P Msg A n w y (e.symm (rj, rest)) ch i =
                lazyInsertedCommitAt P Msg A n w y rs0 ch i := by
              apply lazyInsertedCommitAt_eq_of_rs_prefix_lt P Msg A n w y
                (e.symm (rj, rest)) rs0 ch i j hij
              intro k hk
              exact h_prefix_of_rj rj k hk
            have h_qj_rj :
                lazyQueryAt P Msg A n w y (e.symm (rj, rest)) ch j.val =
                lazyQueryAt P Msg A n w y rs0 ch j.val := by
              apply lazyQueryAt_eq_of_rs_prefix P Msg A n w y
                (e.symm (rj, rest)) rs0 ch j.val
              intro k hk
              exact h_prefix_of_rj rj k hk
            unfold g lazyPairCommitReuse
            rw [h_ins_rj, h_qj_rj, h_qj0]
            simp
          rw [show (fun rj => g (e.symm (rj, rest))) = fun _ => (0 : ℝ) from by
                funext rj; exact h_point rj,
              uniformExpect_const]
          exact hδ_nonneg
        | some qj =>
          cases qj with
          | inr mt =>
            have h_point : ∀ rj : P.ProverRandomness n, g (e.symm (rj, rest)) = 0 := by
              intro rj
              have h_ins_rj :
                  lazyInsertedCommitAt P Msg A n w y (e.symm (rj, rest)) ch i =
                  lazyInsertedCommitAt P Msg A n w y rs0 ch i := by
                apply lazyInsertedCommitAt_eq_of_rs_prefix_lt P Msg A n w y
                  (e.symm (rj, rest)) rs0 ch i j hij
                intro k hk
                exact h_prefix_of_rj rj k hk
              have h_qj_rj :
                  lazyQueryAt P Msg A n w y (e.symm (rj, rest)) ch j.val =
                  lazyQueryAt P Msg A n w y rs0 ch j.val := by
                apply lazyQueryAt_eq_of_rs_prefix P Msg A n w y
                  (e.symm (rj, rest)) rs0 ch j.val
                intro k hk
                exact h_prefix_of_rj rj k hk
              unfold g lazyPairCommitReuse
              rw [h_ins_rj, h_qj_rj, h_qj0]
              simp
            rw [show (fun rj => g (e.symm (rj, rest))) = fun _ => (0 : ℝ) from by
                  funext rj; exact h_point rj,
                uniformExpect_const]
            exact hδ_nonneg
          | inl mj =>
            have h_point : ∀ rj : P.ProverRandomness n,
                g (e.symm (rj, rest)) =
                  (if ti = P.commit n w y rj then (1 : ℝ) else 0) := by
              intro rj
              have h_ins_rj :
                  lazyInsertedCommitAt P Msg A n w y (e.symm (rj, rest)) ch i =
                  lazyInsertedCommitAt P Msg A n w y rs0 ch i := by
                apply lazyInsertedCommitAt_eq_of_rs_prefix_lt P Msg A n w y
                  (e.symm (rj, rest)) rs0 ch i j hij
                intro k hk
                exact h_prefix_of_rj rj k hk
              have h_qj_rj :
                  lazyQueryAt P Msg A n w y (e.symm (rj, rest)) ch j.val =
                  lazyQueryAt P Msg A n w y rs0 ch j.val := by
                apply lazyQueryAt_eq_of_rs_prefix P Msg A n w y
                  (e.symm (rj, rest)) rs0 ch j.val
                intro k hk
                exact h_prefix_of_rj rj k hk
              unfold g lazyPairCommitReuse
              rw [h_ins_rj, h_qj_rj, h_ins0, h_qj0]
              have h_jcoord : (e.symm (rj, rest)) j = rj := by
                simp [e, Equiv.funSplitAt, Equiv.piSplitAt]
              rw [h_jcoord]
              simp [decide_eq_true_eq]
            rw [show (fun rj => g (e.symm (rj, rest))) =
                (fun rj => if ti = P.commit n w y rj then (1 : ℝ) else 0) from by
                  funext rj; exact h_point rj]
            simpa [eq_comm] using h_unpred n w y ti (kg.keyOf_valid n w)
    exact le_trans (uniformExpect_mono _ h_rest) (le_of_eq (uniformExpect_const _ _))
  have h_inner_w : ∀ w : R.Witness n,
      uniformExpect (Fin q → P.Challenge n) (fun ch =>
        uniformExpect (Fin q → P.ProverRandomness n) (fun rs =>
          if lazyPairCommitReuse P Msg A n w (kg.keyOf n w) rs ch i j then (1 : ℝ) else 0))
      ≤ δ n := by
    intro w
    exact le_trans (uniformExpect_mono _ (h_inner w)) (le_of_eq (uniformExpect_const _ _))
  exact le_trans (uniformExpect_mono _ h_inner_w) (le_of_eq (uniformExpect_const _ _))

/-- Union bound over all pairs `(i,j)`: probability of any LazyROM commitment
reuse event is at most `q² · δ`. -/
private theorem lazyCommitReuse_bound {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    [∀ n, Fintype (R.Witness n)] [∀ n, Nonempty (R.Witness n)]
    (kg : R.WithKeyGen)
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    (δ : ℕ → ℝ)
    (h_unpred : P.UnpredictableCommitments δ) :
    uniformExpect
      ((R.Witness n × (Fin (A.numQueries n) → P.ProverRandomness n)) ×
        (Fin (A.numQueries n) → P.Challenge n))
      (fun ⟨⟨w, rs⟩, ch⟩ =>
        if ∃ (i j : Fin (A.numQueries n)), i.val < j.val ∧
            lazyPairCommitReuse P Msg A n w (kg.keyOf n w) rs ch i j
        then (1 : ℝ) else 0)
      ≤ (A.numQueries n : ℝ) ^ 2 * δ n := by
  classical
  let q := A.numQueries n
  have h_union : ∀ (w : R.Witness n) (rs : Fin q → P.ProverRandomness n)
      (ch : Fin q → P.Challenge n),
      (if ∃ (i j : Fin q), i.val < j.val ∧
          lazyPairCommitReuse P Msg A n w (kg.keyOf n w) rs ch i j
        then (1 : ℝ) else 0) ≤
      ∑ p : Fin q × Fin q,
        if p.1.val < p.2.val ∧
            lazyPairCommitReuse P Msg A n w (kg.keyOf n w) rs ch p.1 p.2
        then 1 else 0 := by
    intro w rs ch
    split
    · rename_i h
      obtain ⟨i, j, hij, hpair⟩ := h
      have h_nonneg : ∀ p ∈ (Finset.univ : Finset (Fin q × Fin q)),
          (0 : ℝ) ≤
            (if p.1.val < p.2.val ∧
                lazyPairCommitReuse P Msg A n w (kg.keyOf n w) rs ch p.1 p.2
              then 1 else 0) :=
        fun p _ => ite_nonneg zero_le_one (le_refl 0)
      have h_single := Finset.single_le_sum h_nonneg (Finset.mem_univ (i, j))
      have h_ij :
          (if (i : Fin q).val < j.val ∧
              lazyPairCommitReuse P Msg A n w (kg.keyOf n w) rs ch i j
            then (1 : ℝ) else 0) = 1 := if_pos ⟨hij, hpair⟩
      linarith
    · rename_i hfalse
      exact Finset.sum_nonneg fun p _ => ite_nonneg zero_le_one (le_refl 0)
  have h_pair : ∀ (p : Fin q × Fin q),
      uniformExpect
        ((R.Witness n × (Fin q → P.ProverRandomness n)) × (Fin q → P.Challenge n))
        (fun ⟨⟨w, rs⟩, ch⟩ =>
          if p.1.val < p.2.val ∧
              lazyPairCommitReuse P Msg A n w (kg.keyOf n w) rs ch p.1 p.2
          then (1 : ℝ) else 0) ≤ δ n := by
    intro p
    rcases p with ⟨i, j⟩
    by_cases hij : i.val < j.val
    · have := lazyPairCommitReuse_pair_bound P Msg kg A n δ h_unpred i j hij
      exact le_trans
        (uniformExpect_mono _ (fun ⟨⟨w, rs⟩, ch⟩ => by
          by_cases hpair : lazyPairCommitReuse P Msg A n w (kg.keyOf n w) rs ch i j
          · simp [hij, hpair]
          · simp [hij, hpair]))
        this
    · have h_zero :
          (fun x :
            (R.Witness n × (Fin q → P.ProverRandomness n)) × (Fin q → P.Challenge n) =>
              if i.val < j.val ∧
                  lazyPairCommitReuse P Msg A n x.1.1 (kg.keyOf n x.1.1) x.1.2 x.2 i j
              then (1 : ℝ) else 0) = fun _ => 0 := by
        funext x
        simp [hij]
      rw [h_zero, uniformExpect_const]
      have hδ_nonneg : 0 ≤ δ n := by
        let r0 : P.ProverRandomness n := (P.proverRandomnessNonempty n).some
        have htmp := h_unpred n (Classical.arbitrary (R.Witness n))
          (kg.keyOf n (Classical.arbitrary (R.Witness n)))
          (P.commit n (Classical.arbitrary (R.Witness n))
            (kg.keyOf n (Classical.arbitrary (R.Witness n))) r0)
          (kg.keyOf_valid n (Classical.arbitrary (R.Witness n)))
        exact le_trans (uniformExpect_nonneg _ (fun _ => by split <;> norm_num)) htmp
      exact hδ_nonneg
  calc uniformExpect
        ((R.Witness n × (Fin q → P.ProverRandomness n)) × (Fin q → P.Challenge n))
        (fun ⟨⟨w, rs⟩, ch⟩ =>
          if ∃ (i j : Fin q), i.val < j.val ∧
              lazyPairCommitReuse P Msg A n w (kg.keyOf n w) rs ch i j
          then (1 : ℝ) else 0)
      ≤ uniformExpect
          ((R.Witness n × (Fin q → P.ProverRandomness n)) × (Fin q → P.Challenge n))
          (fun ⟨⟨w, rs⟩, ch⟩ =>
            ∑ p : Fin q × Fin q,
              if p.1.val < p.2.val ∧
                  lazyPairCommitReuse P Msg A n w (kg.keyOf n w) rs ch p.1 p.2
              then 1 else 0) :=
        uniformExpect_mono _ (fun ⟨⟨w, rs⟩, ch⟩ => h_union w rs ch)
    _ = ∑ p : Fin q × Fin q,
          uniformExpect
            ((R.Witness n × (Fin q → P.ProverRandomness n)) × (Fin q → P.Challenge n))
            (fun ⟨⟨w, rs⟩, ch⟩ =>
              if p.1.val < p.2.val ∧
                  lazyPairCommitReuse P Msg A n w (kg.keyOf n w) rs ch p.1 p.2
              then 1 else 0) :=
        uniformExpect_finset_sum _
    _ ≤ ∑ _p : Fin q × Fin q, δ n :=
        Finset.sum_le_sum (fun p _ => h_pair p)
    _ = (Fintype.card (Fin q × Fin q) : ℝ) * δ n := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ (q : ℝ) ^ 2 * δ n := by
        simp [Fintype.card_prod, Fintype.card_fin]; ring_nf; exact le_refl _

/-- Single-step lookup persistence for `mapGameRealOracle`: if `(mf, tf)` is
already in the map and the query is not a signing query for `mf`, the lookup
is preserved. -/
private theorem mapGameRealOracle_lookup_persist {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    (n : ℕ) (q : ℕ)
    (w : R.Witness n) (y : R.Statement n)
    (rs : Fin q → P.ProverRandomness n)
    (ch : Fin q → P.Challenge n)
    (i : Fin q) (map : MapState P Msg n)
    (mf : Msg n) (tf : P.Commitment n) (v : P.Challenge n)
    (qry : Msg n ⊕ (Msg n × P.Commitment n))
    (h_lookup : assocLookup (mf, tf) map = some v)
    (h_not_sign_mf : ∀ m, qry = .inl m → m ≠ mf) :
    assocLookup (mf, tf) (mapGameRealOracle P Msg n q w y rs ch i map qry).2 = some v := by
  letI := P.commitmentDecEq n
  cases qry with
  | inl m =>
    simp only [mapGameRealOracle]
    have hne : m ≠ mf := h_not_sign_mf m rfl
    simp only [assocLookup]
    rw [if_neg (fun h => hne (Prod.mk.inj h).1)]
    exact h_lookup
  | inr mt =>
    simp only [mapGameRealOracle]
    cases hlk : assocLookup (mt.1, mt.2) map with
    | some c => exact h_lookup
    | none =>
      simp only [assocLookup]
      have hne : ¬ ((mt.1, mt.2) = (mf, tf)) := by
        intro heq; rw [Prod.mk.injEq] at heq; rw [heq.1, heq.2] at hlk
        simp [hlk] at h_lookup
      rw [if_neg hne]
      exact h_lookup

/-- The query log produced by `runWithState` has length at most `fuel`. -/
private theorem runWithState_length_le {Q R A S : Type}
    : ∀ (interaction : OracleInteraction Q R A)
        (fuel : Nat) (oracle : Fin fuel → S → Q → R × S)
        (s : S) (queries : List Q) (a : A) (sf : S),
      interaction.runWithState fuel oracle s = some (queries, a, sf) →
      queries.length ≤ fuel := by
  intro interaction fuel
  induction fuel generalizing interaction with
  | zero =>
    intro oracle s queries a sf h
    cases interaction with
    | done _ =>
      change some ([], _, _) = some (queries, a, sf) at h
      obtain ⟨rfl, _, _⟩ := Prod.mk.inj (Option.some.inj h)
      simp
    | query _ _ => exact absurd h nofun
  | succ n ih =>
    intro oracle s queries a sf h
    cases interaction with
    | done _ =>
      change some ([], _, _) = some (queries, a, sf) at h
      obtain ⟨rfl, _, _⟩ := Prod.mk.inj (Option.some.inj h)
      simp
    | query q k =>
      simp only [OracleInteraction.runWithState] at h
      split at h
      · exact absurd h nofun
      · have hinj := Option.some.inj h
        obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj hinj
        simp only [List.length_cons]
        exact Nat.succ_le_succ (ih _ _ _ _ _ _ (by assumption))

/-- `runWithState` final state equals `stateBeforeWithState` at `queries.length`. -/
private theorem runWithState_finalState_eq_stateBeforeWithState {Q R A S : Type}
    : ∀ (interaction : OracleInteraction Q R A)
        (fuel : Nat) (oracle : Fin fuel → S → Q → R × S)
        (s : S) (queries : List Q) (a : A) (sf : S),
      interaction.runWithState fuel oracle s = some (queries, a, sf) →
      stateBeforeWithState interaction fuel oracle s queries.length = some sf := by
  intro interaction fuel
  induction fuel generalizing interaction with
  | zero =>
    intro oracle s queries a sf h
    cases interaction with
    | done a' =>
      simp only [OracleInteraction.runWithState, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _, rfl⟩ := h; simp [stateBeforeWithState]
    | query _ _ =>
      simp only [OracleInteraction.runWithState] at h; contradiction
  | succ fuel ih =>
    intro oracle s queries a sf h
    cases interaction with
    | done a' =>
      simp only [OracleInteraction.runWithState, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _, rfl⟩ := h; simp [stateBeforeWithState]
    | query q k =>
      simp only [OracleInteraction.runWithState] at h
      split at h
      · simp at h
      · next qs' a' hrec =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        simp only [stateBeforeWithState, List.length_cons]
        exact ih _ _ _ _ _ _ hrec

/-- `runWithState` query list entries match `queryAtWithState`. -/
private theorem runWithState_query_eq_queryAtWithState {Q R A S : Type}
    : ∀ (interaction : OracleInteraction Q R A)
        (fuel : Nat) (oracle : Fin fuel → S → Q → R × S)
        (s : S) (queries : List Q) (a : A) (sf : S),
      interaction.runWithState fuel oracle s = some (queries, a, sf) →
      ∀ (idx : Nat) (hlt : idx < queries.length),
        queryAtWithState interaction fuel oracle s idx = some (queries.get ⟨idx, hlt⟩) := by
  intro interaction fuel
  induction fuel generalizing interaction with
  | zero =>
    intro oracle s queries a sf h
    cases interaction with
    | done a' =>
      simp only [OracleInteraction.runWithState, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _, _⟩ := h
      intro idx hlt; simp at hlt
    | query _ _ =>
      simp only [OracleInteraction.runWithState] at h; contradiction
  | succ fuel ih =>
    intro oracle s queries a sf h
    cases interaction with
    | done a' =>
      simp only [OracleInteraction.runWithState, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _, _⟩ := h
      intro idx hlt; simp at hlt
    | query q k =>
      simp only [OracleInteraction.runWithState] at h
      split at h
      · simp at h
      · next qs' a' hrec =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        intro idx hlt
        cases idx with
        | zero => simp [queryAtWithState]
        | succ idx' =>
          simp only [queryAtWithState, List.get_cons_succ]
          exact ih _ _ _ _ _ _ hrec idx' (by simpa [List.length_cons] using hlt)

/-- At index 0, `stateBeforeWithState` always returns the initial state. -/
private theorem stateBeforeWithState_at_zero {Q R A S : Type}
    (interaction : OracleInteraction Q R A)
    (fuel : Nat) (oracle : Fin fuel → S → Q → R × S)
    (s : S) :
    stateBeforeWithState interaction fuel oracle s 0 = some s := by
  cases interaction with
  | done _ => rfl
  | query _ _ => cases fuel <;> rfl

/-- If `stateBeforeWithState` at `idx+1` is `some`, then so are the state and
query at `idx`, and they compose via the oracle. -/
private theorem stateBeforeWithState_pred {Q R A S : Type}
    : ∀ (interaction : OracleInteraction Q R A)
        (fuel : Nat) (oracle : Fin fuel → S → Q → R × S)
        (s : S) (idx : Nat) (hidx : idx < fuel) (st' : S),
      stateBeforeWithState interaction fuel oracle s (idx + 1) = some st' →
      ∃ (st : S) (qry : Q),
        stateBeforeWithState interaction fuel oracle s idx = some st ∧
        queryAtWithState interaction fuel oracle s idx = some qry ∧
        st' = (oracle ⟨idx, hidx⟩ st qry).2 := by
  intro interaction fuel
  induction fuel generalizing interaction with
  | zero => intro _ _ _ _ hidx; omega
  | succ fuel ih =>
    intro oracle s idx hidx st' h_step
    cases interaction with
    | done a =>
      cases idx with
      | zero => simp [stateBeforeWithState] at h_step
      | succ _ => simp [stateBeforeWithState] at h_step
    | query q k =>
      cases idx with
      | zero =>
        simp only [stateBeforeWithState] at h_step
        have h0 := stateBeforeWithState_at_zero
          (k (oracle ⟨0, Nat.zero_lt_succ fuel⟩ s q).1) fuel
          (fun i => oracle ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
          (oracle ⟨0, Nat.zero_lt_succ fuel⟩ s q).2
        rw [h0] at h_step
        exact ⟨s, q, rfl, rfl, (Option.some.inj h_step).symm⟩
      | succ idx' =>
        simp only [stateBeforeWithState] at h_step
        have ih_result := ih (k (oracle ⟨0, Nat.zero_lt_succ fuel⟩ s q).1)
          (fun i => oracle ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
          (oracle ⟨0, Nat.zero_lt_succ fuel⟩ s q).2
          idx' (by omega) st' h_step
        obtain ⟨st, qry, h_st, h_qry, h_eq⟩ := ih_result
        simp only [stateBeforeWithState, queryAtWithState]
        exact ⟨st, qry, h_st, h_qry, h_eq⟩

/-- The state at step `idx + 1` is obtained by applying the oracle at step `idx`
to the state and query at step `idx`. -/
private theorem stateBeforeWithState_step {Q R A S : Type}
    : ∀ (interaction : OracleInteraction Q R A)
        (fuel : Nat) (oracle : Fin fuel → S → Q → R × S)
        (s : S) (idx : Nat) (hidx : idx < fuel) (st : S) (qry : Q),
      stateBeforeWithState interaction fuel oracle s idx = some st →
      queryAtWithState interaction fuel oracle s idx = some qry →
      stateBeforeWithState interaction fuel oracle s (idx + 1) =
        some (oracle ⟨idx, hidx⟩ st qry).2 := by
  intro interaction fuel
  induction fuel generalizing interaction with
  | zero => intro _ _ _ _ hidx; omega
  | succ fuel ih =>
    intro oracle s idx hidx st qry h_st h_qry
    cases interaction with
    | done a =>
      cases idx with
      | zero => simp [queryAtWithState] at h_qry
      | succ _ => simp [stateBeforeWithState] at h_st
    | query q k =>
      cases idx with
      | zero =>
        simp only [stateBeforeWithState, Option.some.injEq] at h_st
        simp only [queryAtWithState, Option.some.injEq] at h_qry
        subst h_st; subst h_qry
        simp only [stateBeforeWithState]
        cases (k (oracle ⟨0, Nat.zero_lt_succ fuel⟩ s q).1) with
        | done a => cases fuel <;> simp [stateBeforeWithState]
        | query _ _ => cases fuel <;> simp [stateBeforeWithState]
      | succ idx' =>
        simp only [stateBeforeWithState] at h_st ⊢
        simp only [queryAtWithState] at h_qry
        exact ih (k (oracle ⟨0, Nat.zero_lt_succ fuel⟩ s q).1)
          (fun i => oracle ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
          (oracle ⟨0, Nat.zero_lt_succ fuel⟩ s q).2
          idx' (by omega) st qry h_st h_qry

/-- Single-step preservation: `mapGameRealOracle` preserves
`assocLookup key st = none` when the query doesn't insert `key`. -/
private theorem mapGameReal_step_preserves_none {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    (n : ℕ) (q : ℕ)
    (w : R.Witness n) (y : R.Statement n)
    (rs : Fin q → P.ProverRandomness n)
    (ch : Fin q → P.Challenge n)
    (i : Fin q) (st : MapState P Msg n)
    (qry : Msg n ⊕ (Msg n × P.Commitment n))
    (key : Msg n × P.Commitment n)
    (h_none : assocLookup key st = none)
    (h_not_hash : qry ≠ Sum.inr key)
    (h_not_sign : ∀ m, qry = Sum.inl m → m ≠ key.1) :
    assocLookup key (mapGameRealOracle P Msg n q w y rs ch i st qry).2 = none := by
  letI := P.commitmentDecEq n
  cases qry with
  | inl m =>
    simp only [mapGameRealOracle, assocLookup]
    have hne : m ≠ key.1 := h_not_sign m rfl
    rw [if_neg (fun h => hne (Prod.mk.inj h).1)]
    exact h_none
  | inr mt =>
    simp only [mapGameRealOracle]
    cases hlk : assocLookup mt st with
    | some c => exact h_none
    | none =>
      simp only [assocLookup]
      have hne : mt ≠ key := fun h => h_not_hash (congrArg Sum.inr h)
      rw [if_neg hne]
      exact h_none

/-- In the mapGameRealOracle execution, if the forged message was never signed
and the first hash query for the forgery key is at index `j`, then the final
map associates the forgery key with `ch j`. -/
private theorem mapGameRealOracle_finalMap_lookup {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    (w : R.Witness n) (y : R.Statement n)
    (rs : Fin (A.numQueries n) → P.ProverRandomness n)
    (ch : Fin (A.numQueries n) → P.Challenge n)
    (queries : List (Msg n ⊕ (Msg n × P.Commitment n)))
    (mf : Msg n) (tf : P.Commitment n) (zf : P.Response n)
    (finalMap : MapState P Msg n)
    (h_result : (A.interact n y).runWithState (A.numQueries n)
        (mapGameRealOracle P Msg n (A.numQueries n) w y rs ch) [] =
      some (queries, (mf, tf, zf), finalMap))
    (hj : List.findIdx (fun x => decide (x = Sum.inr (mf, tf))) queries < A.numQueries n)
    (hj_in : List.findIdx (fun x => decide (x = Sum.inr (mf, tf))) queries < queries.length)
    (h_not_signed : (List.filterMap (fun q => match q with
      | .inl m => some m | .inr _ => none) queries).contains mf = false) :
    assocLookup (mf, tf) finalMap =
      some (ch ⟨List.findIdx (fun x => decide (x = Sum.inr (mf, tf))) queries, hj⟩) := by
  set j := List.findIdx (fun x => decide (x = Sum.inr (mf, tf))) queries with j_def
  set oracle := mapGameRealOracle P Msg n (A.numQueries n) w y rs ch
  have h_final := runWithState_finalState_eq_stateBeforeWithState _ _ _ _ _ _ _ h_result
  have h_query := runWithState_query_eq_queryAtWithState _ _ _ _ _ _ _ h_result
  letI := P.commitmentDecEq n
  have h_len_le := runWithState_length_le _ _ _ _ _ _ _ h_result
  -- Sub-claim: no signing query has message mf
  have h_not_sign_any : ∀ (i : Nat) (hi : i < queries.length) (m : Msg n),
      queries.get ⟨i, hi⟩ = .inl m → m ≠ mf := by
    intro i hi m hqi hmf; rw [hmf] at hqi
    have hmem : Sum.inl mf ∈ queries := by rw [← hqi]; exact List.getElem_mem hi
    have hfm : mf ∈ queries.filterMap (fun q => match q with
      | .inl m => some m | .inr _ => none) :=
      List.mem_filterMap.mpr ⟨.inl mf, hmem, rfl⟩
    have h_ct := List.contains_iff_mem.mpr hfm
    rw [h_ct] at h_not_signed
    exact Bool.noConfusion h_not_signed
  -- Sub-claim: before step j, no hash query matches (mf, tf)
  have h_not_hash_before : ∀ (i : Nat), i < j →
      ∀ (hi : i < queries.length), queries.get ⟨i, hi⟩ ≠ .inr (mf, tf) := by
    intro i hi_lt_j hi hqi
    exact absurd hqi (by
      have := List.not_of_lt_findIdx (j_def ▸ hi_lt_j)
      simpa using this)
  -- Main proof by forward induction
  suffices ∀ (k : Nat) (hk : k ≤ queries.length),
      ∃ st, stateBeforeWithState (A.interact n y) (A.numQueries n) oracle [] k = some st ∧
        (k ≤ j → assocLookup (mf, tf) st = none) ∧
        (j < k → assocLookup (mf, tf) st = some (ch ⟨j, hj⟩)) by
    obtain ⟨st, h_st, _, h_after⟩ := this queries.length le_rfl
    rw [h_final] at h_st; cases h_st
    exact h_after (by omega)
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨[], stateBeforeWithState_at_zero _ _ _ _, fun _ => rfl, fun h => absurd h (by omega)⟩
  | succ k' ih =>
    intro hk
    obtain ⟨st_prev, h_prev, h_none_if, h_some_if⟩ := ih (by omega)
    have hk'_fuel : k' < A.numQueries n := by omega
    -- Get query at step k'
    have hk'_len : k' < queries.length := by omega
    have h_qk : queryAtWithState (A.interact n y) (A.numQueries n) oracle [] k' =
        some (queries.get ⟨k', hk'_len⟩) := h_query k' hk'_len
    -- Step forward
    have h_step := stateBeforeWithState_step _ _ _ _ k' hk'_fuel st_prev
      (queries.get ⟨k', hk'_len⟩) h_prev h_qk
    set st_next := (oracle ⟨k', hk'_fuel⟩ st_prev (queries.get ⟨k', hk'_len⟩)).2
    refine ⟨st_next, h_step, fun hle => ?_, fun hlt => ?_⟩
    · -- k'+1 ≤ j, so k' < j: lookup stays none
      have h_prev_none := h_none_if (by omega)
      exact mapGameReal_step_preserves_none P Msg n (A.numQueries n) w y rs ch
        ⟨k', hk'_fuel⟩ st_prev (queries.get ⟨k', hk'_len⟩) (mf, tf) h_prev_none
        (h_not_hash_before k' (by omega) hk'_len)
        (fun m hm => h_not_sign_any k' hk'_len m hm)
    · -- j < k'+1, so j ≤ k'
      by_cases hjk : j = k'
      · -- k' = j: this is the insertion step
        subst hjk
        have h_prev_none := h_none_if le_rfl
        -- Query at step j is .inr (mf, tf)
        have h_qj_eq : queries.get ⟨j, hk'_len⟩ = .inr (mf, tf) := by
          have := List.findIdx_getElem (w := hj_in)
          simp only [decide_eq_true_eq] at this; exact this
        -- Oracle inserts (mf, tf) since assocLookup is none
        change assocLookup (mf, tf) st_next = some (ch ⟨j, hj⟩)
        simp only [st_next, oracle, h_qj_eq, mapGameRealOracle, h_prev_none, assocLookup]
        simp
      · -- k' > j: lookup persists from previous step
        have h_prev_some := h_some_if (by omega)
        change assocLookup (mf, tf) st_next = some (ch ⟨j, hj⟩)
        exact mapGameRealOracle_lookup_persist P Msg n (A.numQueries n) w y rs ch
          ⟨k', hk'_fuel⟩ st_prev mf tf (ch ⟨j, hj⟩) (queries.get ⟨k', hk'_len⟩)
          h_prev_some (fun m hm => h_not_sign_any k' hk'_len m hm)

/-- Entries in a stateful interaction's state came from the initial state
or were inserted by an oracle step. -/
private theorem stateBeforeWithState_mem_source {Q R A : Type} {S : Type}
    : ∀ (interaction : OracleInteraction Q R A)
        (fuel : Nat) (oracle : Fin fuel → S → Q → R × S)
        (s : S) (idx : Nat) (st : S)
        (P : S → Prop),
      P s →
      (∀ (j : Fin fuel) (sj : S) (qj : Q), P sj → P (oracle j sj qj).2) →
      stateBeforeWithState interaction fuel oracle s idx = some st →
      P st := by
  intro interaction fuel
  induction fuel generalizing interaction with
  | zero =>
    intro oracle s idx st P hP _ h_st
    cases interaction with
    | done _ => cases idx with
                | zero =>
                  simp only [stateBeforeWithState, Option.some.injEq] at h_st
                  subst h_st; exact hP
                | succ _ =>
                  simp only [stateBeforeWithState] at h_st
                  contradiction
    | query _ _ => cases idx with
                   | zero =>
                     simp only [stateBeforeWithState, Option.some.injEq] at h_st
                     subst h_st; exact hP
                   | succ _ =>
                     simp only [stateBeforeWithState] at h_st
                     contradiction
  | succ fuel ih =>
    intro oracle s idx st P hP hOracle h_st
    cases interaction with
    | done a =>
      cases idx with
      | zero =>
        simp only [stateBeforeWithState, Option.some.injEq] at h_st
        subst h_st; exact hP
      | succ _ =>
        simp only [stateBeforeWithState] at h_st
        contradiction
    | query q k =>
      cases idx with
      | zero =>
        simp only [stateBeforeWithState, Option.some.injEq] at h_st
        subst h_st; exact hP
      | succ idx' =>
        simp only [stateBeforeWithState] at h_st
        exact ih (k (oracle ⟨0, Nat.zero_lt_succ fuel⟩ s q).1)
          (fun i => oracle ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
          (oracle ⟨0, Nat.zero_lt_succ fuel⟩ s q).2 idx' st P
          (hOracle ⟨0, Nat.zero_lt_succ fuel⟩ s q hP)
          (fun j sj qj hPsj => hOracle ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ sj qj hPsj)
          h_st

/-- Every entry in the lazy-oracle map at step `idx` has its commitment
component witnessed by `lazyInsertedCommitAt` at some earlier step. -/
private theorem lazyMap_entry_commit_source {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    (w : R.Witness n) (y : R.Statement n)
    (rs : Fin (A.numQueries n) → P.ProverRandomness n)
    (ch : Fin (A.numQueries n) → P.Challenge n)
    (idx : Nat) (hidx : idx < A.numQueries n)
    (st : MapState P Msg n)
    (key : Msg n × P.Commitment n) (v : P.Challenge n)
    (h_st : lazyMapBefore P Msg A n w y rs ch idx = some st)
    (h_mem : (key, v) ∈ st) :
    ∃ (i : Fin (A.numQueries n)), i.val < idx ∧
      lazyInsertedCommitAt P Msg A n w y rs ch i = some key.2 := by
  induction idx generalizing st key v with
  | zero =>
    unfold lazyMapBefore at h_st
    rw [stateBeforeWithState_at_zero] at h_st
    cases h_st; simp at h_mem
  | succ k ih =>
    have hk : k < A.numQueries n := Nat.lt_of_succ_lt hidx
    unfold lazyMapBefore at h_st
    obtain ⟨map_k, qry_k, h_map_k, h_qry_k, h_eq⟩ :=
      stateBeforeWithState_pred _ _ _ _ k hk st h_st
    rw [h_eq] at h_mem
    letI := P.commitmentDecEq n
    cases qry_k with
    | inl m =>
      simp only [lazyRomOracle] at h_mem
      cases hlookup : assocLookup (m, P.commit n w y (rs ⟨k, hk⟩)) map_k with
      | some c =>
        simp only [hlookup] at h_mem
        obtain ⟨i, hi_lt, hi⟩ :=
          ih hk map_k key v (by unfold lazyMapBefore; exact h_map_k) h_mem
        exact ⟨i, by omega, hi⟩
      | none =>
        simp only [hlookup] at h_mem
        cases h_mem with
        | head =>
          refine ⟨⟨k, hk⟩, by change k < k + 1; omega, ?_⟩
          unfold lazyInsertedCommitAt lazyQueryAt
          rw [h_qry_k]
        | tail _ h_tail =>
          obtain ⟨i, hi_lt, hi⟩ :=
            ih hk map_k key v (by unfold lazyMapBefore; exact h_map_k) h_tail
          exact ⟨i, by omega, hi⟩
    | inr mt =>
      simp only [lazyRomOracle] at h_mem
      cases hlookup : assocLookup (mt.1, mt.2) map_k with
      | some c =>
        simp only [hlookup] at h_mem
        obtain ⟨i, hi_lt, hi⟩ :=
          ih hk map_k key v (by unfold lazyMapBefore; exact h_map_k) h_mem
        exact ⟨i, by omega, hi⟩
      | none =>
        simp only [hlookup] at h_mem
        cases h_mem with
        | head =>
          refine ⟨⟨k, hk⟩, by change k < k + 1; omega, ?_⟩
          unfold lazyInsertedCommitAt lazyQueryAt
          rw [h_qry_k]
        | tail _ h_tail =>
          obtain ⟨i, hi_lt, hi⟩ :=
            ih hk map_k key v (by unfold lazyMapBefore; exact h_map_k) h_tail
          exact ⟨i, by omega, hi⟩

/-- If a signing query at step `k` finds its commitment already in the map,
then a pair-reuse event exists. -/
private theorem map_lookup_implies_pairReuse {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    (w : R.Witness n) (y : R.Statement n)
    (rs : Fin (A.numQueries n) → P.ProverRandomness n)
    (ch : Fin (A.numQueries n) → P.Challenge n)
    (k : Nat) (hk : k < A.numQueries n)
    (st : MapState P Msg n)
    (m : Msg n) (c : P.Challenge n)
    (h_st : lazyMapBefore P Msg A n w y rs ch k = some st)
    (h_qry : lazyQueryAt P Msg A n w y rs ch k = some (Sum.inl m))
    (h_lookup : assocLookup (m, P.commit n w y (rs ⟨k, hk⟩)) st = some c) :
    ∃ (i j : Fin (A.numQueries n)), i.val < j.val ∧
      lazyPairCommitReuse P Msg A n w y rs ch i j = true := by
  have h_mem := assocLookup_some_mem _ _ _ h_lookup
  obtain ⟨i, hi_lt, hi_commit⟩ := lazyMap_entry_commit_source P Msg A n w y rs ch
    k hk st (m, P.commit n w y (rs ⟨k, hk⟩)) c h_st h_mem
  refine ⟨i, ⟨k, hk⟩, hi_lt, ?_⟩
  unfold lazyPairCommitReuse
  rw [hi_commit, show (⟨k, hk⟩ : Fin (A.numQueries n)).val = k from rfl, h_qry]
  simp

/-- If two oracles agree at every step on the `(state, query)` encountered
during execution with `oracle₁`, then `runWithState` produces the same result. -/
private theorem runWithState_eq_of_oracle_agree_on_trace {Q R A S : Type}
    : ∀ (interaction : OracleInteraction Q R A)
        (fuel : Nat) (oracle₁ oracle₂ : Fin fuel → S → Q → R × S)
        (s : S),
        (∀ (k : Nat) (hk : k < fuel) (st : S) (q : Q),
          stateBeforeWithState interaction fuel oracle₁ s k = some st →
          queryAtWithState interaction fuel oracle₁ s k = some q →
          oracle₁ ⟨k, hk⟩ st q = oracle₂ ⟨k, hk⟩ st q) →
        interaction.runWithState fuel oracle₁ s =
        interaction.runWithState fuel oracle₂ s := by
  intro interaction fuel
  induction fuel generalizing interaction with
  | zero => intro _ _ _ _; cases interaction <;> rfl
  | succ n ih =>
    intro oracle₁ oracle₂ s h
    cases interaction with
    | done => rfl
    | query q k =>
      simp only [OracleInteraction.runWithState]
      have h0 : oracle₁ ⟨0, Nat.zero_lt_succ n⟩ s q =
          oracle₂ ⟨0, Nat.zero_lt_succ n⟩ s q :=
        h 0 (Nat.zero_lt_succ n) s q rfl rfl
      rw [h0]
      have h_ih := ih (k (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ s q).1)
        (fun (i : Fin n) => oracle₁ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
        (fun (i : Fin n) => oracle₂ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
        (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ s q).2
        (fun k' hk' st' q' h_state h_query => by
          have := h (k' + 1) (by omega) st' q'
            (by simp only [stateBeforeWithState]; rw [h0]; exact h_state)
            (by simp only [queryAtWithState]; rw [h0]; exact h_query)
          exact this)
      rw [h_ih]

/-- If no pair-reuse event occurs, LazyROM and MapGame_Real produce the same
run statement for fixed coins. -/
private theorem lazy_run_stmt_eq_mapGame_real_run_stmt_of_no_reuse {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    (w : R.Witness n) (y : R.Statement n)
    (rs : Fin (A.numQueries n) → P.ProverRandomness n)
    (ch : Fin (A.numQueries n) → P.Challenge n) :
    (¬ ∃ (i j : Fin (A.numQueries n)), i.val < j.val ∧
      lazyPairCommitReuse P Msg A n w y rs ch i j = true) →
    lazyRom_run_stmt P Msg A n w y rs ch =
    mapGame_real_run_stmt P Msg A n w y rs ch := by
  intro h_no_reuse
  let q := A.numQueries n
  letI := P.commitmentDecEq n
  -- Step 1: Show the runWithState calls agree
  have h_run_eq : (A.interact n y).runWithState q
      (lazyRomOracle P Msg n q w y rs ch) [] =
    (A.interact n y).runWithState q
      (mapGameRealOracle P Msg n q w y rs ch) [] := by
    apply runWithState_eq_of_oracle_agree_on_trace
    intro k hk st qry h_st h_qry
    cases qry with
    | inr mt =>
      simp [lazyRomOracle, mapGameRealOracle]
    | inl m =>
      unfold lazyRomOracle mapGameRealOracle
      simp only
      cases h_lookup : assocLookup (m, P.commit n w y (rs ⟨k, hk⟩)) st with
      | none => rfl
      | some c =>
        exfalso
        exact h_no_reuse (map_lookup_implies_pairReuse P Msg A n w y rs ch
          k hk st m c h_st h_qry h_lookup)
  -- Step 2: Use the equality to simplify
  simp only [lazyRom_run_stmt, mapGame_real_run_stmt]
  have h_rw : (A.interact n y).runWithState (A.numQueries n)
      (lazyRomOracle P Msg n (A.numQueries n) w y rs ch) [] =
    (A.interact n y).runWithState (A.numQueries n)
      (mapGameRealOracle P Msg n (A.numQueries n) w y rs ch) [] := h_run_eq
  rw [h_rw]
  cases h_result : (A.interact n y).runWithState (A.numQueries n)
      (mapGameRealOracle P Msg n (A.numQueries n) w y rs ch) [] with
  | none => rfl
  | some val =>
    obtain ⟨queries, ⟨mf, tf, zf⟩, finalMap⟩ := val
    simp only
    split
    next hj =>
      -- Split on whether j < queries.length (hash was actually queried)
      by_cases hj_in :
        List.findIdx (fun x => decide (x = Sum.inr (mf, tf))) queries < queries.length
      · -- Hash WAS queried: use mapGameRealOracle_finalMap_lookup
        simp only [hj_in, ↓reduceIte]
        set signMsgs := List.filterMap (fun q => match q with
          | .inl m => some m | .inr _ => none) queries
        cases h_signed : signMsgs.contains mf with
        | true =>
          simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
          cases assocLookup (mf, tf) finalMap <;> rfl
        | false =>
          have h_lookup := mapGameRealOracle_finalMap_lookup P Msg A n w y rs ch
            queries mf tf zf finalMap h_result hj hj_in h_signed
          simp only [h_lookup]
      · -- Hash was NOT queried: both sides are none
        simp only [hj_in, ↓reduceIte]
        -- LHS: match assocLookup ... with | some c => ... | none => none = none
        set signMsgs := List.filterMap (fun q => match q with
          | .inl m => some m | .inr _ => none) queries
        cases h_signed : signMsgs.contains mf with
        | true =>
          simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
          cases assocLookup (mf, tf) finalMap <;> rfl
        | false =>
          have h_no_hash : Sum.inr (mf, tf) ∉ queries := by
            intro hmem
            apply hj_in
            rw [List.findIdx_lt_length]
            refine ⟨Sum.inr (mf, tf), hmem, ?_⟩
            dsimp
            exact of_decide_eq_self_eq_true _
          have h_none : assocLookup (mf, tf) finalMap = none := by
            set oracle := mapGameRealOracle P Msg n (A.numQueries n) w y rs ch
            have h_final := runWithState_finalState_eq_stateBeforeWithState _ _ _ _ _ _ _ h_result
            have h_query_at := runWithState_query_eq_queryAtWithState _ _ _ _ _ _ _ h_result
            have h_len_le := runWithState_length_le _ _ _ _ _ _ _ h_result
            -- No signing query has message mf
            have h_not_sign_mf : ∀ (i : Nat) (hi : i < queries.length) (m : Msg n),
                queries.get ⟨i, hi⟩ = .inl m → m ≠ mf := by
              intro i hi m hqi hmf; rw [hmf] at hqi
              have hmem : Sum.inl mf ∈ queries := by rw [← hqi]; exact List.getElem_mem hi
              have hfm : mf ∈ signMsgs := List.mem_filterMap.mpr ⟨.inl mf, hmem, rfl⟩
              have h_ct := List.contains_iff_mem.mpr hfm
              rw [h_ct] at h_signed
              exact Bool.noConfusion h_signed
            -- Forward induction: assocLookup stays none at every step
            suffices ∀ k (hk : k ≤ queries.length),
                ∃ st, stateBeforeWithState (A.interact n y) (A.numQueries n)
                    oracle [] k = some st ∧
                  assocLookup (mf, tf) st = none by
              obtain ⟨st, h_st, h_ans⟩ := this queries.length le_rfl
              rw [h_final] at h_st; cases h_st; exact h_ans
            intro k
            induction k with
            | zero =>
              intro _
              exact ⟨[], stateBeforeWithState_at_zero _ _ _ _, rfl⟩
            | succ k' ih =>
              intro hk
              obtain ⟨st_prev, h_prev, h_prev_none⟩ := ih (by omega)
              have hk'_fuel : k' < A.numQueries n := by omega
              have hk'_len : k' < queries.length := by omega
              have h_qk := h_query_at k' hk'_len
              have h_step := stateBeforeWithState_step _ _ _ _ k' hk'_fuel st_prev
                (queries.get ⟨k', hk'_len⟩) h_prev h_qk
              refine ⟨_, h_step, ?_⟩
              exact mapGameReal_step_preserves_none P Msg n (A.numQueries n) w y rs ch
                ⟨k', hk'_fuel⟩ st_prev (queries.get ⟨k', hk'_len⟩) (mf, tf) h_prev_none
                (by intro h_eq; exact h_no_hash (by rw [← h_eq]; exact List.getElem_mem hk'_len))
                (fun m hm => h_not_sign_mf k' hk'_len m hm)
          simp [h_none]
    next hj =>
      rfl

/-- `uniformExpect` does not depend on the particular `Fintype`/`Nonempty`
instances chosen for the sampling type. -/
private theorem uniformExpect_inst_irrel {α : Type*}
    [instF₀ : Fintype α] [instN₀ : Nonempty α] (f : α → ℝ)
    (instF : Fintype α) (instN : Nonempty α) :
    @uniformExpect α instF₀ instN₀ f = @uniformExpect α instF instN f := by
  cases Subsingleton.elim instF₀ instF
  cases Subsingleton.elim instN₀ instN
  rfl

/-- **Lazy sampling**: the ROM EUF-CMA advantage equals the LazyROM
advantage. The ROM game samples a full random function
`H : Msg × Comm → Ch` and evaluates it at ≤ q adaptively-chosen points.
By the lazy sampling principle, evaluating a uniform random function at
fresh points yields independent uniform values, which is exactly what
the per-query challenges `ch_i` provide. Cached values in the Map ensure
consistency on repeated queries, faithfully reproducing `H`.

**Proof approach (future work):** Induction on `fuel` using
`Equiv.piSplitAt` to decompose the function space
`(X → Y) ≃ Y × ({x' // x' ≠ x₀} → Y)` at each query point. Requires:
- `uniformExpect_eval_at_point`: `E_{H:X→Y}[f(H(x))] = E_{y:Y}[f(y)]`
- Bridge between `run` (used by ROM) and `runWithState` (used by LazyROM)
- Strengthened IH tracking Map consistency with the random function -/
private theorem rom_eq_lazy_rom {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    [∀ n, Fintype (Msg n)] [∀ n, Nonempty (Msg n)]
    [∀ n, Fintype (R.Witness n)] [∀ n, Nonempty (R.Witness n)]
    (kg : R.WithKeyGen)
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ) :
    (ROM_EUF_CMA_Game P Msg kg).advantage A n =
    lazyRom_advantage P Msg kg A n := by
  simp only [ROM_EUF_CMA_Game, romCmaWinCondition,
    List.contains_eq_mem, List.mem_filterMap,
    Sum.exists, Option.some.injEq, exists_eq_right, reduceCtorEq, and_false,
    exists_const, or_false, lazyRom_advantage, forkAcceptProb,
    lazyRom_run, lazyRom_run_stmt, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true, decide_eq_false_iff_not]
  conv_lhs => rw [uniformExpect_prod]
  conv_rhs => rw [uniformExpect_prod]
  congr 1
  ext wrs
  rcases wrs with ⟨w, rs⟩
  let runPayoff : Option (List (Msg n ⊕ (Msg n × P.Commitment n)) ×
      (Msg n × P.Commitment n × P.Response n) × MapState P Msg n) → ℝ :=
    fun result =>
      letI := P.commitmentDecEq n
      match result with
      | none => 0
      | some (queries, (mf, tf, zf), finalMap) =>
        let j := queries.findIdx (fun x => decide (x = .inr (mf, tf)))
        if hj : j < A.numQueries n then
          let signMsgs := queries.filterMap (fun q => match q with
            | .inl m => some m | .inr _ => none)
          match assocLookup (mf, tf) finalMap with
          | some c => boolToReal (P.verify n (kg.keyOf n w) tf c zf && !decide (mf ∈ signMsgs))
          | none => 0
        else 0
  have h_swap :=
    lazyRomH_runWithState_uniform_eq (P := P) (Msg := Msg)
      n (A.numQueries n) (A.interact n (kg.keyOf n w)) w (kg.keyOf n w) rs
      runPayoff
  let rhsNested : (Fin (A.numQueries n) → P.Challenge n) → ℝ := fun ch =>
    match
      (match
        (A.interact n (kg.keyOf n w)).runWithState (A.numQueries n)
          (lazyRomOracle P Msg n (A.numQueries n) w (kg.keyOf n w) rs ch) [] with
      | none => (none : Option (Fin (A.numQueries n) ×
          (Msg n × P.Commitment n × P.Response n)))
      | some (queries, (mf, tf, zf), finalMap) =>
        if hj : List.findIdx (fun x => decide (x = Sum.inr (mf, tf))) queries < A.numQueries n then
          match assocLookup (mf, tf) finalMap with
          | some c =>
            if P.verify n (kg.keyOf n w) tf c zf &&
                !(List.filterMap (fun q : Msg n ⊕ (Msg n × P.Commitment n) => match q with
                  | Sum.inl m => some m
                  | Sum.inr _ => none) queries).contains mf then
              some
                (⟨List.findIdx (fun x => decide (x = Sum.inr (mf, tf))) queries, hj⟩,
                  (mf, tf, zf))
            else none
          | none => none
        else (none : Option (Fin (A.numQueries n) ×
            (Msg n × P.Commitment n × P.Response n))))
    with
    | none => 0
    | some _ => 1
  have h_rhs_fun :
      (fun ch =>
        runPayoff ((A.interact n (kg.keyOf n w)).runWithState (A.numQueries n)
          (lazyRomOracle P Msg n (A.numQueries n) w (kg.keyOf n w) rs ch) [])) =
      rhsNested := by
    funext ch
    let result :=
      (A.interact n (kg.keyOf n w)).runWithState (A.numQueries n)
        (lazyRomOracle P Msg n (A.numQueries n) w (kg.keyOf n w) rs ch) []
    cases h_result : result with
    | none =>
      simp [rhsNested, runPayoff, boolToReal, result, h_result]
    | some triple =>
      rcases triple with ⟨queries, forg, finalMap⟩
      rcases forg with ⟨mf, tf, zf⟩
      by_cases hj : List.findIdx (fun x => decide (x = Sum.inr (mf, tf))) queries < A.numQueries n
      · cases h_lookup : assocLookup (mf, tf) finalMap with
        | none =>
          simp [rhsNested, runPayoff, boolToReal, result, h_result, hj, h_lookup]
        | some c =>
          have h_contains :
              (List.filterMap (fun q => match q with
                | Sum.inl m => some m
                | Sum.inr _ => none) queries).contains mf =
              decide (mf ∈ List.filterMap (fun q => match q with
                | Sum.inl m => some m
                | Sum.inr _ => none) queries) := by
            simp
          by_cases hverify :
              (P.verify n (kg.keyOf n w) tf c zf &&
                !decide
                  (mf ∈
                    List.filterMap
                      (fun q =>
                        match q with
                        | Sum.inl m => some m
                        | Sum.inr _ => none)
                      queries)) = true
          · simp [rhsNested, runPayoff, boolToReal, result, h_result, hj, h_lookup,
              hverify]
          · simp [rhsNested, runPayoff, boolToReal, result, h_result, hj, h_lookup,
              hverify]
      · simp [rhsNested, runPayoff, boolToReal, result, h_result, hj]
  have h_main :
      uniformExpect (Fin (A.numQueries n) → (Msg n × P.Commitment n → P.Challenge n))
        (fun Hs =>
          runPayoff
            ((A.interact n (kg.keyOf n w)).runWithState (A.numQueries n)
              (fun i st qry =>
                lazyRomHOracle P Msg n (A.numQueries n) w (kg.keyOf n w) rs i (Hs i) st qry) [])) =
      uniformExpect (Fin (A.numQueries n) → P.Challenge n) rhsNested := by
    calc
      uniformExpect (Fin (A.numQueries n) → (Msg n × P.Commitment n → P.Challenge n))
          (fun Hs =>
            runPayoff
              ((A.interact n (kg.keyOf n w)).runWithState (A.numQueries n)
                (fun i st qry =>
                  lazyRomHOracle P Msg n (A.numQueries n)
                    w (kg.keyOf n w) rs i (Hs i) st qry) [])) =
        uniformExpect (Fin (A.numQueries n) → P.Challenge n)
          (fun ch =>
            runPayoff ((A.interact n (kg.keyOf n w)).runWithState (A.numQueries n)
              (lazyRomOracle P Msg n (A.numQueries n) w (kg.keyOf n w) rs ch) [])) := by
        simpa [runPayoff, boolToReal, lazyRomHOracle] using h_swap
      _ = uniformExpect (Fin (A.numQueries n) → P.Challenge n) rhsNested := by
        rw [h_rhs_fun]
  let goalRhs : (Fin (A.numQueries n) → P.Challenge n) → ℝ := fun b =>
    match
      match
        (A.interact n (kg.keyOf n w)).runWithState (A.numQueries n)
          (lazyRomOracle P Msg n (A.numQueries n) w (kg.keyOf n w) rs b) [] with
      | none => (none : Option (Fin (A.numQueries n) ×
          (Msg n × P.Commitment n × P.Response n)))
      | some (queries, (mf, tf, zf), finalMap) =>
        if h : List.findIdx (fun x => decide (x = Sum.inr (mf, tf))) queries < A.numQueries n then
          match assocLookup (mf, tf) finalMap with
          | some c =>
            if P.verify n (kg.keyOf n w) tf c zf &&
                !(List.filterMap (fun q : Msg n ⊕ (Msg n × P.Commitment n) => match q with
                  | Sum.inl m => some m
                  | Sum.inr _ => none) queries).contains mf then
              some
                (⟨List.findIdx (fun x => decide (x = Sum.inr (mf, tf))) queries, h⟩,
                  (mf, tf, zf))
            else none
          | none => none
        else (none : Option (Fin (A.numQueries n) ×
            (Msg n × P.Commitment n × P.Response n)))
    with
    | none => 0
    | some _ => 1
  have h_rhs_nested_eq_goal : rhsNested = goalRhs := by
    funext b
    let result :=
      (A.interact n (kg.keyOf n w)).runWithState (A.numQueries n)
        (lazyRomOracle P Msg n (A.numQueries n) w (kg.keyOf n w) rs b) []
    cases h_result : result with
    | none =>
      simp [rhsNested, goalRhs, result, h_result]
    | some triple =>
      rcases triple with ⟨queries, forg, finalMap⟩
      rcases forg with ⟨mf, tf, zf⟩
      by_cases hj : List.findIdx (fun x => decide (x = Sum.inr (mf, tf))) queries < A.numQueries n
      · cases h_lookup : assocLookup (mf, tf) finalMap with
        | none =>
          simp [rhsNested, goalRhs, result, h_result, hj, h_lookup]
        | some c =>
          by_cases hcond :
              (P.verify n (kg.keyOf n w) tf c zf &&
                !(List.filterMap
                    (fun q =>
                      match q with
                      | Sum.inl m => some m
                      | Sum.inr _ => none)
                    queries).contains
                  mf) = true
          · simp [rhsNested, goalRhs, result, h_result, hj, h_lookup]
          · simp [rhsNested, goalRhs, result, h_result, hj, h_lookup]
      · simp [rhsNested, goalRhs, result, h_result, hj]
  conv_lhs =>
    arg 2
    ext Hs
    simp [runPayoff, boolToReal, lazyRomHOracle]
  refine h_main.trans ?_
  rw [h_rhs_nested_eq_goal]
  apply congrArg (uniformExpect (Fin (A.numQueries n) → P.Challenge n))
  funext b
  let result :=
    (A.interact n (kg.keyOf n w)).runWithState (A.numQueries n)
      (lazyRomOracle P Msg n (A.numQueries n) w (kg.keyOf n w) rs b) []
  cases h_result : result with
  | none =>
    simp [goalRhs, result, h_result]
  | some triple =>
    rcases triple with ⟨queries, forg, finalMap⟩
    rcases forg with ⟨mf, tf, zf⟩
    by_cases hj : List.findIdx (fun x => decide (x = Sum.inr (mf, tf))) queries < A.numQueries n
    · cases h_lookup : assocLookup (mf, tf) finalMap with
      | none =>
        simp [goalRhs, result, h_result, hj, h_lookup]
      | some c =>
        by_cases hcond :
            (P.verify n (kg.keyOf n w) tf c zf &&
              !(List.filterMap
                  (fun q =>
                    match q with
                    | Sum.inl m => some m
                    | Sum.inr _ => none)
                  queries).contains
                mf) = true
        · simp only [goalRhs, result, h_result, hj, h_lookup, List.contains_eq_mem,
            List.mem_filterMap, Sum.exists, Option.some.injEq, exists_eq_right,
            reduceCtorEq, and_false, exists_const, or_false, Bool.and_eq_true,
            Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
          conv_lhs =>
            rw [dif_pos (show True by trivial)]
            rw [if_pos hcond]
            simp
          conv_rhs =>
            rw [dif_pos (show True by trivial)]
            rw [if_pos hcond]
            simp
        · simp only [goalRhs, result, h_result, hj, h_lookup, List.contains_eq_mem,
            List.mem_filterMap, Sum.exists, Option.some.injEq, exists_eq_right,
            reduceCtorEq, and_false, exists_const, or_false, Bool.and_eq_true,
            Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
          conv_lhs =>
            rw [dif_pos (show True by trivial)]
            rw [if_neg hcond]
            simp
          conv_rhs =>
            rw [dif_pos (show True by trivial)]
            rw [if_neg hcond]
            simp
    · simp [goalRhs, result, h_result, hj]

/-- **LazyROM ≤ MapGame_Real + q²δ**: the game hop from lazy ROM to
MapGame_Real. The two games use the same coin type
`(W × (Fin q → PR)) × (Fin q → Ch)` and identical post-processing.
Their oracles differ only at signing steps where the key
`(m, commit(w,y,rs_i))` is already in the Map:

- `lazyRomOracle` uses the cached challenge (simulating a consistent
  random function)
- `mapGameRealOracle` always uses the fresh `ch_i`

When no such collision occurs, both oracles are identical at every step,
producing the same interaction and hence the same indicator value.

The collision probability is bounded by `q² · δ`:
- **Signing-signing**: commitment collision between `rs_i` and `rs_j`,
  bounded by `uniformExpect_commit_collision_pair` / `δ` per pair
- **Hash-signing**: adversary predicting `commit(w,y,rs_i)` before step
  `i`, bounded by `UnpredictableCommitments` since `rs_i` is independent
  of the adversary's queries before step `i`

Total: ≤ `q(q-1)/2` pairs × `δ` each ≤ `q² · δ`. -/
private theorem lazy_le_mapGame_real {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    [∀ n, Nonempty (Msg n)]
    [∀ n, Fintype (R.Witness n)] [∀ n, Nonempty (R.Witness n)]
    (kg : R.WithKeyGen)
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    (δ : ℕ → ℝ)
    (h_unpred : P.UnpredictableCommitments δ) :
    lazyRom_advantage P Msg kg A n ≤
    mapGame_real_advantage P Msg kg A n +
    (A.numQueries n : ℝ) ^ 2 * δ n := by
  classical
  let q := A.numQueries n
  letI := P.proverRandomnessFintype n
  letI := P.proverRandomnessNonempty n
  letI := P.challengeFintype n
  letI := P.challengeNonempty n
  let Ω := (R.Witness n × (Fin q → P.ProverRandomness n)) ×
      (Fin q → P.Challenge n)
  let fL : Ω → ℝ := fun ⟨⟨w, rs⟩, ch⟩ =>
    match lazyRom_run_stmt P Msg A n w (kg.keyOf n w) rs ch with
    | none => 0
    | some _ => 1
  let fM : Ω → ℝ := fun ⟨⟨w, rs⟩, ch⟩ =>
    match mapGame_real_run_stmt P Msg A n w (kg.keyOf n w) rs ch with
    | none => 0
    | some _ => 1
  let bad : Ω → Prop := fun ⟨⟨w, rs⟩, ch⟩ =>
    ∃ (i j : Fin q), i.val < j.val ∧
      lazyPairCommitReuse P Msg A n w (kg.keyOf n w) rs ch i j = true
  have h_agree : ∀ ω : Ω, ¬ bad ω → fL ω = fM ω := by
    intro ⟨⟨w, rs⟩, ch⟩ hnb
    dsimp [fL, fM, bad] at hnb ⊢
    rw [lazy_run_stmt_eq_mapGame_real_run_stmt_of_no_reuse
      P Msg A n w (kg.keyOf n w) rs ch hnb]
  have h_fL_nn : ∀ ω : Ω, 0 ≤ fL ω := by
    intro ⟨⟨w, rs⟩, ch⟩
    dsimp [fL]
    split <;> norm_num
  have h_fL_le : ∀ ω : Ω, fL ω ≤ 1 := by
    intro ⟨⟨w, rs⟩, ch⟩
    dsimp [fL]
    split <;> norm_num
  have h_fM_nn : ∀ ω : Ω, 0 ≤ fM ω := by
    intro ⟨⟨w, rs⟩, ch⟩
    dsimp [fM]
    split <;> norm_num
  have h_fM_le : ∀ ω : Ω, fM ω ≤ 1 := by
    intro ⟨⟨w, rs⟩, ch⟩
    dsimp [fM]
    split <;> norm_num
  have h_hop := uniformExpect_game_hop Ω fL fM bad h_agree
    h_fL_nn h_fL_le h_fM_nn h_fM_le
  have h_bad_bound :
      uniformExpect Ω (fun ω => if bad ω then (1 : ℝ) else 0) ≤
      (q : ℝ) ^ 2 * δ n := by
    simpa [Ω, bad] using
      lazyCommitReuse_bound P Msg kg A n δ h_unpred
  have h_sub :
      uniformExpect Ω fL - uniformExpect Ω fM ≤
        uniformExpect Ω (fun ω => if bad ω then (1 : ℝ) else 0) := by
    exact le_trans (le_abs_self _) h_hop
  have h_lin :
      uniformExpect Ω fL ≤
        uniformExpect Ω fM +
        uniformExpect Ω (fun ω => if bad ω then (1 : ℝ) else 0) := by
    linarith [h_sub]
  have h_main :
      uniformExpect Ω fL ≤ uniformExpect Ω fM + (q : ℝ) ^ 2 * δ n := by
    exact le_trans h_lin (by linarith [h_bad_bound])
  have h_advL : lazyRom_advantage P Msg kg A n = uniformExpect Ω fL := by
    unfold lazyRom_advantage forkAcceptProb lazyRom_run
    congr!; rename_i x; obtain ⟨⟨w, rs⟩, ch⟩ := x
    dsimp [fL]; split <;> simp_all
  have h_advM : mapGame_real_advantage P Msg kg A n = uniformExpect Ω fM := by
    unfold mapGame_real_advantage forkAcceptProb mapGame_real_run
    congr!; rename_i x; obtain ⟨⟨w, rs⟩, ch⟩ := x
    dsimp [fM]; split <;> simp_all
  rw [h_advL, h_advM]; exact h_main

/-- **ROM ≤ MapGame_Real + q²δ**: the ROM advantage is at most the
MapGame_Real advantage plus a commitment collision term `q² · δ`.

Proved by combining:
- `rom_eq_lazy_rom`: ROM advantage = LazyROM advantage (lazy sampling)
- `lazy_le_mapGame_real`: LazyROM ≤ MapGame_Real + q²δ (game hop) -/
private theorem rom_le_mapGame_real {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    [∀ n, Fintype (Msg n)] [∀ n, Nonempty (Msg n)]
    [∀ n, Fintype (R.Witness n)] [∀ n, Nonempty (R.Witness n)]
    (kg : R.WithKeyGen)
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    (δ : ℕ → ℝ)
    (h_unpred : P.UnpredictableCommitments δ) :
    (ROM_EUF_CMA_Game P Msg kg).advantage A n ≤
    mapGame_real_advantage P Msg kg A n +
    (A.numQueries n : ℝ) ^ 2 * δ n := by
  have h1 := rom_eq_lazy_rom P Msg kg A n
  have h2 := lazy_le_mapGame_real P Msg kg A n δ h_unpred
  linarith

/-- **ROM game hop bound**: combines `rom_le_mapGame_real` (lazy sampling +
collision bound) with `mapGame_real_eq_mapGame1_hvzk` (HVZK switch). -/
private theorem rom_eq_mapGame1_hvzk_bound {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    [∀ n, Fintype (Msg n)] [∀ n, Nonempty (Msg n)]
    [∀ n, Fintype (R.Witness n)] [∀ n, Nonempty (R.Witness n)]
    (kg : R.WithKeyGen)
    (hvzk : P.SpecialHVZK)
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    (δ : ℕ → ℝ)
    (h_unpred : P.UnpredictableCommitments δ) :
    (ROM_EUF_CMA_Game P Msg kg).advantage A n ≤
      mapGame1_hvzk_advantage P Msg kg hvzk A n +
      (A.numQueries n : ℝ) ^ 2 * δ n := by
  have h1 := rom_le_mapGame_real P Msg kg A n δ h_unpred
  have h2 := mapGame_real_eq_mapGame1_hvzk P Msg kg hvzk A n
  linarith

/-- When `mapGame1_hvzk_run_stmt` succeeds, extract the underlying
`runWithState` result and key properties. -/
private lemma mapGame1_hvzk_run_stmt_data {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type) [∀ n, DecidableEq (Msg n)]
    (hvzk : P.SpecialHVZK) (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    (y : R.Statement n) (sr : Fin (A.numQueries n) → hvzk.SimRandomness n)
    (ch : Fin (A.numQueries n) → P.Challenge n)
    {j : Fin (A.numQueries n)} {mf : Msg n} {tf : P.Commitment n}
    {zf : P.Response n}
    (h : mapGame1_hvzk_run_stmt P Msg hvzk A n y sr ch =
      some (j, (mf, tf, zf))) :
    ∃ queries finalMap,
      (A.interact n y).runWithState (A.numQueries n)
        (mapGame1HvzkOracle P Msg hvzk n (A.numQueries n) y sr ch) [] =
        some (queries, (mf, tf, zf), finalMap) ∧
      j.val ≤ queries.length ∧
      (∀ (hlt : j.val < queries.length), queries[j.val] = .inr (mf, tf)) := by
  letI := P.commitmentDecEq n
  have h_def : mapGame1_hvzk_run_stmt P Msg hvzk A n y sr ch =
      match (A.interact n y).runWithState (A.numQueries n)
        (mapGame1HvzkOracle P Msg hvzk n (A.numQueries n) y sr ch) [] with
      | none => none
      | some (queries, (mf', tf', zf'), _) =>
        let jv := queries.findIdx (fun x => decide (x = .inr (mf', tf')))
        if hj : jv < A.numQueries n then
          if jv < queries.length then
            let signMsgs := queries.filterMap (fun q => match q with
              | .inl m => some m | .inr _ => none)
            if P.verify n y tf' (ch ⟨jv, hj⟩) zf' && !(signMsgs.contains mf') then
              some (⟨jv, hj⟩, (mf', tf', zf'))
            else none
          else none
        else none := by rfl
  rw [h_def] at h
  generalize h_run : (A.interact n y).runWithState (A.numQueries n)
    (mapGame1HvzkOracle P Msg hvzk n (A.numQueries n) y sr ch) [] = result at h
  rcases result with _ | ⟨queries, ⟨mf', tf', zf'⟩, finalMap⟩
  · exact absurd h nofun
  · dsimp only [] at h
    split at h
    · split at h
      · split at h
        · have hinj := Option.some.inj h
          have hj_eq := (Prod.mk.inj hinj).1
          have hrest := (Prod.mk.inj hinj).2
          have hmf : mf' = mf := (Prod.mk.inj hrest).1
          have hrest2 := (Prod.mk.inj hrest).2
          have htf_eq : tf' = tf := (Prod.mk.inj hrest2).1
          have hzf : zf' = zf := (Prod.mk.inj hrest2).2
          refine ⟨queries, finalMap, ?_, ?_, ?_⟩
          · rw [← hmf, ← htf_eq, ← hzf]
          · have hj_val : queries.findIdx (fun x => decide (x = .inr (mf', tf'))) = j.val :=
              congrArg Fin.val hj_eq
            rw [← hj_val]; exact List.findIdx_le_length
          · intro hlt
            rw [← hmf, ← htf_eq]
            have hj_val : queries.findIdx (fun x => decide (x = .inr (mf', tf'))) = j.val :=
              congrArg Fin.val hj_eq
            have hlt' : queries.findIdx (fun x => decide (x = .inr (mf', tf'))) < queries.length :=
              hj_val ▸ hlt
            have h_beq := List.findIdx_getElem (w := hlt')
            have h_at := of_decide_eq_true h_beq
            simp only [hj_val] at h_at; exact h_at
        · exact absurd h nofun
      · exact absurd h nofun
    · exact absurd h nofun

/-- When `mapGame1_hvzk_run_stmt` succeeds, verification passed. -/
private lemma mapGame1_hvzk_run_stmt_verify {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type) [∀ n, DecidableEq (Msg n)]
    (hvzk : P.SpecialHVZK) (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    (y : R.Statement n) (sr : Fin (A.numQueries n) → hvzk.SimRandomness n)
    (ch : Fin (A.numQueries n) → P.Challenge n)
    {j : Fin (A.numQueries n)} {mf : Msg n} {tf : P.Commitment n}
    {zf : P.Response n}
    (h : mapGame1_hvzk_run_stmt P Msg hvzk A n y sr ch =
      some (j, (mf, tf, zf))) :
    P.verify n y tf (ch j) zf = true := by
  simp only [mapGame1_hvzk_run_stmt] at h
  split at h
  · exact absurd h nofun
  · split at h
    · split at h
      · split at h
        · have hinj := Option.some.inj h
          have hj_eq : _ = j := congrArg Prod.fst hinj
          have hmf := congrArg Prod.fst (congrArg Prod.snd hinj)
          have htf := congrArg Prod.fst (congrArg Prod.snd (congrArg Prod.snd hinj))
          have hzf := congrArg Prod.snd (congrArg Prod.snd (congrArg Prod.snd hinj))
          subst hmf; subst htf; subst hzf; rw [← hj_eq]
          simp_all
        · exact absurd h nofun
      · exact absurd h nofun
    · exact absurd h nofun

/-- **Fork extraction (Map-based)**: when forking succeeds, special
soundness extracts a valid witness. -/
private theorem forkExtraction_le_advR_map {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    [∀ n, Nonempty (Msg n)]
    [∀ n, Fintype (R.Witness n)] [∀ n, Nonempty (R.Witness n)]
    [∀ n (w : R.Witness n) (y : R.Statement n), Decidable (R.relation n w y)]
    (kg : R.WithKeyGen)
    (ss : P.SpecialSoundness) (hvzk : P.SpecialHVZK)
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    [Fintype (hvzk.SimRandomness n)] [Nonempty (hvzk.SimRandomness n)]
    [Fintype (P.Challenge n)] [Nonempty (P.Challenge n)]
    [DecidableEq (P.Challenge n)] :
    ∃ find_n : R.Statement n → R.Witness n,
      forkProb
        (R.Witness n × (Fin (A.numQueries n) → hvzk.SimRandomness n))
        (P.Challenge n) (A.numQueries n)
        (mapGame1_hvzk_run P Msg kg hvzk A n) ≤
      uniformExpect (R.Witness n) (fun w =>
        boolToReal (decide (R.relation n (find_n (kg.keyOf n w)) (kg.keyOf n w)))) := by
  set q := A.numQueries n
  have fork_sound : ∀ (y : R.Statement n) (sr : Fin q → hvzk.SimRandomness n)
      (ch₁ ch₂ : Fin q → P.Challenge n)
      {j : Fin q} {mf₁ mf₂ : Msg n} {tf₁ tf₂ : P.Commitment n}
      {zf₁ zf₂ : P.Response n},
      mapGame1_hvzk_run_stmt P Msg hvzk A n y sr ch₁ = some (j, (mf₁, tf₁, zf₁)) →
      mapGame1_hvzk_run_stmt P Msg hvzk A n y sr
        (fun i => if i.val < j.val then ch₁ i else ch₂ i) =
        some (j, (mf₂, tf₂, zf₂)) →
      ch₁ j ≠ ch₂ j →
      R.relation n (ss.extract n y tf₁ (ch₁ j) zf₁ (ch₂ j) zf₂) y := by
    intro y sr ch₁ ch₂ j mf₁ mf₂ tf₁ tf₂ zf₁ zf₂ h₁ h₂ h_neq
    have hv₁ := mapGame1_hvzk_run_stmt_verify P Msg hvzk A n y sr ch₁ h₁
    have hv₂ := mapGame1_hvzk_run_stmt_verify P Msg hvzk A n y sr
      (fun i => if i.val < j.val then ch₁ i else ch₂ i) h₂
    have h_ch_at_j : (fun i : Fin (A.numQueries n) =>
        if i.val < j.val then ch₁ i else ch₂ i) j = ch₂ j :=
      if_neg (Nat.lt_irrefl _)
    rw [h_ch_at_j] at hv₂
    have htf : tf₁ = tf₂ := by
      obtain ⟨queries₁, _, hrun₁, hle₁, hget₁⟩ :=
        mapGame1_hvzk_run_stmt_data P Msg hvzk A n y sr ch₁ h₁
      set ch_fork : Fin (A.numQueries n) → P.Challenge n :=
        fun i => if i.val < j.val then ch₁ i else ch₂ i
      obtain ⟨queries₂, _, hrun₂, hle₂, hget₂⟩ :=
        mapGame1_hvzk_run_stmt_data P Msg hvzk A n y sr ch_fork h₂
      have h_oracle_agree : ∀ (i : Fin (A.numQueries n)), i.val < j.val →
          mapGame1HvzkOracle P Msg hvzk n (A.numQueries n) y sr ch₁ i =
          mapGame1HvzkOracle P Msg hvzk n (A.numQueries n) y sr ch_fork i := by
        intro i hi
        have h_ch_eq : ch_fork i = ch₁ i := if_pos hi
        funext map qry
        unfold mapGame1HvzkOracle
        rw [h_ch_eq]
      by_cases hjlt : j.val < queries₁.length
      · have hjlt₂ : j.val < queries₂.length :=
          OracleInteraction.runWithState_prefix_implies_length
            (A.interact n y) (A.numQueries n)
            (mapGame1HvzkOracle P Msg hvzk n (A.numQueries n) y sr ch₁)
            (mapGame1HvzkOracle P Msg hvzk n (A.numQueries n) y sr ch_fork)
            [] j.val h_oracle_agree hrun₁ hrun₂ hjlt
        have hq_eq : queries₁[j.val] = queries₂[j.val] :=
          OracleInteraction.runWithState_prefix_query_eq
            (A.interact n y) (A.numQueries n)
            (mapGame1HvzkOracle P Msg hvzk n (A.numQueries n) y sr ch₁)
            (mapGame1HvzkOracle P Msg hvzk n (A.numQueries n) y sr ch_fork)
            [] j.val h_oracle_agree hrun₁ hrun₂ hjlt hjlt₂
        have hq₁ : queries₁[j.val] = .inr (mf₁, tf₁) := hget₁ hjlt
        have hq₂ : queries₂[j.val] = .inr (mf₂, tf₂) := hget₂ hjlt₂
        have := hq₁.symm.trans (hq_eq.trans hq₂)
        exact (Prod.mk.inj (Sum.inr.inj this)).2
      · have h_agree_all : ∀ (i : Fin (A.numQueries n)),
            i.val < queries₁.length →
            mapGame1HvzkOracle P Msg hvzk n (A.numQueries n) y sr ch₁ i =
            mapGame1HvzkOracle P Msg hvzk n (A.numQueries n) y sr ch_fork i := by
          intro i hi
          exact h_oracle_agree i (lt_of_lt_of_le hi (Nat.le_of_not_lt hjlt))
        have hrun₂' :=
          OracleInteraction.runWithState_det_prefix
            (A.interact n y) (A.numQueries n)
            (mapGame1HvzkOracle P Msg hvzk n (A.numQueries n) y sr ch₁)
            (mapGame1HvzkOracle P Msg hvzk n (A.numQueries n) y sr ch_fork)
            [] hrun₁ h_agree_all
        rw [hrun₂'] at hrun₂
        have hinj := Option.some.inj hrun₂
        have hrest := (Prod.mk.inj hinj).2
        have hforg := (Prod.mk.inj hrest).1
        exact (Prod.mk.inj (Prod.mk.inj hforg).2).1
    rw [← htf] at hv₂
    exact ss.soundness n y tf₁ (ch₁ j) zf₁ (ch₂ j) zf₂ h_neq hv₁ hv₂
  let find_n : R.Statement n → R.Witness n := fun y =>
    Classical.epsilon (fun w' => R.relation n w' y)
  refine ⟨find_n, ?_⟩
  have h_mono : forkProb
      (R.Witness n × (Fin q → hvzk.SimRandomness n))
      (P.Challenge n) q
      (mapGame1_hvzk_run P Msg kg hvzk A n) ≤
    uniformExpect ((R.Witness n × (Fin q → hvzk.SimRandomness n)) ×
      (Fin q → P.Challenge n) × (Fin q → P.Challenge n))
      (fun p => boolToReal
        (decide (R.relation n (find_n (kg.keyOf n p.1.1))
          (kg.keyOf n p.1.1)))) := by
    unfold forkProb uniformExpect
    apply Finset.sum_le_sum
    intro ⟨⟨w, sr⟩, ch₁, ch₂⟩ _
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    dsimp only [mapGame1_hvzk_run]
    rcases h_run₁ : mapGame1_hvzk_run_stmt P Msg hvzk A n (kg.keyOf n w) sr ch₁
      with _ | ⟨j, mf₁, tf₁, zf₁⟩
    · exact boolToReal_nonneg _
    · dsimp only []
      rcases h_run₂ : mapGame1_hvzk_run_stmt P Msg hvzk A n (kg.keyOf n w) sr
          (fun i => if i.val < j.val then ch₁ i else ch₂ i)
        with _ | ⟨j', mf₂, tf₂, zf₂⟩
      · exact boolToReal_nonneg _
      · dsimp only []
        have h_if : (if (j : ℕ) < (j : ℕ) then ch₁ j else ch₂ j) = ch₂ j :=
          if_neg (Nat.lt_irrefl _)
        simp only [h_if]
        by_cases h_cond : j = j' ∧ ch₁ j ≠ ch₂ j
        · obtain ⟨hjj', h_neq⟩ := h_cond; subst hjj'
          have h_rel := fork_sound (kg.keyOf n w) sr ch₁ ch₂ h_run₁ h_run₂ h_neq
          have h_eps := Classical.epsilon_spec
            (p := fun w' => R.relation n w' (kg.keyOf n w)) ⟨_, h_rel⟩
          have h_rel_find : R.relation n (find_n (kg.keyOf n w)) (kg.keyOf n w) := h_eps
          have lhs_eq : boolToReal (decide (j = j ∧ ch₁ j ≠ ch₂ j)) = 1 := by
            simp [boolToReal, h_neq]
          have rhs_eq : boolToReal
              (decide (R.relation n (find_n (kg.keyOf n w)) (kg.keyOf n w))) = 1 := by
            simp [boolToReal, h_rel_find]
          linarith
        · have lhs_eq : boolToReal (decide (j = j' ∧ ch₁ j ≠ ch₂ j)) = 0 := by
            simp [boolToReal, h_cond]
          linarith [boolToReal_nonneg
            (decide (R.relation n (find_n (kg.keyOf n w))
              (kg.keyOf n w)))]
  have h_eq : uniformExpect ((R.Witness n × (Fin q → hvzk.SimRandomness n)) ×
      (Fin q → P.Challenge n) × (Fin q → P.Challenge n))
      (fun p => boolToReal (decide (R.relation n (find_n (kg.keyOf n p.1.1)) (kg.keyOf n p.1.1)))) =
    uniformExpect (R.Witness n) (fun w =>
      boolToReal (decide (R.relation n (find_n (kg.keyOf n w)) (kg.keyOf n w)))) := by
    trans uniformExpect (R.Witness n × (Fin q → hvzk.SimRandomness n))
      (fun (x : R.Witness n × (Fin q → hvzk.SimRandomness n)) =>
        boolToReal (decide (R.relation n (find_n (kg.keyOf n x.1)) (kg.keyOf n x.1))))
    · exact uniformExpect_prod_ignore_snd
        (fun (x : R.Witness n × (Fin q → hvzk.SimRandomness n)) =>
          boolToReal (decide (R.relation n (find_n (kg.keyOf n x.1)) (kg.keyOf n x.1))))
    · exact uniformExpect_prod_ignore_snd
        (fun w => boolToReal (decide (R.relation n (find_n (kg.keyOf n w)) (kg.keyOf n w))))
  linarith

/-- **Forking reduction for MapGame1_HVZK.** -/
private theorem mapGame1_hvzk_forking_bound {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    [∀ n, Nonempty (Msg n)]
    [∀ n, Fintype (R.Witness n)] [∀ n, Nonempty (R.Witness n)]
    [∀ n (w : R.Witness n) (y : R.Statement n), Decidable (R.relation n w y)]
    (kg : R.WithKeyGen)
    (ss : P.SpecialSoundness) (hvzk : P.SpecialHVZK)
    (A : ROM_EUF_CMA_Adversary P Msg) :
    ∃ B : RelationSolver R, ∀ n,
      mapGame1_hvzk_advantage P Msg kg hvzk A n ≤
        Real.sqrt ((A.numQueries n : ℝ) *
          (RelationGame R kg).advantage B n +
          (A.numQueries n : ℝ) /
            Fintype.card (P.Challenge n)) := by
  suffices per_n : ∀ n, ∃ find_n : R.Statement n → R.Witness n,
      mapGame1_hvzk_advantage P Msg kg hvzk A n ≤
        Real.sqrt ((A.numQueries n : ℝ) *
          uniformExpect (R.Witness n) (fun w =>
            boolToReal (decide (R.relation n (find_n (kg.keyOf n w)) (kg.keyOf n w)))) +
          (A.numQueries n : ℝ) / Fintype.card (P.Challenge n)) by
    exact ⟨⟨fun n => (per_n n).choose⟩, fun n => (per_n n).choose_spec⟩
  intro n
  letI := hvzk.simRandomnessFintype n
  letI := hvzk.simRandomnessNonempty n
  letI := P.challengeFintype n
  letI := P.challengeNonempty n
  letI := P.challengeDecEq n
  by_cases hq : A.numQueries n = 0
  · refine ⟨fun _ => Classical.arbitrary _, ?_⟩
    have h_adv_le : mapGame1_hvzk_advantage P Msg kg hvzk A n ≤ 0 := by
      change forkAcceptProb _ _ _ _ ≤ 0
      have h_nn := forkAcceptProb_nonneg
        (R.Witness n × (Fin (A.numQueries n) → hvzk.SimRandomness n))
        (P.Challenge n) (A.numQueries n)
        (mapGame1_hvzk_run P Msg kg hvzk A n)
      suffices h : forkAcceptProb
          (R.Witness n × (Fin (A.numQueries n) → hvzk.SimRandomness n))
          (P.Challenge n) (A.numQueries n)
          (mapGame1_hvzk_run P Msg kg hvzk A n) ≤ 0 from h
      unfold forkAcceptProb
      trans uniformExpect
        ((R.Witness n × (Fin (A.numQueries n) → hvzk.SimRandomness n)) ×
          (Fin (A.numQueries n) → P.Challenge n))
        (fun _ => (0 : ℝ))
      · apply uniformExpect_mono
        intro ⟨⟨w, sr⟩, ch⟩; dsimp only []
        cases h_run : mapGame1_hvzk_run P Msg kg hvzk A n ⟨w, sr⟩ ch with
        | none => norm_num
        | some p => exact absurd p.1.isLt (by omega)
      · exact le_of_eq (uniformExpect_const _ 0)
    linarith [Real.sqrt_nonneg ((A.numQueries n : ℝ) *
      uniformExpect (R.Witness n) (fun w =>
        boolToReal (decide (R.relation n
          ((fun _ => Classical.arbitrary _) (kg.keyOf n w)) (kg.keyOf n w)))) +
      (A.numQueries n : ℝ) / Fintype.card (P.Challenge n))]
  · have hq_pos : 0 < A.numQueries n := by omega
    let Coins := R.Witness n × (Fin (A.numQueries n) → hvzk.SimRandomness n)
    let run := mapGame1_hvzk_run P Msg kg hvzk A n
    have h_fork := forking_lemma Coins (P.Challenge n) (A.numQueries n) run hq_pos
    obtain ⟨find_n, h_extract⟩ := forkExtraction_le_advR_map P Msg kg ss hvzk A n
    have h_rearrange :
        forkAcceptProb Coins (P.Challenge n) (A.numQueries n) run ^ 2 /
          (A.numQueries n : ℝ) ≤
        uniformExpect (R.Witness n) (fun w =>
          boolToReal (decide (R.relation n (find_n (kg.keyOf n w)) (kg.keyOf n w)))) +
        forkAcceptProb Coins (P.Challenge n) (A.numQueries n) run /
          Fintype.card (P.Challenge n) := by
      linarith
    have h_acc_nn := forkAcceptProb_nonneg Coins (P.Challenge n) (A.numQueries n) run
    have h_acc_le1 := forkAcceptProb_le_one Coins (P.Challenge n) (A.numQueries n) run
    have h_Ch_pos : (0 : ℝ) < Fintype.card (P.Challenge n) :=
      Nat.cast_pos.mpr Fintype.card_pos
    refine ⟨find_n, ?_⟩
    change forkAcceptProb Coins (P.Challenge n) (A.numQueries n) run ≤ _
    exact quadratic_sqrt_bound h_acc_nn h_acc_le1
      (Nat.cast_pos.mpr hq_pos) h_Ch_pos h_rearrange


/-- **Concrete security bound for Fiat-Shamir in the ROM.**

If the Sigma protocol has special soundness, special HVZK, and
`δ`-unpredictable commitments (Def 19.7, Boneh-Shoup), there exists
a relation solver whose advantage, combined with the forking overhead,
bounds the ROM EUF-CMA advantage:

$$\mathrm{Adv}_{\mathrm{ROM\text{-}EUF\text{-}CMA}}(A, n)
  \le \sqrt{q \cdot \mathrm{Adv}_R(B, n) + q / |\mathcal{C}|}
    + q^2 \cdot \delta$$

where `q` is the total query bound and `|𝒞|` is the challenge space size.

**Proof** (Boneh-Shoup §19.6.1, Theorem 19.16):
1. *Game hop* (`rom_eq_mapGame1_hvzk_bound`): ROM → MapGame1_HVZK.
   Gap bounded by `q² · δ` via lazy sampling + collision bound + HVZK.
2. *Forking* (`mapGame1_hvzk_forking_bound`): In MapGame1_HVZK, the
   signing oracle doesn't use the witness. Forking lemma + special
   soundness extraction yields `acc ≤ √(q · Adv_R + q/|Ch|)`. -/
theorem fiatShamir_ROM_bound {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    [∀ n, Fintype (Msg n)] [∀ n, Nonempty (Msg n)]
    [∀ n, Fintype (R.Witness n)] [∀ n, Nonempty (R.Witness n)]
    [∀ n (w : R.Witness n) (y : R.Statement n), Decidable (R.relation n w y)]
    (kg : R.WithKeyGen)
    (ss : P.SpecialSoundness) (hvzk : P.SpecialHVZK)
    (A : ROM_EUF_CMA_Adversary P Msg)
    (δ : ℕ → ℝ)
    (h_unpred : P.UnpredictableCommitments δ) :
    ∃ B : RelationSolver R, ∀ n,
      (ROM_EUF_CMA_Game P Msg kg).advantage A n ≤
        Real.sqrt ((A.numQueries n : ℝ) *
          (RelationGame R kg).advantage B n +
          (A.numQueries n : ℝ) /
            Fintype.card (P.Challenge n)) +
        (A.numQueries n : ℝ) ^ 2 * δ n := by
  obtain ⟨B, hB⟩ := mapGame1_hvzk_forking_bound P Msg kg ss hvzk A
  exact ⟨B, fun n => by
    have h_rom_le := rom_eq_mapGame1_hvzk_bound P Msg kg hvzk A n δ h_unpred
    have h_fork := hB n
    linarith⟩

/-- The **Fiat-Shamir reduction**: given a ROM EUF-CMA adversary `A`,
construct a relation solver via the forking lemma and special soundness
extraction. In a concrete implementation, `B` runs `A` as a subroutine;
if `A` is efficient, so is `B`.

This is the adversary whose advantage appears in `fiatShamir_ROM_bound`
and `fiatShamir_ROM_secure` (Boneh-Shoup §19.6.1). -/
noncomputable def fiatShamirReduction {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    [∀ n, Fintype (Msg n)] [∀ n, Nonempty (Msg n)]
    [∀ n, Fintype (R.Witness n)] [∀ n, Nonempty (R.Witness n)]
    [∀ n (w : R.Witness n) (y : R.Statement n), Decidable (R.relation n w y)]
    (kg : R.WithKeyGen)
    (ss : P.SpecialSoundness) (hvzk : P.SpecialHVZK)
    (A : ROM_EUF_CMA_Adversary P Msg)
    (δ : ℕ → ℝ)
    (h_unpred : P.UnpredictableCommitments δ) : RelationSolver R :=
  (fiatShamir_ROM_bound P Msg kg ss hvzk A δ h_unpred).choose

/-- **Asymptotic security of Fiat-Shamir in the ROM.**

If:
1. The Sigma protocol has special soundness and special HVZK
2. The underlying relation is hard against `Admissible` adversaries
3. The protocol has `δ`-unpredictable commitments for negligible `δ`
4. The challenge space grows super-polynomially
5. The adversary makes polynomially many queries
6. The Fiat-Shamir reduction `fiatShamirReduction P Msg kg ss hvzk A`
   is in the `Admissible` class

Then the ROM EUF-CMA advantage is negligible.

This is the main theorem connecting Sigma protocols to practical
signatures in the random oracle model (Theorem 19.16, Boneh-Shoup).

The `Admissible` predicate captures the class of adversaries against
which the relation is assumed hard (e.g., polynomial-time solvers).
The hypothesis `hAdm` asks that the reduction from `A` to a relation
solver lands in this class — in practice, the reduction runs `A` as
a subroutine, so if `A` is efficient the reduction is efficient too. -/
theorem fiatShamir_ROM_secure {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    [∀ n, Fintype (Msg n)] [∀ n, Nonempty (Msg n)]
    [∀ n, Fintype (R.Witness n)] [∀ n, Nonempty (R.Witness n)]
    [∀ n (w : R.Witness n) (y : R.Statement n), Decidable (R.relation n w y)]
    (kg : R.WithKeyGen)
    (ss : P.SpecialSoundness) (hvzk : P.SpecialHVZK)
    {Admissible : RelationSolver R → Prop}
    (hR : (RelationGame R kg).SecureAgainst Admissible)
    (δ : ℕ → ℝ)
    (h_unpred : P.UnpredictableCommitments δ)
    (hDelta : Negligible δ)
    (hChallenge : Negligible (fun n => 1 / (Fintype.card (P.Challenge n) : ℝ)))
    (A : ROM_EUF_CMA_Adversary P Msg)
    (hPoly : PolynomiallyBounded (fun n => (A.numQueries n : ℝ)))
    (hAdm : Admissible (fiatShamirReduction P Msg kg ss hvzk A δ h_unpred)) :
    Negligible (fun n => (ROM_EUF_CMA_Game P Msg kg).advantage A n) := by
  -- B is the reduction; hB is the concrete bound from fiatShamir_ROM_bound
  let B := fiatShamirReduction P Msg kg ss hvzk A δ h_unpred
  have hB := (fiatShamir_ROM_bound P Msg kg ss hvzk A δ h_unpred).choose_spec
  -- Component 1: q · Adv_R(B, ·) is negligible
  have h_qAdv : Negligible (fun n =>
      (A.numQueries n : ℝ) * (RelationGame R kg).advantage B n) :=
    ((hR B hAdm).mul_polyBounded hPoly).mono ⟨0, fun n _ =>
      le_of_eq (congr_arg abs (mul_comm _ _))⟩
  -- Component 2: q / |Ch| is negligible
  have h_qCh : Negligible (fun n =>
      (A.numQueries n : ℝ) / (Fintype.card (P.Challenge n) : ℝ)) :=
    (hChallenge.mul_polyBounded hPoly).mono ⟨0, fun n _ =>
      le_of_eq (congr_arg abs (by ring))⟩
  -- Component 3: √(q · Adv_R + q/|Ch|) is negligible
  have h_sum_nn : ∀ n, 0 ≤ (A.numQueries n : ℝ) *
      (RelationGame R kg).advantage B n +
      (A.numQueries n : ℝ) / (Fintype.card (P.Challenge n) : ℝ) :=
    fun n => add_nonneg
      (mul_nonneg (Nat.cast_nonneg _)
        (uniformExpect_nonneg _ fun _ => boolToReal_nonneg _))
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have h_sqrt := (h_qAdv.add h_qCh).sqrt_nonneg h_sum_nn
  -- Component 4: q² · δ is negligible
  have h_q2Delta : Negligible (fun n =>
      (A.numQueries n : ℝ) ^ 2 * δ n) :=
    (hDelta.mul_polyBounded hPoly.sq).mono ⟨0, fun n _ =>
      le_of_eq (congr_arg abs (by ring))⟩
  -- Full bound is negligible
  have h_bound := h_sqrt.add h_q2Delta
  -- Transfer to advantage via concrete bound
  exact h_bound.mono ⟨0, fun n _ => by
    have h_adv_nn : 0 ≤ (ROM_EUF_CMA_Game P Msg kg).advantage A n := by
      unfold ROM_EUF_CMA_Game romCmaWinCondition romCmaOracle
      apply uniformExpect_nonneg
      intro ⟨⟨_, _⟩, _⟩
      dsimp only
      generalize h_run : (A.interact _ _).runWithState _ _ [] = result
      cases result with
      | none => exact le_refl 0
      | some val =>
          rcases val with ⟨queries, ⟨mf, tf, zf⟩, finalMap⟩
          dsimp
          split
          · split
            · exact boolToReal_nonneg _
            · exact le_refl 0
          · exact le_refl 0
    rw [abs_of_nonneg h_adv_nn]
    exact le_trans (hB n) (le_abs_self _)⟩

end
