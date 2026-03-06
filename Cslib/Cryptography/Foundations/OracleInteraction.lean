/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

@[expose] public section

/-!
# Oracle Interactions

An **oracle interaction** models an adversary that adaptively queries
an oracle, choosing each query based on the responses to all previous
queries. This is the standard model for security games where the
adversary has oracle access (e.g., signing oracles in EUF-CMA).

## Main Definitions

* `OracleInteraction Q R A` — an inductive type representing an
  adaptive sequence of queries of type `Q` receiving responses of
  type `R`, eventually producing a result of type `A`
* `OracleInteraction.run` — execute an interaction against a concrete
  oracle with a fuel budget, returning the query log and result

## Design Notes

The interaction is modeled as a free monad over the query/response
interface. The `run` function uses fuel-based recursion to ensure
termination: each query consumes one unit of fuel, and the oracle
at step `i` is indexed by `Fin fuel` to enable structural recursion
on the fuel parameter.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2014]
-/

/-- An **oracle interaction** where the adversary adaptively queries
an oracle of type `Q → R` and eventually produces a value of type `A`.

- `done a` — the adversary is finished and returns `a`
- `query q k` — the adversary asks query `q` and continues with
  the continuation `k` applied to the oracle's response -/
inductive OracleInteraction (Q : Type) (R : Type) (A : Type) where
  /-- The adversary is done and returns a result -/
  | done : A → OracleInteraction Q R A
  /-- The adversary makes a query and continues based on the response -/
  | query : Q → (R → OracleInteraction Q R A) → OracleInteraction Q R A

/-- Execute an oracle interaction against a concrete oracle, with a
fuel budget limiting the number of queries.

The oracle is `Fin fuel → Q → R`, where the `Fin fuel` index
represents which query step we are at (enabling the game to use
independent randomness for each query). Returns `none` if the
fuel is exhausted before the interaction completes, or
`some (queries, result)` with the list of queries made and the
final result.

Uses structural recursion on `fuel`. -/
def OracleInteraction.run {Q R A : Type}
    : (interaction : OracleInteraction Q R A) →
      (fuel : Nat) →
      (oracle : Fin fuel → Q → R) →
      Option (List Q × A)
  | .done a, _, _ => some ([], a)
  | .query _ _, 0, _ => none
  | .query q k, fuel + 1, oracle =>
    let response := oracle ⟨0, Nat.zero_lt_succ fuel⟩ q
    let shiftedOracle : Fin fuel → Q → R :=
      fun i => oracle ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
    match (k response).run fuel shiftedOracle with
    | none => none
    | some (qs, a) => some (q :: qs, a)

/-- The query log produced by `run` has length at most `fuel`. -/
theorem OracleInteraction.run_length_le {Q R A : Type}
    (interaction : OracleInteraction Q R A)
    (fuel : Nat) (oracle : Fin fuel → Q → R)
    {queries : List Q} {a : A}
    (h : interaction.run fuel oracle = some (queries, a)) :
    queries.length ≤ fuel := by
  induction fuel generalizing interaction queries a with
  | zero =>
    cases interaction with
    | done _ =>
      change some ([], _) = some (queries, a) at h
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
      exact Nat.le.refl
    | query _ _ =>
      change (none : Option _) = some (queries, a) at h
      exact absurd h nofun
  | succ n ih =>
    cases interaction with
    | done _ =>
      change some ([], _) = some (queries, a) at h
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
      exact Nat.zero_le _
    | query q k =>
      have h_red : OracleInteraction.run (.query q k) (n + 1) oracle =
          match (k (oracle ⟨0, Nat.zero_lt_succ n⟩ q)).run n
            (fun i : Fin n => oracle ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) with
          | none => none
          | some (qs, a') => some (q :: qs, a') := rfl
      rw [h_red] at h
      rcases h_rec : (k (oracle ⟨0, Nat.zero_lt_succ n⟩ q)).run n
        (fun i : Fin n => oracle ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
        with _ | ⟨qs, a'⟩
      · rw [h_rec] at h; exact absurd h nofun
      · rw [h_rec] at h
        obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
        exact Nat.succ_le_succ (ih _ _ h_rec)

/-- **Deterministic prefix**: if two oracles agree on the first `k`
indices, both runs complete, and both query logs have an entry at
position `k`, then the `k`-th query is the same.

This captures the fact that adaptive oracle interactions are
deterministic given the oracle responses: if two oracles agree
on the first `k` steps, the interaction reaches the same state
at step `k`, and hence issues the same query. -/
theorem OracleInteraction.run_prefix_query_eq {Q R A : Type}
    (interaction : OracleInteraction Q R A)
    (fuel : Nat) (oracle₁ oracle₂ : Fin fuel → Q → R)
    (k : Nat)
    (h_agree : ∀ (i : Fin fuel), i.val < k → oracle₁ i = oracle₂ i)
    {queries₁ queries₂ : List Q} {a₁ a₂ : A}
    (h₁ : interaction.run fuel oracle₁ = some (queries₁, a₁))
    (h₂ : interaction.run fuel oracle₂ = some (queries₂, a₂))
    (hk₁ : k < queries₁.length) (hk₂ : k < queries₂.length) :
    queries₁[k] = queries₂[k] := by
  induction fuel generalizing interaction k queries₁ queries₂ a₁ a₂ with
  | zero =>
    cases interaction with
    | done _ =>
      change some ([], _) = _ at h₁
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h₁)
      exact absurd hk₁ (by simp)
    | query _ _ =>
      exact absurd (show (none : Option _) = _ from h₁) nofun
  | succ n ih =>
    cases interaction with
    | done _ =>
      change some ([], _) = _ at h₁
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h₁)
      exact absurd hk₁ (by simp)
    | query q cont =>
      -- Reduce run in both hypotheses
      have red₁ : OracleInteraction.run (.query q cont) (n + 1) oracle₁ =
          match (cont (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ q)).run n
            (fun i : Fin n => oracle₁ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) with
          | none => none | some (qs, a') => some (q :: qs, a') := rfl
      have red₂ : OracleInteraction.run (.query q cont) (n + 1) oracle₂ =
          match (cont (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ q)).run n
            (fun i : Fin n => oracle₂ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) with
          | none => none | some (qs, a') => some (q :: qs, a') := rfl
      rw [red₁] at h₁; rw [red₂] at h₂
      -- Extract recursive results
      rcases h_rec₁ : (cont (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ q)).run n
        (fun i : Fin n => oracle₁ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
        with _ | ⟨qs₁, a₁'⟩
      · rw [h_rec₁] at h₁; exact absurd h₁ nofun
      · rw [h_rec₁] at h₁
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h₁)
        rcases h_rec₂ : (cont (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ q)).run n
          (fun i : Fin n => oracle₂ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
          with _ | ⟨qs₂, a₂'⟩
        · rw [h_rec₂] at h₂; exact absurd h₂ nofun
        · rw [h_rec₂] at h₂
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h₂)
          -- queries₁ = q :: qs₁, queries₂ = q :: qs₂
          cases k with
          | zero => rfl
          | succ k' =>
            simp only [List.length_cons, Nat.succ_lt_succ_iff] at hk₁ hk₂
            show qs₁[k'] = qs₂[k']
            -- Oracle responses at step 0 agree (0 < k'+1)
            have h_r : oracle₁ ⟨0, Nat.zero_lt_succ n⟩ q =
                oracle₂ ⟨0, Nat.zero_lt_succ n⟩ q :=
              congrFun (h_agree ⟨0, Nat.zero_lt_succ n⟩ (Nat.zero_lt_succ k')) q
            -- So the continuations are the same
            rw [h_r] at h_rec₁
            exact ih (cont (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ q))
              (fun i : Fin n => oracle₁ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
              (fun i : Fin n => oracle₂ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
              k'
              (fun i hi => h_agree ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
                (Nat.succ_lt_succ hi))
              h_rec₁ h_rec₂ hk₁ hk₂

/-- **Prefix length preservation**: if two oracles agree on the first
`k` indices, both runs complete, and the first run has `k < queries₁.length`,
then the second run also has `k < queries₂.length`.

This captures the fact that the interaction's decision to continue or
terminate at step `k` depends only on oracle responses at steps `< k`. -/
theorem OracleInteraction.run_prefix_implies_length {Q R A : Type}
    (interaction : OracleInteraction Q R A)
    (fuel : Nat) (oracle₁ oracle₂ : Fin fuel → Q → R)
    (k : Nat)
    (h_agree : ∀ (i : Fin fuel), i.val < k → oracle₁ i = oracle₂ i)
    {queries₁ queries₂ : List Q} {a₁ a₂ : A}
    (h₁ : interaction.run fuel oracle₁ = some (queries₁, a₁))
    (h₂ : interaction.run fuel oracle₂ = some (queries₂, a₂))
    (hk₁ : k < queries₁.length) :
    k < queries₂.length := by
  induction fuel generalizing interaction k queries₁ queries₂ a₁ a₂ with
  | zero =>
    cases interaction with
    | done _ =>
      change some ([], _) = _ at h₁
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h₁)
      exact absurd hk₁ (by simp)
    | query _ _ =>
      exact absurd (show (none : Option _) = _ from h₁) nofun
  | succ n ih =>
    cases interaction with
    | done _ =>
      change some ([], _) = _ at h₁
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h₁)
      exact absurd hk₁ (by simp)
    | query q cont =>
      have red₁ : OracleInteraction.run (.query q cont) (n + 1) oracle₁ =
          match (cont (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ q)).run n
            (fun i : Fin n => oracle₁ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) with
          | none => none | some (qs, a') => some (q :: qs, a') := rfl
      have red₂ : OracleInteraction.run (.query q cont) (n + 1) oracle₂ =
          match (cont (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ q)).run n
            (fun i : Fin n => oracle₂ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) with
          | none => none | some (qs, a') => some (q :: qs, a') := rfl
      rw [red₁] at h₁; rw [red₂] at h₂
      rcases h_rec₁ : (cont (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ q)).run n
        (fun i : Fin n => oracle₁ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
        with _ | ⟨qs₁, a₁'⟩
      · rw [h_rec₁] at h₁; exact absurd h₁ nofun
      · rw [h_rec₁] at h₁
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h₁)
        rcases h_rec₂ : (cont (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ q)).run n
          (fun i : Fin n => oracle₂ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
          with _ | ⟨qs₂, a₂'⟩
        · rw [h_rec₂] at h₂; exact absurd h₂ nofun
        · rw [h_rec₂] at h₂
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h₂)
          cases k with
          | zero => simp [List.length_cons]
          | succ k' =>
            simp only [List.length_cons, Nat.succ_lt_succ_iff] at hk₁ ⊢
            have h_r : oracle₁ ⟨0, Nat.zero_lt_succ n⟩ q =
                oracle₂ ⟨0, Nat.zero_lt_succ n⟩ q :=
              congrFun (h_agree ⟨0, Nat.zero_lt_succ n⟩ (Nat.zero_lt_succ k')) q
            rw [h_r] at h_rec₁
            exact ih (cont (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ q))
              (fun i : Fin n => oracle₁ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
              (fun i : Fin n => oracle₂ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
              k'
              (fun i hi => h_agree ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
                (Nat.succ_lt_succ hi))
              h_rec₁ h_rec₂ hk₁

/-- **Deterministic prefix (full)**: if two oracles agree on all indices
`< queries.length`, and the first run succeeds producing `(queries, a)`,
then the second run produces the same `(queries, a)`.

This strengthens `run_prefix_query_eq` from agreement at a single position
to identical outputs: if the oracles agree on all steps the interaction
actually used, the interaction is fully deterministic. -/
theorem OracleInteraction.run_det_prefix {Q R A : Type}
    (interaction : OracleInteraction Q R A)
    (fuel : Nat) (oracle₁ oracle₂ : Fin fuel → Q → R)
    {queries : List Q} {a : A}
    (h₁ : interaction.run fuel oracle₁ = some (queries, a))
    (h_agree : ∀ (i : Fin fuel), i.val < queries.length →
               oracle₁ i = oracle₂ i) :
    interaction.run fuel oracle₂ = some (queries, a) := by
  induction fuel generalizing interaction queries a with
  | zero =>
    cases interaction with
    | done a' =>
      change some ([], a') = some (queries, a) at h₁
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h₁)
      rfl
    | query _ _ =>
      exact absurd (show (none : Option _) = _ from h₁) nofun
  | succ n ih =>
    cases interaction with
    | done a' =>
      change some ([], a') = some (queries, a) at h₁
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h₁)
      rfl
    | query q k =>
      have red₁ : OracleInteraction.run (.query q k) (n + 1) oracle₁ =
          match (k (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ q)).run n
            (fun i : Fin n => oracle₁ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) with
          | none => none | some (qs, a') => some (q :: qs, a') := rfl
      rw [red₁] at h₁
      rcases h_rec : (k (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ q)).run n
        (fun i : Fin n => oracle₁ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
        with _ | ⟨qs, a'⟩
      · rw [h_rec] at h₁; exact absurd h₁ nofun
      · rw [h_rec] at h₁
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h₁)
        -- queries = q :: qs, so queries.length = qs.length + 1
        -- Oracle responses at step 0 agree (0 < (q :: qs).length)
        have h_r : oracle₁ ⟨0, Nat.zero_lt_succ n⟩ q =
            oracle₂ ⟨0, Nat.zero_lt_succ n⟩ q :=
          congrFun (h_agree ⟨0, Nat.zero_lt_succ n⟩
            (by simp [List.length_cons])) q
        -- Apply IH with shifted oracles
        have h_ih := ih (k (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ q))
          (fun i : Fin n => oracle₁ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
          (fun i : Fin n => oracle₂ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
          h_rec
          (fun i hi => h_agree ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
            (by simp [List.length_cons]; omega))
        -- Now show run oracle₂ = some (q :: qs, a)
        have red₂ : OracleInteraction.run (.query q k) (n + 1) oracle₂ =
            match (k (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ q)).run n
              (fun i : Fin n => oracle₂ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) with
            | none => none | some (qs, a') => some (q :: qs, a') := rfl
        rw [red₂, ← h_r, h_ih]

/-- Execute an oracle interaction against a **stateful** oracle, with a
fuel budget. The oracle at each step receives the current state `S` and
returns a response along with an updated state.

Returns `none` if fuel is exhausted, otherwise
`some (queries, result, finalState)`.
Uses structural recursion on `fuel`. -/
def OracleInteraction.runWithState {Q R A S : Type}
    : (interaction : OracleInteraction Q R A) →
      (fuel : Nat) →
      (oracle : Fin fuel → S → Q → R × S) →
      (initState : S) →
      Option (List Q × A × S)
  | .done a, _, _, s => some ([], a, s)
  | .query _ _, 0, _, _ => none
  | .query q k, fuel + 1, oracle, s =>
    let (response, s') := oracle ⟨0, Nat.zero_lt_succ fuel⟩ s q
    let shiftedOracle : Fin fuel → S → Q → R × S :=
      fun i => oracle ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
    match (k response).runWithState fuel shiftedOracle s' with
    | none => none
    | some (qs, a, sf) => some (q :: qs, a, sf)

/-- **Deterministic prefix (stateful)**: if two stateful oracles agree on
the first `k` indices, both runs complete from the same initial state,
and both query logs have an entry at position `k`, then the `k`-th query
is the same. -/
theorem OracleInteraction.runWithState_prefix_query_eq {Q R A S : Type}
    (interaction : OracleInteraction Q R A)
    (fuel : Nat) (oracle₁ oracle₂ : Fin fuel → S → Q → R × S)
    (s : S) (k : Nat)
    (h_agree : ∀ (i : Fin fuel), i.val < k → oracle₁ i = oracle₂ i)
    {queries₁ queries₂ : List Q} {a₁ a₂ : A} {sf₁ sf₂ : S}
    (h₁ : interaction.runWithState fuel oracle₁ s = some (queries₁, a₁, sf₁))
    (h₂ : interaction.runWithState fuel oracle₂ s = some (queries₂, a₂, sf₂))
    (hk₁ : k < queries₁.length) (hk₂ : k < queries₂.length) :
    queries₁[k] = queries₂[k] := by
  induction fuel generalizing interaction k queries₁ queries₂ a₁ a₂ sf₁ sf₂ s with
  | zero =>
    cases interaction with
    | done _ =>
      change some ([], _, _) = _ at h₁
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h₁)
      exact absurd hk₁ (by simp)
    | query _ _ =>
      exact absurd (show (none : Option _) = _ from h₁) nofun
  | succ n ih =>
    cases interaction with
    | done _ =>
      change some ([], _, _) = _ at h₁
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h₁)
      exact absurd hk₁ (by simp)
    | query q cont =>
      have red₁ : OracleInteraction.runWithState (.query q cont) (n + 1) oracle₁ s =
          match (cont (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ s q).1).runWithState n
            (fun i : Fin n => oracle₁ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
            (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ s q).2 with
          | none => none | some (qs, a', sf') => some (q :: qs, a', sf') := rfl
      have red₂ : OracleInteraction.runWithState (.query q cont) (n + 1) oracle₂ s =
          match (cont (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ s q).1).runWithState n
            (fun i : Fin n => oracle₂ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
            (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ s q).2 with
          | none => none | some (qs, a', sf') => some (q :: qs, a', sf') := rfl
      rw [red₁] at h₁; rw [red₂] at h₂
      rcases h_rec₁ : (cont (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ s q).1).runWithState n
        (fun i : Fin n => oracle₁ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
        (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ s q).2
        with _ | ⟨qs₁, a₁', sf₁'⟩
      · rw [h_rec₁] at h₁; exact absurd h₁ nofun
      · rw [h_rec₁] at h₁
        obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h₁)
        rcases h_rec₂ : (cont (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ s q).1).runWithState n
          (fun i : Fin n => oracle₂ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
          (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ s q).2
          with _ | ⟨qs₂, a₂', sf₂'⟩
        · rw [h_rec₂] at h₂; exact absurd h₂ nofun
        · rw [h_rec₂] at h₂
          obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h₂)
          cases k with
          | zero => rfl
          | succ k' =>
            simp only [List.length_cons, Nat.succ_lt_succ_iff] at hk₁ hk₂
            show qs₁[k'] = qs₂[k']
            have h_r : oracle₁ ⟨0, Nat.zero_lt_succ n⟩ s q =
                oracle₂ ⟨0, Nat.zero_lt_succ n⟩ s q :=
              congrFun (congrFun (h_agree ⟨0, Nat.zero_lt_succ n⟩
                (Nat.zero_lt_succ k')) s) q
            rw [h_r] at h_rec₁
            exact ih (cont (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ s q).1)
              (fun i : Fin n => oracle₁ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
              (fun i : Fin n => oracle₂ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
              (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ s q).2
              k'
              (fun i hi => h_agree ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
                (Nat.succ_lt_succ hi))
              h_rec₁ h_rec₂ hk₁ hk₂

/-- **Prefix length preservation (stateful)**: if two stateful oracles
agree on the first `k` indices, both runs complete from the same initial
state, and the first run has `k < queries₁.length`, then the second run
also has `k < queries₂.length`. -/
theorem OracleInteraction.runWithState_prefix_implies_length {Q R A S : Type}
    (interaction : OracleInteraction Q R A)
    (fuel : Nat) (oracle₁ oracle₂ : Fin fuel → S → Q → R × S)
    (s : S) (k : Nat)
    (h_agree : ∀ (i : Fin fuel), i.val < k → oracle₁ i = oracle₂ i)
    {queries₁ queries₂ : List Q} {a₁ a₂ : A} {sf₁ sf₂ : S}
    (h₁ : interaction.runWithState fuel oracle₁ s = some (queries₁, a₁, sf₁))
    (h₂ : interaction.runWithState fuel oracle₂ s = some (queries₂, a₂, sf₂))
    (hk₁ : k < queries₁.length) :
    k < queries₂.length := by
  induction fuel generalizing interaction k queries₁ queries₂ a₁ a₂ sf₁ sf₂ s with
  | zero =>
    cases interaction with
    | done _ =>
      change some ([], _, _) = _ at h₁
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h₁)
      exact absurd hk₁ (by simp)
    | query _ _ =>
      exact absurd (show (none : Option _) = _ from h₁) nofun
  | succ n ih =>
    cases interaction with
    | done _ =>
      change some ([], _, _) = _ at h₁
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h₁)
      exact absurd hk₁ (by simp)
    | query q cont =>
      have red₁ : OracleInteraction.runWithState (.query q cont) (n + 1) oracle₁ s =
          match (cont (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ s q).1).runWithState n
            (fun i : Fin n => oracle₁ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
            (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ s q).2 with
          | none => none | some (qs, a', sf') => some (q :: qs, a', sf') := rfl
      have red₂ : OracleInteraction.runWithState (.query q cont) (n + 1) oracle₂ s =
          match (cont (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ s q).1).runWithState n
            (fun i : Fin n => oracle₂ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
            (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ s q).2 with
          | none => none | some (qs, a', sf') => some (q :: qs, a', sf') := rfl
      rw [red₁] at h₁; rw [red₂] at h₂
      rcases h_rec₁ : (cont (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ s q).1).runWithState n
        (fun i : Fin n => oracle₁ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
        (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ s q).2
        with _ | ⟨qs₁, a₁', sf₁'⟩
      · rw [h_rec₁] at h₁; exact absurd h₁ nofun
      · rw [h_rec₁] at h₁
        obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h₁)
        rcases h_rec₂ : (cont (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ s q).1).runWithState n
          (fun i : Fin n => oracle₂ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
          (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ s q).2
          with _ | ⟨qs₂, a₂', sf₂'⟩
        · rw [h_rec₂] at h₂; exact absurd h₂ nofun
        · rw [h_rec₂] at h₂
          obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h₂)
          cases k with
          | zero => simp [List.length_cons]
          | succ k' =>
            simp only [List.length_cons, Nat.succ_lt_succ_iff] at hk₁ ⊢
            have h_r : oracle₁ ⟨0, Nat.zero_lt_succ n⟩ s q =
                oracle₂ ⟨0, Nat.zero_lt_succ n⟩ s q :=
              congrFun (congrFun (h_agree ⟨0, Nat.zero_lt_succ n⟩
                (Nat.zero_lt_succ k')) s) q
            rw [h_r] at h_rec₁
            exact ih (cont (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ s q).1)
              (fun i : Fin n => oracle₁ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
              (fun i : Fin n => oracle₂ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
              (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ s q).2
              k'
              (fun i hi => h_agree ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
                (Nat.succ_lt_succ hi))
              h_rec₁ h_rec₂ hk₁

/-- **Deterministic prefix (stateful, full)**: if two stateful oracles
agree on all indices `< queries.length`, both start from the same state,
and the first run succeeds producing `(queries, a, sf)`, then the second
run produces the same result. -/
theorem OracleInteraction.runWithState_det_prefix {Q R A S : Type}
    (interaction : OracleInteraction Q R A)
    (fuel : Nat) (oracle₁ oracle₂ : Fin fuel → S → Q → R × S)
    (s : S)
    {queries : List Q} {a : A} {sf : S}
    (h₁ : interaction.runWithState fuel oracle₁ s = some (queries, a, sf))
    (h_agree : ∀ (i : Fin fuel), i.val < queries.length →
               oracle₁ i = oracle₂ i) :
    interaction.runWithState fuel oracle₂ s = some (queries, a, sf) := by
  induction fuel generalizing interaction queries a sf s with
  | zero =>
    cases interaction with
    | done a' =>
      change some ([], a', s) = some (queries, a, sf) at h₁
      obtain ⟨rfl, hrest⟩ := Prod.mk.inj (Option.some.inj h₁)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrest
      rfl
    | query _ _ =>
      exact absurd (show (none : Option _) = _ from h₁) nofun
  | succ n ih =>
    cases interaction with
    | done a' =>
      change some ([], a', s) = some (queries, a, sf) at h₁
      obtain ⟨rfl, hrest⟩ := Prod.mk.inj (Option.some.inj h₁)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrest
      rfl
    | query q k =>
      have red₁ : OracleInteraction.runWithState (.query q k) (n + 1) oracle₁ s =
          match (k (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ s q).1).runWithState n
            (fun i : Fin n => oracle₁ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
            (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ s q).2 with
          | none => none | some (qs, a', sf') => some (q :: qs, a', sf') := rfl
      rw [red₁] at h₁
      rcases h_rec : (k (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ s q).1).runWithState n
        (fun i : Fin n => oracle₁ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
        (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ s q).2
        with _ | ⟨qs, a', sf'⟩
      · rw [h_rec] at h₁; exact absurd h₁ nofun
      · rw [h_rec] at h₁
        obtain ⟨rfl, hrest⟩ := Prod.mk.inj (Option.some.inj h₁)
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrest
        have h_r : oracle₁ ⟨0, Nat.zero_lt_succ n⟩ s q =
            oracle₂ ⟨0, Nat.zero_lt_succ n⟩ s q :=
          congrFun (congrFun (h_agree ⟨0, Nat.zero_lt_succ n⟩
            (by simp [List.length_cons])) s) q
        have h_ih := ih (k (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ s q).1)
          (fun i : Fin n => oracle₁ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
          (fun i : Fin n => oracle₂ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
          (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ s q).2
          h_rec
          (fun i hi => h_agree ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
            (by simp [List.length_cons]; omega))
        have red₂ : OracleInteraction.runWithState (.query q k) (n + 1) oracle₂ s =
            match (k (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ s q).1).runWithState n
              (fun i : Fin n => oracle₂ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
              (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ s q).2 with
            | none => none | some (qs, a', sf') => some (q :: qs, a', sf') := rfl
        rw [red₂, ← h_r, h_ih]

end
