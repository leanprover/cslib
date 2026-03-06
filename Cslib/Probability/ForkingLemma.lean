/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Probability.Discrete

@[expose] public section

/-!
# The General Forking Lemma

The **Forking Lemma** (Bellare-Neven 2006) is a general probabilistic tool
for extracting two accepting transcripts from a single algorithm by
replaying it with a modified random oracle.

## Setup

An algorithm takes random coins and a random oracle table `h : Fin q → R`
(q entries from a finite type R). It either fails or outputs a "fork index"
`j : Fin q` and some result. **Forking** means: run once with `h₁`, get
index `j`; build `h_fork` agreeing with `h₁` on indices `< j` but using
fresh randomness `h₂` on indices `≥ j`; run again with `h_fork`.

## Main Definitions

* `forkAcceptProb` — acceptance probability of a randomized oracle algorithm
* `forkProb` — probability that forking produces two runs with matching
  fork index but differing oracle response at that index

## Main Results

* `forking_lemma` — the general forking lemma bound:
  `forkProb ≥ acc²/q - acc/|R|`

## References

* [M. Bellare, G. Neven, *Multi-Signatures in the Plain Public-Key Model
  and a General Forking Lemma*][BellareNeven2006]
* [D. Pointcheval, J. Stern, *Security Arguments for Digital Signatures
  and Blind Signatures*][PointchevalStern2000]
-/

namespace Cslib.Probability

/-- Acceptance probability of a randomized oracle algorithm.

The algorithm takes random coins and a random oracle table
`h : Fin q → R` and either fails (`none`) or outputs a fork index
`j : Fin q` and some result. -/
noncomputable def forkAcceptProb
    {α : Type} (Coins R : Type) [Fintype Coins] [Nonempty Coins]
    [Fintype R] [Nonempty R] (q : ℕ)
    (run : Coins → (Fin q → R) → Option (Fin q × α)) : ℝ :=
  uniformExpect (Coins × (Fin q → R)) (fun ⟨c, h⟩ =>
    match run c h with | none => 0 | some _ => 1)

/-- Forking success probability.

Fork an algorithm: run once with `h₁` to get index `j`, build `h_fork`
agreeing with `h₁` on indices `< j` but using fresh `h₂` on indices
`≥ j`, run again. Forking succeeds if both runs output the same index
`j` and the oracle responses at `j` differ. -/
noncomputable def forkProb
    {α : Type} (Coins R : Type) [Fintype Coins] [Nonempty Coins]
    [Fintype R] [Nonempty R] [DecidableEq R] (q : ℕ)
    (run : Coins → (Fin q → R) → Option (Fin q × α)) : ℝ :=
  uniformExpect (Coins × (Fin q → R) × (Fin q → R))
    (fun ⟨c, h₁, h₂⟩ =>
      match run c h₁ with
      | none => 0
      | some (j, _) =>
        let h_fork : Fin q → R :=
          fun i => if i.val < j.val then h₁ i else h₂ i
        match run c h_fork with
        | none => 0
        | some (j', _) =>
          boolToReal (decide (j = j' ∧ h₁ j ≠ h_fork j)))

/-- `forkAcceptProb` is nonneg: it's the expected value of a {0,1}-valued function. -/
theorem forkAcceptProb_nonneg
    {α : Type} (Coins R : Type) [Fintype Coins] [Nonempty Coins]
    [Fintype R] [Nonempty R] (q : ℕ)
    (run : Coins → (Fin q → R) → Option (Fin q × α)) :
    0 ≤ forkAcceptProb Coins R q run := by
  apply uniformExpect_nonneg
  intro ⟨c, h⟩; dsimp only []
  split <;> norm_num

/-- `forkAcceptProb` is at most 1: it's the expected value of a function bounded by 1. -/
theorem forkAcceptProb_le_one
    {α : Type} (Coins R : Type) [Fintype Coins] [Nonempty Coins]
    [Fintype R] [Nonempty R] (q : ℕ)
    (run : Coins → (Fin q → R) → Option (Fin q × α)) :
    forkAcceptProb Coins R q run ≤ 1 := by
  unfold forkAcceptProb
  calc uniformExpect (Coins × (Fin q → R)) (fun ⟨c, h⟩ =>
        match run c h with | none => 0 | some _ => 1)
      ≤ uniformExpect (Coins × (Fin q → R)) (fun _ => (1 : ℝ)) := by
        apply uniformExpect_mono
        intro ⟨c, h⟩; dsimp only []
        split <;> norm_num
    _ = 1 := uniformExpect_const _ 1

/-- Acceptance probability for fixed coins `c`, averaged over oracle tables. -/
private noncomputable def perCoinsAcc
    {α : Type} {R : Type} [Fintype R] [Nonempty R] {q : ℕ}
    (run : Coins → (Fin q → R) → Option (Fin q × α)) (c : Coins) : ℝ :=
  uniformExpect (Fin q → R) (fun h =>
    match run c h with | none => 0 | some _ => 1)

/-- Acceptance probability for fixed coins `c` at a specific index `j`. -/
private noncomputable def perIndexAcc
    {α : Type} {R : Type} [Fintype R] [Nonempty R] {q : ℕ}
    (run : Coins → (Fin q → R) → Option (Fin q × α)) (c : Coins) (j : Fin q) : ℝ :=
  uniformExpect (Fin q → R) (fun h =>
    match run c h with | none => 0 | some (j', _) => if j' = j then 1 else 0)

/-- The acceptance probability decomposes as a sum over indices:
`perCoinsAcc c = ∑_j perIndexAcc c j`. -/
private theorem perCoinsAcc_eq_sum
    {α : Type} {R : Type} [Fintype R] [Nonempty R] {q : ℕ}
    (run : Coins → (Fin q → R) → Option (Fin q × α)) (c : Coins) :
    perCoinsAcc run c = ∑ j : Fin q, perIndexAcc run c j := by
  unfold perCoinsAcc perIndexAcc
  rw [← uniformExpect_finsum]
  congr 1; ext h
  match hrun : run c h with
  | none => simp [Finset.sum_const_zero]
  | some (j', _) =>
    symm
    simp only [eq_comm (a := j')]
    rw [Finset.sum_ite_eq']
    simp

/-- Per-coins fork probability: fork success probability for fixed coins `c`. -/
private noncomputable def perCoinsFork
    {α : Type} {R : Type} [Fintype R] [Nonempty R] [DecidableEq R] {q : ℕ}
    (run : Coins → (Fin q → R) → Option (Fin q × α)) (c : Coins) : ℝ :=
  uniformExpect ((Fin q → R) × (Fin q → R)) (fun ⟨h₁, h₂⟩ =>
    match run c h₁ with
    | none => 0
    | some (j, _) =>
      let h_fork : Fin q → R := fun i => if i.val < j.val then h₁ i else h₂ i
      match run c h_fork with
      | none => 0
      | some (j', _) =>
        boolToReal (decide (j = j' ∧ h₁ j ≠ h_fork j)))

/-- Per-index fork contribution: expected value of the indicator that the
first run gives index `j`, the second run (with merge at `j`) also gives
index `j`, and the oracle responses at `j` differ. -/
private noncomputable def perIndexFork
    {α : Type} {R : Type} [Fintype R] [Nonempty R] [DecidableEq R] {q : ℕ}
    (run : Coins → (Fin q → R) → Option (Fin q × α)) (c : Coins) (j : Fin q) : ℝ :=
  uniformExpect ((Fin q → R) × (Fin q → R)) (fun ⟨h₁, h₂⟩ =>
    let acc₁ : ℝ := match run c h₁ with
      | none => 0
      | some (j', _) => if j' = j then 1 else 0
    let h_fork : Fin q → R := fun i => if i.val < j.val then h₁ i else h₂ i
    let acc₂ : ℝ := match run c h_fork with
      | none => 0
      | some (j', _) => if j' = j then 1 else 0
    acc₁ * acc₂ * if h₁ j = h₂ j then 0 else 1)

/-- The fork integrand decomposes as a sum of per-index contributions. -/
private theorem perCoinsFork_eq_sum
    {α : Type} {R : Type} [Fintype R] [Nonempty R] [DecidableEq R] {q : ℕ}
    (run : Coins → (Fin q → R) → Option (Fin q × α)) (c : Coins) :
    perCoinsFork run c = ∑ j : Fin q, perIndexFork run c j := by
  simp only [perCoinsFork, perIndexFork, ← uniformExpect_finsum]
  congr 1; ext ⟨h₁, h₂⟩
  dsimp only []
  rcases hrun : run c h₁ with _ | ⟨j, a⟩
  · -- When first run fails: both sides are 0
    simp
  · -- When first run gives (j, a): sum collapses to j₀ = j
    -- Simplify: j.val < j.val is false, so h_fork j = h₂ j
    simp only [show ¬ (j.val < j.val) from Nat.lt_irrefl _, ite_false]
    -- Collapse the sum using sum_eq_single: only the x = j term is nonzero
    rw [Finset.sum_eq_single j]
    · -- Main: show the j-th term equals the LHS
      simp only [ite_true, one_mul]
      -- Case split on the second run
      rcases run c (fun i => if i.val < j.val then h₁ i else h₂ i) with _ | ⟨j', b⟩
      · simp
      · by_cases h_jj' : j = j'
        · subst h_jj'
          simp only [true_and, ite_true]
          by_cases h_eq : h₁ j = h₂ j
          · simp [boolToReal, h_eq]
          · simp [boolToReal, h_eq]
        · have h_jj'2 : j' ≠ j := Ne.symm h_jj'
          simp [boolToReal, h_jj', h_jj'2]
    · -- All x ≠ j terms vanish
      intro x _ hxj
      simp [Ne.symm hxj]
    · -- j ∈ univ (trivial)
      intro h; exact absurd (Finset.mem_univ j) h

/-- Collision bound: the probability that the first run gives index `j` AND
`h₁(j) = h₂(j)` is exactly `perIndexAcc(c,j) / |R|`. -/
private theorem collision_bound
    {α : Type} {R : Type} [Fintype R] [Nonempty R] [DecidableEq R] {q : ℕ}
    (run : Coins → (Fin q → R) → Option (Fin q × α)) (c : Coins) (j : Fin q) :
    uniformExpect ((Fin q → R) × (Fin q → R)) (fun ⟨h₁, h₂⟩ =>
      (match run c h₁ with
        | none => (0 : ℝ)
        | some (j', _) => if j' = j then 1 else 0) *
      if h₁ j = h₂ j then 1 else 0) =
    perIndexAcc run c j / Fintype.card R := by
  -- Fubini: separate h₁ and h₂
  rw [uniformExpect_prod]
  -- For fixed h₁, factor out acc₁ (constant wrt h₂)
  -- and show E_{h₂}[1{h₁(j) = h₂(j)}] = 1/|R|
  have h_marginal : ∀ (r : R),
      uniformExpect (Fin q → R) (fun h₂ => if r = h₂ j then (1 : ℝ) else 0) =
      1 / Fintype.card R := by
    intro r
    -- Use funSplitAt to decompose h₂ as (h₂(j), rest)
    rw [show (fun h₂ : Fin q → R => if r = h₂ j then (1 : ℝ) else 0) =
        (fun p : R × ({i : Fin q // i ≠ j} → R) => if r = p.1 then (1 : ℝ) else 0) ∘
        (Equiv.funSplitAt j R) from by ext h₂; simp [Equiv.funSplitAt],
      uniformExpect_congr (Equiv.funSplitAt j R)]
    -- Decompose as E_{rj}[E_{rest}[...]] and the inner is constant
    rw [uniformExpect_prod]
    -- Reduce (a, b).1 to a
    conv_lhs =>
      arg 2; ext a
      rw [show (fun b : {i : Fin q // i ≠ j} → R => if r = (a, b).1 then (1 : ℝ) else 0) =
          (fun _ => if r = a then (1 : ℝ) else 0) from rfl]
      rw [uniformExpect_const]
    -- E_a[1{r = a}] = 1/|R|
    rw [uniformExpect_eq]
    simp only [eq_comm (a := r), Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring
  -- Now simplify the inner expectation
  conv_lhs =>
    arg 2; ext h₁
    rw [show (fun h₂ : Fin q → R =>
        (match run c h₁ with
          | none => (0 : ℝ)
          | some (j', _) => if j' = j then 1 else 0) *
        if h₁ j = h₂ j then 1 else 0) =
      (fun h₂ => (match run c h₁ with
          | none => (0 : ℝ)
          | some (j', _) => if j' = j then 1 else 0) *
        ((fun h₂ : Fin q → R => if h₁ j = h₂ j then (1 : ℝ) else 0) h₂)) from rfl,
      uniformExpect_smul, h_marginal]
  -- E_{h₁}[acc₁ * (1/|R|)] = (1/|R|) * perIndexAcc
  unfold perIndexAcc
  rw [show (fun h₁ : Fin q → R =>
      (match run c h₁ with
        | none => (0 : ℝ)
        | some (j', _) => if j' = j then 1 else 0) *
      (1 / ↑(Fintype.card R))) =
    (fun h₁ => (1 / Fintype.card R : ℝ) *
      (match run c h₁ with
        | none => (0 : ℝ)
        | some (j', _) => if j' = j then 1 else 0)) from by ext; ring,
    uniformExpect_smul]
  ring

/-- Correlation bound: `E[1{first gives j} · 1{second gives j}] ≥ perIndexAcc(c,j)²`.
Uses oracle table split + independence + Jensen. -/
private theorem correlation_bound
    {α : Type} {R : Type} [Fintype R] [Nonempty R] {q : ℕ}
    (run : Coins → (Fin q → R) → Option (Fin q × α)) (c : Coins) (j : Fin q) :
    uniformExpect ((Fin q → R) × (Fin q → R)) (fun ⟨h₁, h₂⟩ =>
      (match run c h₁ with
        | none => (0 : ℝ)
        | some (j', _) => if j' = j then 1 else 0) *
      (match run c (fun i => if i.val < j.val then h₁ i else h₂ i) with
        | none => (0 : ℝ)
        | some (j', _) => if j' = j then 1 else 0)) ≥
    perIndexAcc run c j ^ 2 := by
  -- Abbreviation for the indicator function
  let ind : (Fin q → R) → ℝ := fun h =>
    match run c h with | none => 0 | some (j', _) => if j' = j then 1 else 0
  -- Prefix/suffix split equiv
  let P := {i : Fin q // i.val < j.val}
  let S := {i : Fin q // ¬(i.val < j.val)}
  let e := Equiv.piEquivPiSubtypeProd (fun i : Fin q => i.val < j.val) (fun _ => R)
  -- β(p) = conditional expectation of ind given prefix p
  let β : (P → R) → ℝ := fun p =>
    uniformExpect (S → R) (fun s => ind (e.symm (p, s)))
  -- Step A: LHS = E_p[β(p)²]
  -- Key merge identity: merge(e.symm(p₁,s₁), e.symm(p₂,s₂)) = e.symm(p₁,s₂)
  have merge_eq : ∀ (p₁ : P → R) (s₁ : S → R) (p₂ : P → R) (s₂ : S → R),
      (fun i : Fin q => if i.val < j.val then e.symm (p₁, s₁) i else e.symm (p₂, s₂) i) =
      e.symm (p₁, s₂) := by
    intro p₁ s₁ p₂ s₂; funext i
    -- e.symm applies dite on i.val < j.val: choosing p or s component
    -- The outer ite selects which e.symm to use
    -- When i.val < j.val: outer selects e.symm(p₁,s₁), inner dite selects p₁
    -- When ¬(i.val < j.val): outer selects e.symm(p₂,s₂), inner dite selects s₂
    -- Both match e.symm(p₁,s₂): dite selects p₁ or s₂
    by_cases h : i.val < j.val
    · -- i.val < j.val: both sides give p₁ ⟨i, h⟩
      simp only [h, ite_true]
      show e.symm (p₁, s₁) i = e.symm (p₁, s₂) i
      change (if h' : i.val < j.val then p₁ ⟨i, h'⟩ else s₁ ⟨i, h'⟩) =
             (if h' : i.val < j.val then p₁ ⟨i, h'⟩ else s₂ ⟨i, h'⟩)
      simp [h]
    · -- ¬(i.val < j.val): both sides give s₂ ⟨i, h⟩
      simp only [h, ite_false]
      show e.symm (p₂, s₂) i = e.symm (p₁, s₂) i
      change (if h' : i.val < j.val then p₂ ⟨i, h'⟩ else s₂ ⟨i, h'⟩) =
             (if h' : i.val < j.val then p₁ ⟨i, h'⟩ else s₂ ⟨i, h'⟩)
      simp [h]
  have lhs_eq : uniformExpect ((Fin q → R) × (Fin q → R)) (fun ⟨h₁, h₂⟩ =>
      ind h₁ * ind (fun i => if i.val < j.val then h₁ i else h₂ i)) =
      uniformExpect (P → R) (fun p => β p ^ 2) := by
    -- Sub-step 1: Change variables via Equiv.prodCongr e e
    have cov : uniformExpect ((Fin q → R) × (Fin q → R)) (fun ⟨h₁, h₂⟩ =>
        ind h₁ * ind (fun i => if i.val < j.val then h₁ i else h₂ i)) =
      uniformExpect (((P → R) × (S → R)) × ((P → R) × (S → R)))
        (fun ⟨⟨p₁, s₁⟩, ⟨_, s₂⟩⟩ => ind (e.symm (p₁, s₁)) * ind (e.symm (p₁, s₂))) := by
      -- Change variables via (Equiv.prodCongr e e).symm
      rw [← uniformExpect_congr (Equiv.prodCongr e e).symm]
      congr 1; ext ⟨⟨p₁, s₁⟩, ⟨p₂, s₂⟩⟩
      simp only [Function.comp_def, Equiv.prodCongr_symm, Equiv.prodCongr_apply,
        Prod.map_fst, Prod.map_snd]
      congr 1
      exact congr_arg ind (merge_eq p₁ s₁ p₂ s₂)
    -- Sub-step 2: Integrate out p₂ + factor s₁,s₂ + collapse to β²
    have factor : uniformExpect (((P → R) × (S → R)) × ((P → R) × (S → R)))
        (fun ⟨⟨p₁, s₁⟩, ⟨_, s₂⟩⟩ => ind (e.symm (p₁, s₁)) * ind (e.symm (p₁, s₂))) =
      uniformExpect (P → R) (fun p => β p ^ 2) := by
      -- Convert to projection form for easier rewriting
      change uniformExpect _ (fun (x : ((P → R) × (S → R)) × ((P → R) × (S → R))) =>
        ind (e.symm (x.1.1, x.1.2)) * ind (e.symm (x.1.1, x.2.2))) = _
      -- Fubini: split ((p₁,s₁),(p₂,s₂)) into outer (p₁,s₁) and inner (p₂,s₂)
      rw [uniformExpect_prod]
      -- Reduce (a,b).1 → a and (a,b).2 → b
      dsimp only []
      -- Factor out ind(e⁻¹(a.1,a.2)) from inner (constant wrt b)
      simp_rw [uniformExpect_smul]
      -- Drop unused b.1: E_{(b₁,b₂)}[ind(e⁻¹(a.1,b₂))] = E_{s₂}[ind(e⁻¹(a.1,s₂))]
      have h_drop : ∀ p₁ : P → R,
        uniformExpect ((P → R) × (S → R)) (fun b =>
          ind (e.symm (p₁, b.2))) = β p₁ := by
        intro p₁
        exact uniformExpect_prod_ignore_fst (fun s₂ => ind (e.symm (p₁, s₂)))
      simp_rw [h_drop]
      -- Now: E_{(p₁,s₁)}[ind(e⁻¹(p₁,s₁)) * β(p₁)] = E_p[β(p)²]
      rw [uniformExpect_prod]; dsimp only []
      -- Commute and factor out β(p) (constant wrt s₁)
      simp_rw [show ∀ (p : P → R) (s : S → R),
        ind (e.symm (p, s)) * β p = β p * ind (e.symm (p, s)) from
        fun _ _ => mul_comm _ _, uniformExpect_smul]
      -- Now E_p[β(p) * β(p)] = E_p[β(p)²]
      congr 1; ext p; ring
    rw [cov, factor]
  -- Step B: Jensen's inequality: E[β²] ≥ (E[β])²
  have jensen := uniformExpect_sq_le (P → R) β
  -- Step C: E[β] = perIndexAcc
  have beta_eq : uniformExpect (P → R) β = perIndexAcc run c j := by
    -- β(p) = E_s[ind(e.symm(p,s))], so E_p[β(p)] = E_{(p,s)}[ind(e.symm(p,s))]
    change uniformExpect (P → R) (fun p =>
      uniformExpect (S → R) (fun s => ind (e.symm (p, s)))) = _
    -- Rewrite inner as composition to help Fubini match
    rw [show (fun p : P → R => uniformExpect (S → R) (fun s => ind (e.symm (p, s)))) =
        (fun p => uniformExpect (S → R) (fun s => (ind ∘ e.symm) (p, s))) from rfl,
      ← uniformExpect_prod,
      uniformExpect_congr e.symm]
    rfl
  -- Combine: LHS = E[β²] ≥ (E[β])² = perIndexAcc²
  calc uniformExpect ((Fin q → R) × (Fin q → R)) (fun ⟨h₁, h₂⟩ =>
        ind h₁ * ind (fun i => if i.val < j.val then h₁ i else h₂ i))
      = uniformExpect (P → R) (fun p => β p ^ 2) := lhs_eq
    _ ≥ (uniformExpect (P → R) β) ^ 2 := jensen
    _ = perIndexAcc run c j ^ 2 := by rw [beta_eq]

/-- Per-index bound: the fork contribution at index `j` is at least
`perIndexAcc(c,j)² - perIndexAcc(c,j)/|R|`. -/
private theorem perIndexFork_ge
    {α : Type} {R : Type} [Fintype R] [Nonempty R] [DecidableEq R] {q : ℕ}
    (run : Coins → (Fin q → R) → Option (Fin q × α)) (c : Coins) (j : Fin q) :
    perIndexFork run c j ≥ perIndexAcc run c j ^ 2 - perIndexAcc run c j / Fintype.card R := by
  -- perIndexFork = E[acc₁ · acc₂ · (1 - col)]
  -- ≥ E[acc₁ · acc₂] - E[acc₁ · col]
  -- ≥ perIndexAcc² - perIndexAcc/|R|
  -- Step 1: Pointwise lower bound
  -- perIndexFork integrand = acc₁ * acc₂ * notcol ≥ acc₁*acc₂ - acc₁*col
  -- because acc₁*acc₂*notcol - (acc₁*acc₂ - acc₁*col) = acc₁*col*(1-acc₂) ≥ 0
  have h_lb : perIndexFork run c j ≥
      uniformExpect ((Fin q → R) × (Fin q → R)) (fun ⟨h₁, h₂⟩ =>
        (match run c h₁ with | none => (0:ℝ) | some (j', _) => if j' = j then 1 else 0) *
        (match run c (fun i => if i.val < j.val then h₁ i else h₂ i) with
          | none => (0:ℝ) | some (j', _) => if j' = j then 1 else 0)) -
      uniformExpect ((Fin q → R) × (Fin q → R)) (fun ⟨h₁, h₂⟩ =>
        (match run c h₁ with | none => (0:ℝ) | some (j', _) => if j' = j then 1 else 0) *
        if h₁ j = h₂ j then 1 else 0) := by
    unfold perIndexFork
    rw [← uniformExpect_sub]
    apply uniformExpect_mono
    intro ⟨h₁, h₂⟩
    -- Case split on the first run
    rcases hrun₁ : run c h₁ with _ | ⟨j₁, a₁⟩
    · -- acc₁ = 0: both sides 0
      simp [hrun₁]
    · by_cases hj₁ : j₁ = j
      · -- j₁ = j: acc₁ = 1
        subst hj₁
        simp only [hrun₁, ite_true, one_mul]
        -- Case split on the second run
        rcases hrun₂ : run c (fun i => if i.val < j₁.val then h₁ i else h₂ i)
          with _ | ⟨j₂, a₂⟩
        · simp; split <;> simp
        · by_cases hj₂ : j₂ = j₁
          · subst hj₂; simp; split <;> simp
          · simp [hj₂]; split <;> simp
      · -- j₁ ≠ j: acc₁ = 0
        simp [hrun₁, hj₁]
  -- Step 2: Apply correlation and collision bounds
  linarith [correlation_bound run c j, collision_bound run c j]

/-- Per-coins fork bound: for fixed coins `c`, the fork probability is at least
`perCoinsAcc(c)²/q - perCoinsAcc(c)/|R|`. -/
private theorem per_coins_fork_ge
    {α : Type} (R : Type) [Fintype R] [Nonempty R] [DecidableEq R] {q : ℕ}
    (run : Coins → (Fin q → R) → Option (Fin q × α)) (c : Coins) (hq : 0 < q) :
    perCoinsFork run c ≥
      perCoinsAcc run c ^ 2 / q - perCoinsAcc run c / Fintype.card R := by
  -- Decompose into per-index contributions
  rw [perCoinsFork_eq_sum]
  -- Each per-index contribution ≥ α_j² - α_j/|R|
  have h_per_index : ∀ j : Fin q,
      perIndexFork run c j ≥
        perIndexAcc run c j ^ 2 - perIndexAcc run c j / Fintype.card R :=
    fun j => perIndexFork_ge run c j
  -- Sum the per-index bounds
  have h_sum_ge : ∑ j : Fin q, perIndexFork run c j ≥
      ∑ j : Fin q, (perIndexAcc run c j ^ 2 - perIndexAcc run c j / Fintype.card R) :=
    Finset.sum_le_sum fun j _ => h_per_index j
  -- Split the sum
  have h_split : ∑ j : Fin q,
      (perIndexAcc run c j ^ 2 - perIndexAcc run c j / Fintype.card R) =
      ∑ j : Fin q, perIndexAcc run c j ^ 2 -
      ∑ j : Fin q, (perIndexAcc run c j / Fintype.card R) :=
    Finset.sum_sub_distrib
      (fun j => perIndexAcc run c j ^ 2)
      (fun j => perIndexAcc run c j / Fintype.card R)
  -- The sum of α_j/|R| = perCoinsAcc/|R|
  have h_sum_div : ∑ j : Fin q, (perIndexAcc run c j / (Fintype.card R : ℝ)) =
      perCoinsAcc run c / Fintype.card R := by
    rw [← Finset.sum_div, ← perCoinsAcc_eq_sum]
  -- Cauchy-Schwarz: ∑ α_j² ≥ (∑ α_j)²/q
  have h_cauchy : ∑ j : Fin q, perIndexAcc run c j ^ 2 ≥
      perCoinsAcc run c ^ 2 / q := by
    rw [perCoinsAcc_eq_sum run c]
    have hq_pos : (0 : ℝ) < q := Nat.cast_pos.mpr hq
    rw [ge_iff_le, div_le_iff₀ hq_pos]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun j : Fin q => perIndexAcc run c j) (fun _ => (1 : ℝ))
    simp only [one_pow, mul_one, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one] at hcs
    linarith
  linarith

/-- **The General Forking Lemma** (Bellare-Neven 2006).

If an algorithm accepts with probability `acc` and outputs a fork index
from `{0, ..., q-1}`, then forking succeeds with probability at least
`acc²/q - acc/|R|`.

The bound comes from:
1. For fixed coins, the probability of accepting at index `j` is `α_j`.
   Forking success for those coins ≥ `∑_j α_j · (α_j - 1/|R|)`.
2. By Cauchy-Schwarz: `∑_j α_j² ≥ (∑_j α_j)²/q`.
3. Average over coins using Jensen (`E[x²] ≥ E[x]²`). -/
theorem forking_lemma
    {α : Type} (Coins R : Type) [Fintype Coins] [Nonempty Coins]
    [Fintype R] [Nonempty R] [DecidableEq R] (q : ℕ)
    (run : Coins → (Fin q → R) → Option (Fin q × α))
    (hq : 0 < q) :
    forkProb Coins R q run ≥
      (forkAcceptProb Coins R q run) ^ 2 / q -
      (forkAcceptProb Coins R q run) / Fintype.card R := by
  -- Step 1: Fubini — rewrite acc as E_c[perCoinsAcc c]
  have acc_eq : forkAcceptProb Coins R q run =
      uniformExpect Coins (fun c => perCoinsAcc run c) := by
    unfold forkAcceptProb perCoinsAcc
    rw [uniformExpect_prod]
  -- Step 2: Fubini — rewrite forkProb as E_c[perCoinsFork c]
  have fork_eq : forkProb Coins R q run =
      uniformExpect Coins (fun c => perCoinsFork run c) := by
    unfold forkProb perCoinsFork
    rw [uniformExpect_prod]
  -- Step 3: Per-coins bound — the heart of the proof
  have per_coins : ∀ c : Coins,
      perCoinsFork run c ≥
        perCoinsAcc run c ^ 2 / q - perCoinsAcc run c / Fintype.card R :=
    fun c => per_coins_fork_ge R run c hq
  -- Step 4: Combine — Fubini + monotonicity + Jensen
  rw [fork_eq, acc_eq]
  calc uniformExpect Coins (fun c => perCoinsFork run c)
      ≥ uniformExpect Coins (fun c =>
          perCoinsAcc run c ^ 2 / q - perCoinsAcc run c / Fintype.card R) :=
        uniformExpect_mono Coins per_coins
    _ = uniformExpect Coins (fun c => perCoinsAcc run c ^ 2 / q) -
        uniformExpect Coins (fun c => perCoinsAcc run c / Fintype.card R) := by
        rw [uniformExpect_sub]
    _ = uniformExpect Coins (fun c => perCoinsAcc run c ^ 2) / q -
        uniformExpect Coins (fun c => perCoinsAcc run c) / Fintype.card R := by
        rw [show (fun c => perCoinsAcc run c ^ 2 / (q : ℝ)) =
              (fun c => (1 / q : ℝ) * perCoinsAcc run c ^ 2) from by ext; ring,
            uniformExpect_smul,
            show (fun c => perCoinsAcc run c / (Fintype.card R : ℝ)) =
              (fun c => (1 / Fintype.card R : ℝ) * perCoinsAcc run c) from by ext; ring,
            uniformExpect_smul]
        ring
    _ ≥ (uniformExpect Coins (fun c => perCoinsAcc run c)) ^ 2 / q -
        uniformExpect Coins (fun c => perCoinsAcc run c) / Fintype.card R := by
        have hj := uniformExpect_sq_le Coins (fun c => perCoinsAcc run c)
        have hq_pos : (0 : ℝ) < q := Nat.cast_pos.mpr hq
        linarith [div_le_div_of_nonneg_right hj (le_of_lt hq_pos)]

end Cslib.Probability

end
