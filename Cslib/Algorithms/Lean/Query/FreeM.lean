/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf, Kim Morrison, Shreyas Srinivas
-/
module

public import Cslib.Foundations.Control.Monad.Free
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Set.Function

/-! # FreeM: query/cost interpreters and lower-bound lemma

This file adds query-complexity interpreters to `FreeM F α`, where the type constructor
`F : Type → Type` represents a query type mapping each query to its response type.

The key operations are:
- `FreeM.eval oracle p`: evaluate `p` by answering each query using `oracle`
- `FreeM.queriesOn oracle p`: count queries along the oracle-determined path
- `FreeM.cost oracle weight p`: weighted query cost

Because the oracle is supplied *after* the program produces its query plan (the `FreeM` tree),
a sound implementation has no way to "guess" what the oracle would respond. This is the
foundation of the anti-cheating guarantee for both upper and lower bounds.

This provides an alternative to the `TimeM`-based cost analysis in
`Cslib.Algorithms.Lean.MergeSort`: here query counting is structural (derived from the
`FreeM` tree) rather than annotation-based.

The combinatorial lower-bound lemma `FreeM.exists_queriesOn_ge_clog` says: if `n` distinct
oracles produce `n` distinct evaluation results from a program whose every response type has
cardinality at most `r`, then some oracle makes at least `⌈log_r n⌉` queries. The proof uses
the adversarial/partition argument: at each query node, the oracles split by their answer,
and the largest fiber still produces distinct results in the corresponding subtree.
-/

public section

namespace Cslib.FreeM

variable {F : Type → Type} {α β : Type}

/-! ## Interpreters

All three interpreters (`eval`, `cost`, `queriesOn`) are defined as `liftM` interpretations
into target monads, routing them through the universal property of the free monad rather
than direct pattern-match on `FreeM`'s constructors:

- `eval` interprets into `Id`.
- `cost` interprets into a `Tally` accumulator monad (a value paired with a `Nat`-valued
  running cost).
- `queriesOn` is `cost` with unit weight.

The constructor-form simp lemmas (`eval_pure`, `eval_liftBind`, `cost_pure`,
`cost_liftBind`, `queriesOn_pure`, `queriesOn_liftBind`) all reduce by `rfl`, giving the
same proof ergonomics as direct pattern-match definitions while honouring the universal
property as the primary abstraction. -/

/-- Internal accumulator monad: a value paired with a `Nat`-valued running cost.
Used to define `cost` and `queriesOn` via `liftM`. -/
structure Tally (α : Type) where
  cost : Nat
  val : α

instance : Monad Tally where
  pure a := ⟨0, a⟩
  bind x f := ⟨x.cost + (f x.val).cost, (f x.val).val⟩

instance : LawfulMonad Tally := LawfulMonad.mk'
  (id_map := fun ⟨n, _⟩ => by
    change Tally.mk (n + 0) _ = Tally.mk n _
    simp)
  (pure_bind := fun a f => by
    change Tally.mk (0 + (f a).cost) (f a).val = f a
    cases f a
    simp)
  (bind_assoc := fun ⟨_, _⟩ _ _ => by
    change Tally.mk _ _ = Tally.mk _ _
    simp [Bind.bind, Nat.add_assoc])

/-- Evaluate a program by answering each query using `oracle`.
Defined as `liftM` to `Id`, the canonical interpreter into pure values. -/
@[expose] def eval (oracle : {ι : Type} → F ι → ι) (p : FreeM F α) : α :=
  p.liftM (m := Id) oracle

/-- Weighted query cost: each query has a cost given by `weight`, accumulated along the
oracle-determined path. Defined as `liftM` into the accumulator monad `Tally`. -/
@[expose] def cost (oracle : {ι : Type} → F ι → ι)
    (weight : {ι : Type} → F ι → Nat) (p : FreeM F α) : Nat :=
  (p.liftM (m := Tally) (fun op => ⟨weight op, oracle op⟩)).cost

/-- Count the number of queries along the path determined by `oracle`. -/
@[expose] def queriesOn (oracle : {ι : Type} → F ι → ι) (p : FreeM F α) : Nat :=
  cost oracle (fun _ => 1) p

-- Simp lemmas for eval

@[simp] theorem eval_pure (oracle : {ι : Type} → F ι → ι) (a : α) :
    eval oracle (.pure a : FreeM F α) = a := rfl

@[simp] theorem eval_liftBind (oracle : {ι : Type} → F ι → ι)
    {ι : Type} (op : F ι) (cont : ι → FreeM F α) :
    eval oracle (.liftBind op cont) = eval oracle (cont (oracle op)) := rfl

@[simp] theorem eval_bind (oracle : {ι : Type} → F ι → ι)
    (t : FreeM F α) (f : α → FreeM F β) :
    eval oracle (t.bind f) = eval oracle (f (eval oracle t)) := by
  induction t with
  | pure a => rfl
  | liftBind op cont ih => exact ih (oracle op)

-- Simp lemmas for cost

@[simp] theorem cost_pure (oracle : {ι : Type} → F ι → ι)
    (weight : {ι : Type} → F ι → Nat) (a : α) :
    cost oracle weight (.pure a : FreeM F α) = 0 := rfl

@[simp] theorem cost_liftBind (oracle : {ι : Type} → F ι → ι)
    (weight : {ι : Type} → F ι → Nat) {ι : Type} (op : F ι) (cont : ι → FreeM F α) :
    cost oracle weight (.liftBind op cont) =
      weight op + cost oracle weight (cont (oracle op)) := rfl

@[simp] theorem cost_bind (oracle : {ι : Type} → F ι → ι)
    (weight : {ι : Type} → F ι → Nat) (t : FreeM F α) (f : α → FreeM F β) :
    cost oracle weight (t.bind f) =
      cost oracle weight t + cost oracle weight (f (eval oracle t)) := by
  induction t with
  | pure a => simp [FreeM.bind]
  | liftBind op cont ih =>
    simp only [FreeM.bind, cost_liftBind, eval_liftBind, ih (oracle op)]
    omega

-- Simp lemmas for queriesOn

@[simp] theorem queriesOn_pure (oracle : {ι : Type} → F ι → ι) (a : α) :
    queriesOn oracle (.pure a : FreeM F α) = 0 := rfl

@[simp] theorem queriesOn_liftBind (oracle : {ι : Type} → F ι → ι)
    {ι : Type} (op : F ι) (cont : ι → FreeM F α) :
    queriesOn oracle (.liftBind op cont) = 1 + queriesOn oracle (cont (oracle op)) := rfl

@[simp] theorem queriesOn_bind (oracle : {ι : Type} → F ι → ι)
    (t : FreeM F α) (f : α → FreeM F β) :
    queriesOn oracle (t.bind f) =
      queriesOn oracle t + queriesOn oracle (f (eval oracle t)) :=
  cost_bind oracle (fun _ => 1) t f

theorem queriesOn_eq_cost_one (oracle : {ι : Type} → F ι → ι) (p : FreeM F α) :
    queriesOn oracle p = cost oracle (fun _ => 1) p := rfl

-- ## Combinatorial lower bound

section LowerBound

/-- Finset-based version: if the oracles indexed by `S` produce `|S|`-many distinct
    evaluation results, then some oracle in `S` makes at least `⌈log_r |S|⌉` queries. -/
private theorem exists_mem_queriesOn_ge_clog (r : Nat)
    (h_fin : ∀ {ρ : Type}, F ρ → Fintype ρ)
    (h_card : ∀ {ρ : Type} (op : F ρ), @Fintype.card ρ (h_fin op) ≤ r)
    {ix : Type} (p : FreeM F α) (S : Finset ix) (hS : S.Nonempty)
    (oracles : ix → ({ρ : Type} → F ρ → ρ))
    (h_inj : Set.InjOn (fun i => p.eval (oracles i)) ↑S) :
    ∃ i ∈ S, p.queriesOn (oracles i) ≥ Nat.clog r S.card := by
  classical
  induction p generalizing ix S with
  | pure a =>
    obtain ⟨i, hi⟩ := hS
    refine ⟨i, hi, ?_⟩
    have hS1 : S.card ≤ 1 :=
      Finset.card_le_one.mpr fun _ ha _ hb => h_inj ha hb rfl
    simp [queriesOn, Nat.clog_of_right_le_one hS1]
  | @liftBind ρ op cont ih =>
    by_cases hle : S.card ≤ 1
    · obtain ⟨i, hi⟩ := hS
      exact ⟨i, hi, by simp [Nat.clog_of_right_le_one hle]⟩
    push Not at hle
    by_cases hr : r ≤ 1
    · obtain ⟨i, hi⟩ := hS
      exact ⟨i, hi, by simp [Nat.clog_of_left_le_one hr]⟩
    push Not at hr
    -- 2 ≤ r, 2 ≤ S.card
    letI : Fintype ρ := h_fin op
    have hk : Fintype.card ρ ≤ r := h_card op
    -- Fintype.card ρ ≥ 1: any oracle produces an answer
    obtain ⟨i₀, _hi₀⟩ := hS
    have : Nonempty ρ := ⟨oracles i₀ op⟩
    have hk1 : 1 ≤ Fintype.card ρ := Fintype.card_pos
    -- Pigeonhole: pick fiber of maximum size
    have ⟨b, _, hb⟩ : ∃ b ∈ (Finset.univ : Finset ρ),
        (S.card - 1) / Fintype.card ρ <
          (S.filter (fun i => oracles i op = b)).card := by
      apply Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
        (fun a _ => Finset.mem_univ (oracles a op))
      simp only [Finset.card_univ]
      calc Fintype.card ρ * ((S.card - 1) / Fintype.card ρ)
          = (S.card - 1) / Fintype.card ρ * Fintype.card ρ := Nat.mul_comm ..
        _ ≤ S.card - 1 := Nat.div_mul_le_self _ _
        _ < S.card := by omega
    set S' := S.filter (fun i => oracles i op = b)
    have hS' : S'.Nonempty :=
      Finset.card_pos.mp (Nat.lt_of_le_of_lt (Nat.zero_le _) hb)
    have h_inj' : Set.InjOn (fun i => (cont b).eval (oracles i)) ↑S' := by
      intro i hi j hj heq
      have him := Finset.mem_coe.mp hi |> Finset.mem_filter.mp
      have hjm := Finset.mem_coe.mp hj |> Finset.mem_filter.mp
      exact h_inj (Finset.mem_coe.mpr him.1) (Finset.mem_coe.mpr hjm.1)
        (by simp [him.2, hjm.2, heq])
    obtain ⟨i, hi, hiq⟩ := ih b S' hS' oracles h_inj'
    have him := Finset.mem_filter.mp hi
    refine ⟨i, him.1, ?_⟩
    simp only [queriesOn_liftBind, him.2]
    -- Need: Nat.clog r S.card ≤ 1 + (cont b).queriesOn (oracles i)
    have hS'_lb : (S.card + r - 1) / r ≤ S'.card := by
      have h1 : (S.card - 1) / r ≤ (S.card - 1) / Fintype.card ρ :=
        Nat.div_le_div_left hk (by omega)
      have h2 : (S.card + r - 1) / r = (S.card - 1) / r + 1 := by
        rw [show S.card + r - 1 = S.card - 1 + r from by omega]
        exact Nat.add_div_right (S.card - 1) (by omega)
      omega
    calc Nat.clog r S.card
        = 1 + Nat.clog r ((S.card + r - 1) / r) := by
          rw [Nat.clog_of_two_le hr (by omega)]; omega
      _ ≤ 1 + Nat.clog r S'.card :=
          Nat.add_le_add_left (Nat.clog_mono_right r hS'_lb) 1
      _ ≤ 1 + (cont b).queriesOn (oracles i) := Nat.add_le_add_left hiq 1

/-- If `n` oracles produce `n` distinct evaluation results from a `FreeM F α` program
whose every response type is finite of cardinality at most `r`, then some oracle makes
at least `⌈log_r n⌉` queries.

This is the core combinatorial lemma for query complexity lower bounds. The proof uses
the adversarial/partition argument: at each query node, the `n` oracles split by their
answer; the largest group (size ≥ ⌈n/r⌉) still produces distinct results in the
corresponding subtree, and the induction proceeds there. -/
theorem exists_queriesOn_ge_clog (r : Nat)
    (h_fin : ∀ {ρ : Type}, F ρ → Fintype ρ)
    (h_card : ∀ {ρ : Type} (op : F ρ), @Fintype.card ρ (h_fin op) ≤ r)
    (p : FreeM F α) {n : Nat}
    (oracles : Fin n → ({ρ : Type} → F ρ → ρ))
    (hn : 0 < n)
    (h_inj : Function.Injective (fun i => p.eval (oracles i))) :
    ∃ i : Fin n, p.queriesOn (oracles i) ≥ Nat.clog r n := by
  have ⟨i, _, hi⟩ := exists_mem_queriesOn_ge_clog r h_fin h_card p Finset.univ
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) oracles h_inj.injOn
  rw [Finset.card_univ, Fintype.card_fin] at hi
  exact ⟨i, hi⟩

end LowerBound

end Cslib.FreeM

end -- public section
