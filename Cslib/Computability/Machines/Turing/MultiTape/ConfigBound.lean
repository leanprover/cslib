/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Option
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# Bounds on the number of reachable configurations in bounded space

For a deterministic multi-tape Turing machine that uses at most `s` cells of work-tape space, the
number of distinct configurations it can be in is at most exponential in `s`.

The configuration type `Cfg` is split into the input head position and the *storage* part
(`Storage`), i.e. the state, the work tape contents and head positions. This split can be used
to show the collapse of small space-bounded classes.


## Important Definitions

The key lemmas in this file are:

* `MultiTapeTM.card_storages_le` bounds the number of *storage configurations* only, disregarding
  the input head position. The function used for the bound is `storageBound Symbol State k s`.
* `MultiTapeTM.card_configs_le` additionally tracks the input head position, giving the bound
  `(n + 2) * storageBound Symbol State k s` on the number of full configurations of an input of
  length `n`.
* `MultiTapeTM.card_configs_le_pow` restates the previous bound as `(n + 2) * a * 2 ^ (c * s)`
  for constants `a` and `c` depending only on the machine, so it can be used to time-bound
  space-bounded machines.

## Design

Starting from the all-blank tapes with every head at `0` and moving by at most one cell per step,
a computation in which tape `i` has visited at most `sᵢ` cells keeps that tape's head position and
every non-blank cell within the per-tape window `[-sᵢ, sᵢ]`.

Hence a storage configuration is determined by finite data over these windows, and counting it
gives the per-tape product `∏ᵢ (2 sᵢ + 1) · (|Symbol| + 1)^(2 sᵢ + 1)`. Since the tapes share the
total space budget (`∑ᵢ sᵢ ≤ s`), this collapses to an expression with the *total* space
(`2s + k`) as the alphabet exponent. The full-configuration bound needed for time-bounding
space-bounded machines then follows by pairing the storage count with the `(n + 2)` possible
input-head positions.

We lose a factor of `2 * k` by simplifying the windows to `[-sᵢ, sᵢ]` instead of the actually used
area, but this is absorbed by the `O(s)` exponent in the final bound. The `+ 2` in `(n + 2)` is
needed because the input head is allowed to move one step off the input in either direction by
the model.
-/

@[expose] public section

open Cslib

namespace Turing.MultiTapeTM

variable {k : ℕ}
variable {State Symbol : Type*}
variable {input : List Symbol}
variable {tm : MultiTapeTM k Symbol State}

/-- The state and work-tape data of a machine, with the cells and head position of tape `i` indexed
by an arbitrary type `ι i`. If you add the input tape position and use `ι i = ℤ`, this is equivalent
to `Cfg` (cf. `Cfg.storage`).
The index set is useful for cardinality arguments if we have a bound on the tape cells that
are actually used.
The input head position is not included because this is useful for arguments below logarithmic
space. -/
@[ext]
structure Storage (Symbol State : Type*) {k : ℕ} (ι : Fin k → Type*) where
  /-- the state of the TM (cf. `Cfg.state`) -/
  state : Option State
  /-- the contents of work tape `i` (cf. `Cfg.workTapes`) -/
  workTapes (i : Fin k) : ι i → Option Symbol
  /-- the position of the head on work tape `i` (cf. `Cfg.workTapePos`) -/
  workTapePos (i : Fin k) : ι i

/-- A `Storage` is just a product of its fields; this equivalence is used for counting. -/
def Storage.equivProd (Symbol State : Type*) (ι : Fin k → Type*) :
    Storage Symbol State ι ≃
      Option State × ((i : Fin k) → ι i → Option Symbol) × ((i : Fin k) → ι i) where
  toFun x := (x.state, x.workTapes, x.workTapePos)
  invFun := fun ⟨state, workTapes, workTapePos⟩ => ⟨state, workTapes, workTapePos⟩

instance (Symbol State : Type*) [Fintype Symbol] [Fintype State]
    (ι : Fin k → Type*) [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)] :
    Fintype (Storage Symbol State ι) :=
  Fintype.ofEquiv _ (Storage.equivProd Symbol State ι).symm

/-- A `Storage` over the unrestricted index type `ℤ` for every tape, as extracted from a full
configuration by `Cfg.storage`. -/
abbrev UnboundedStorage (Symbol State : Type*) (k : ℕ) :=
  Storage Symbol State (fun _ : Fin k => ℤ)

/-- This function maps a `Cfg` to `Storage`, using `ℤ` as the index type for the tapes. -/
def Cfg.storage (c : Cfg k Symbol State input) : UnboundedStorage Symbol State k :=
  ⟨c.state, c.workTapes, c.workTapePos⟩

/-- For a fixed input, a configuration is fully determined by its input-head position together with
its `storage`. Hence counting distinct configurations reduces to counting `(inputPos, storage)`
pairs. -/
lemma inputPos_storage_injective (input : List Symbol) :
    Function.Injective (fun c : Cfg k Symbol State input => (c.inputPos.val, c.storage)) := by
  intro c₁ c₂ h
  simp only [Cfg.storage, Prod.mk.injEq, Storage.mk.injEq] at h
  obtain ⟨hip, hstate, hwt, hwp⟩ := h
  exact Cfg.ext hstate (Fin.ext hip) hwt hwp

/-- The window `[-s, s]` of tape positions allotted to a tape that uses `s` cells. -/
def Storage.window (s : ℕ) : Finset ℤ := Finset.Icc (-(s : ℤ)) s

@[scoped grind =]
lemma Storage.mem_window {s : ℕ} {z : ℤ} : z ∈ Storage.window s ↔ z.natAbs ≤ s := by
  grind [Storage.window]

@[simp]
lemma Storage.card_window (s : ℕ) : (Storage.window s).card = 2 * s + 1 := by
  grind [Storage.window, Int.card_Icc]

/-- A bounded storage configuration: a `Storage` whose tape `i` is restricted to the finite window
`[-(w i), w i]`. Storage configurations of a computation that visits at most the window of each
tape embed injectively into this finite type (`Storage.toBounded`), so its cardinality bounds the
number of reachable storage configurations. -/
abbrev BoundedStorage (Symbol State : Type*) {k : ℕ} (w : Fin k → ℕ) :=
  Storage Symbol State (fun i => Storage.window (w i))

/-- A storage fits in the per-tape windows `w`: on each tape `j`, the head position and every
non-blank cell have absolute value `≤ w j`. -/
structure Storage.FitsIn (x : UnboundedStorage Symbol State k) (w : Fin k → ℕ) : Prop where
  /-- the head position on every tape lies within its window -/
  pos_le : ∀ j, (x.workTapePos j).natAbs ≤ w j
  /-- every non-blank cell on every tape lies within its window -/
  cell_le : ∀ j z, x.workTapes j z ≠ none → z.natAbs ≤ w j

/-- If an `UnboundedStorage` fits in a smaller window, it also fits in the larger window. -/
lemma Storage.FitsIn_mono {x : UnboundedStorage Symbol State k} : Monotone x.FitsIn := by
  intro w₁ w₂ h_le h_fits
  refine ⟨?_, ?_⟩
  · intro j
    grind [h_fits.pos_le j, h_le j]
  · intro j z h_ne
    grind [h_fits.cell_le j z h_ne, h_le j]

/-- Restriction of a storage over `ℤ` to the finite windows `w` (with heads outside their window
clamped to `0`). -/
def Storage.toBounded (x : UnboundedStorage Symbol State k) (w : Fin k → ℕ) :
    BoundedStorage Symbol State w where
  state := x.state
  workTapes j z := x.workTapes j z.1
  workTapePos j :=
    if h : x.workTapePos j ∈ Storage.window (w j) then ⟨x.workTapePos j, h⟩
    else ⟨0, Storage.mem_window.mpr (Nat.zero_le _)⟩

/-- The restriction is injective on storages that fit in the windows. -/
lemma Storage.toBounded_injOn (w : Fin k → ℕ) :
    Set.InjOn (Storage.toBounded (Symbol := Symbol) (State := State) · w) {x | x.FitsIn w} := by
  rintro x ⟨hxp, hxc⟩ y ⟨hyp, hyc⟩ hxy
  simp only [Storage.toBounded, Storage.mk.injEq] at hxy
  obtain ⟨hstate, htapes, hpos⟩ := hxy
  refine Storage.ext hstate (funext₂ fun j z => ?_) (funext fun j => ?_)
  · by_cases hz : z ∈ Storage.window (w j)
    · exact congrFun (congrFun htapes j) ⟨z, hz⟩
    · grind
  · have := congrFun hpos j
    grind [Subtype.ext_iff]

/-- The number of storages over finite position types is the per-tape product of
"cell contents × head position" counts. -/
lemma card_storage [Fintype Symbol] [Fintype State]
    (ι : Fin k → Type*) [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)] :
    Fintype.card (Storage Symbol State ι)
      = (Fintype.card State + 1)
        * ∏ i, Fintype.card (ι i) * (Fintype.card Symbol + 1) ^ Fintype.card (ι i) := by
  rw [Fintype.card_congr (Storage.equivProd Symbol State ι)]
  simp only [Fintype.card_prod, Fintype.card_option, Fintype.card_pi, Finset.prod_const,
    Finset.card_univ, Finset.prod_mul_distrib]
  ring

/-- An upper bound on the number of storage configurations a `k`-tape machine can be in while using
at most `s` cells of total work-tape space, over the given alphabet and state set. The `(2s + 1)^k`
factor counts the possible head positions; the dominant factor `(|Symbol| + 1)^(2s + k)` uses the
*total* space `s` in the exponent (the `k` tapes share the space budget), matching the textbook
`|State| · |Symbol|^{O(s)} · poly(s)` count. -/
def storageBound (Symbol State : Type*) [Fintype Symbol] [Fintype State] (k s : ℕ) : ℕ :=
  (Fintype.card State + 1) * ((2 * s + 1) ^ k * (Fintype.card Symbol + 1) ^ (2 * s + k))

/-- `storageBound` grows at most exponentially in the space `s`: there exist constants `a` and `c`
(depending on the machine's alphabet, state set and tape count) with
`storageBound Symbol State k s ≤ a * 2 ^ (c * s)` for all `s`. -/
lemma storageBound_le_pow [Fintype Symbol] [Fintype State] :
    ∃ a c : ℕ, ∀ s : ℕ, storageBound Symbol State k s ≤ a * 2 ^ (c * s) := by
  set syms := Fintype.card Symbol + 1 with hB
  set states := Fintype.card State + 1 with hQ
  -- The strategy is to bound each factor of `storageBound` by a power of `2`, using `B ≤ 2 ^ B`
  -- and `2 * s + 1 ≤ 2 ^ (s + 1)`. Collecting the exponents then yields
  -- `(s + 1) * k + B * (2 * s + k)`, which splits into the constant part `B * k + k`
  -- (absorbed into `a`) and the part `(2 * B + k) * s` linear in `s` (which is `c * s`).
  refine ⟨states * 2 ^ (syms * k + k), 2 * syms + k, fun s => ?_⟩
  have hB2 : syms ≤ 2 ^ syms := Nat.lt_two_pow_self.le
  have h2s1 : 2 * s + 1 ≤ 2 ^ (s + 1) := by grind [pow_succ, Nat.lt_two_pow_self]
  calc storageBound Symbol State k s
      = states * ((2 * s + 1) ^ k * syms ^ (2 * s + k)) := rfl
    _ ≤ states * ((2 ^ (s + 1)) ^ k * (2 ^ syms) ^ (2 * s + k)) := by
        gcongr <;> exact Nat.zero_le _
    _ = states * 2 ^ ((s + 1) * k + syms * (2 * s + k)) := by rw [← pow_mul, ← pow_mul, ← pow_add]
    _ = states * 2 ^ ((syms * k + k) + (2 * syms + k) * s) := by ring_nf
    _ = states * 2 ^ (syms * k + k) * 2 ^ ((2 * syms + k) * s) := by rw [pow_add, mul_assoc]

/-- The per-tape product is bounded by `storageBound`: each tape uses at most the total space `s`,
and the tapes together use at most `s`, which collapses the alphabet exponent to `2s + k`. -/
lemma card_boundedStorage_le [Fintype Symbol] [Fintype State]
    (w : Fin k → ℕ) (s : ℕ) (hsum : ∑ i, w i ≤ s) :
    Fintype.card (BoundedStorage Symbol State w) ≤ storageBound Symbol State k s := by
  have hle : ∀ i, w i ≤ s := fun i =>
    (Finset.single_le_sum (fun i _ => Nat.zero_le (w i)) (Finset.mem_univ i)).trans hsum
  simp only [card_storage, storageBound, Fintype.card_coe, Storage.card_window]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hsc : ∑ i : Fin k, (2 * w i + 1) = 2 * (∑ i, w i) + k := by
    simp [two_mul, Finset.sum_add_distrib]
  gcongr
  · simpa using Finset.prod_le_pow_card Finset.univ (fun i => 2 * w i + 1) (2 * s + 1)
      fun i _ => by have := hle i; omega
  · omega
  · omega

/-- The storage of any configuration reached within `T` steps fits in the windows given by the
per-tape space usage up to step `T`. -/
lemma storage_fitsIn
    (T : ℕ)
    {t : ℕ}
    (ht : t ≤ T) :
    (tm.configs (tm.initCfg input) t).storage.FitsIn (tm.spaceUsedByTape (tm.initCfg input) T) := by
  -- The bounds at step `t` extend to the window at step `T ≥ t` by monotonicity of space usage.
  apply Storage.FitsIn_mono (fun j => tm.spaceUsedByTape_mono _ j ht)
  refine ⟨?_, ?_⟩
  · intro j
    simpa [Cfg.storage] using tm.natAbs_le_spaceUsedByTape_of_mem_visited
      (tm.mem_visitedByTapeHead_self (tm.initCfg input) t j)
  · intro j
    exact content_natAbs_le_spaceUsedByTape t


open scoped Classical in
/-- For any multi-tape Turing machine that uses at most space `s` up to step `t`, the number
of storage configurations (configurations disregarding the input head positions) up to step `t`
is at most `storageBound Symbol State k s` (independent of `t`). -/
theorem card_storages_le
    [Fintype Symbol] [Fintype State]
    (t s : ℕ)
    (hs : tm.spaceUsed (tm.initCfg input) t ≤ s) :
    ((Finset.range (t + 1)).image (fun t' => (tm.configs (tm.initCfg input) t').storage)).card
    ≤ storageBound Symbol State k s := by
  set space := tm.spaceUsedByTape (tm.initCfg input) t
  calc ((Finset.range (t + 1)).image
          (fun t' => (tm.configs (tm.initCfg input) t').storage)).card
      ≤ Fintype.card (BoundedStorage Symbol State space) := by
        rw [← Finset.card_univ]
        refine Finset.card_le_card_of_injOn (Storage.toBounded · space) (by simp) ?_
        refine Set.InjOn.mono ?_ (Storage.toBounded_injOn space)
        intro x hx
        simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_range] at hx
        obtain ⟨t', ht, rfl⟩ := hx
        exact storage_fitsIn t (by omega)
    _ ≤ storageBound Symbol State k s := card_boundedStorage_le space s hs


open scoped Classical in
/-- The number of distinct configurations a multi-tape Turing machine with space bound `s`
can reach is at most `(n + 2) * storageBound Symbol State k s`, where `n` is the input length.
The `(n + 2)` factor accounts for the input-head position; the `storageBound` factor accounts for
everything else (`storage`). -/
theorem card_configs_le
    [Fintype Symbol] [Fintype State]
    (t s : ℕ)
    (hs : tm.spaceUsed (tm.initCfg input) t ≤ s) :
    ((Finset.range (t + 1)).image (tm.configs (tm.initCfg input))).card
      ≤ (input.length + 2) * storageBound Symbol State k s := by
  -- Counting configurations reduces to counting `(inputPos, storage)` pairs, since the map to such
  -- pairs is injective for a fixed input.
  rw [← Finset.card_image_of_injective _ (inputPos_storage_injective input), Finset.image_image]
  -- The pair image lies in the product of the input-head range with the storage image, so its
  -- cardinality is bounded by `(n + 2)` times the storage count from `card_storages_le`.
  calc ((Finset.range (t + 1)).image (fun t' =>
          ((tm.configs (tm.initCfg input) t').inputPos.val,
           (tm.configs (tm.initCfg input) t').storage))).card
      ≤ (Finset.range (input.length + 2) ×ˢ (Finset.range (t + 1)).image
          (fun t' => (tm.configs (tm.initCfg input) t').storage)).card := by
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_image, Finset.mem_range] at hx
        obtain ⟨t, ht, rfl⟩ := hx
        simp only [Finset.mem_product, Finset.mem_range, Finset.mem_image]
        exact ⟨(tm.configs (tm.initCfg input) t).inputPos.isLt, t, ht, rfl⟩
    _ = (input.length + 2) * ((Finset.range (t + 1)).image
          (fun t => (tm.configs (tm.initCfg input) t).storage)).card := by
        rw [Finset.card_product, Finset.card_range]
    _ ≤ (input.length + 2) * storageBound Symbol State k s :=
        Nat.mul_le_mul_left _ (card_storages_le t s hs)

open scoped Classical in
/-- The number of distinct configurations reachable in space `s` is at most `2 ^ (O(s))`, up to the
`(n + 2)` factor for the input-head position: there are constants `a` and `c` (depending only on
the machine's alphabet, state set and tape count) that bound the configuration count for *every*
input and step count. This is the form used to time-bound space-bounded machines. -/
theorem card_configs_le_pow
    [Finite Symbol] [Finite State] :
    ∃ a c : ℕ, ∀ (input : List Symbol) (t s : ℕ),
      tm.spaceUsed (tm.initCfg input) t ≤ s →
      ((Finset.range (t + 1)).image (tm.configs (tm.initCfg input))).card
        ≤ (input.length + 2) * a * 2 ^ (c * s) := by
  have : Fintype Symbol := Fintype.ofFinite Symbol
  have : Fintype State := Fintype.ofFinite State
  obtain ⟨a, c, hpow⟩ := storageBound_le_pow (Symbol := Symbol) (State := State)
  refine ⟨a, c, fun input t s hs => ?_⟩
  calc ((Finset.range (t + 1)).image (tm.configs (tm.initCfg input))).card
      ≤ (input.length + 2) * storageBound Symbol State k s :=
        tm.card_configs_le t s hs
    _ ≤ (input.length + 2) * (a * 2 ^ (c * s)) := Nat.mul_le_mul_left _ (hpow s)
    _ = (input.length + 2) * a * 2 ^ (c * s) := by ring

end Turing.MultiTapeTM
