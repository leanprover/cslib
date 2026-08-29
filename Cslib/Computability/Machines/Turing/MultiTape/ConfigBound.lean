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
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Tactic.Ring

/-!
# Bounds on the number of reachable configurations in bounded space

A multi-tape Turing machine that uses at most `s` cells of work-tape space can only reach a number
of configurations that differ in their storage content (state and work tapes) that is bounded
exponentially in `s`. Together with the `n + 2` possible positions of the input head this bounds
the number of configurations the machine can be in, disregarding the write-only output tape.

## Important Definitions

The results are layered, from the purely combinatorial to the machine-specific:

* `MultiTapeTM.encard_fitsIn_le` is a counting statement about the type `Storage` alone and does
  not mention Turing machines: a memory whose non-blank cells and heads stay within per-tape
  windows of total size `s` can hold at most `storageBound Symbol State k s` different values.
* `MultiTapeTM.storage_fitsIn` is the geometric input: the storage reached after `t` steps stays
  within the windows given by the space used up to step `t`.
* `MultiTapeTM.encard_storages_le` combines the two: a machine bounded by space `s` passes through
  at most `storageBound Symbol State k s` storages *during its whole run*, no matter how long it
  runs and how long its input is. This is the form needed for arguments below logarithmic space,
  where the number of storages is much smaller than the number of input head positions.
* `MultiTapeTM.encard_cores_le` adds the input head position, giving the bound
  `(n + 2) * storageBound Symbol State k s` on the number of reachable *cores* (`Cfg.core`,
  a configuration without its output tape) for an input of length `n`.
* `MultiTapeTM.storageBound_le_base_mul_pow` restates `storageBound Symbol State k s` as
  `storageBoundBase Symbol State k * 2 ^ (storageBoundExp Symbol k * s)`, so that the bounds can
  be used to time-bound space-bounded machines.

## Design

The write-only output tape is never read by `step`, so it can be dropped: what a machine can still
react to is its `Cfg.core`, the pair of the input head position and the `Storage`. The input head
position, in contrast, *is* read, so it cannot be dropped and has to be counted, which is where
the factor `n + 2` comes from (the input head may move one step off the input in either direction).

Starting from the all-blank tapes with every head at `0` and moving by at most one cell per step,
a computation in which tape `i` has visited at most `sᵢ` cells keeps that tape's head position and
every non-blank cell within the per-tape window `[-sᵢ, sᵢ]`.

Hence a storage is determined by finite data over these windows, and counting it gives the
per-tape product `∏ᵢ (2 sᵢ + 1) · (|Symbol| + 1)^(2 sᵢ + 1)`. Since the tapes share the total space
budget (`∑ᵢ sᵢ ≤ s`), this collapses to an expression with the *total* space (`2s + k`) as the
alphabet exponent.

We lose a factor of `2 * k` by simplifying the windows to `[-sᵢ, sᵢ]` instead of the actually used
area, but this is absorbed by the `O(s)` exponent in the final bound.

The windows for a whole run are available because a machine that is space-bounded at every point in
time attains its per-tape space usage at a single step (`MultiTapeTM.exists_spaceUsedByTape_max`).
-/

@[expose] public section

open Cslib

namespace Turing.MultiTapeTM

variable {k : ℕ}
variable {State Symbol : Type*}
variable {input : List Symbol}
variable {tm : MultiTapeTM k Symbol State}

/-!
## Storage

Defines the core data structure for this file, `Storage`, which contains the state and the work
tapes of a multi-tape Turing machine, where the work tape cells are indexed over a generic index
type.

Then `UnboundedStorage` uses `ℤ` as index type and thus is equivalent to a projection of `Cfg`.

Finally, `BoundedStorage` is introduced which uses `[-s, s]` as index type (with different `s`
for each tape) and it is proven that there is an injective mapping from `UnboundedStorage`
to `BoundedStorage` if the non-blank cells and head positions of the `UnboundedStorage` all lie
inside the `[-s, s]` windows for all tapes.
-/

/-- The state and work-tape data of a machine, with the cells and head position of tape `i` indexed
by an arbitrary type `ι i`. -/
@[ext]
structure Storage (Symbol State : Type*) {k : ℕ} (ι : Fin k → Type*) where
  /-- the state of the TM (cf. `Cfg.state`) -/
  state : Option State
  /-- the contents of work tape `i` (cf. `Cfg.workTapes`) -/
  workTapes (i : Fin k) : ι i → Option Symbol
  /-- the position of the head on work tape `i` (cf. `Cfg.workTapePos`) -/
  workTapePos (i : Fin k) : ι i

/-- A `Storage` is just a product of its fields. -/
def Storage.equivProd (Symbol State : Type*) (ι : Fin k → Type*) :
    Storage Symbol State ι ≃
      Option State × ((i : Fin k) → ι i → Option Symbol) × ((i : Fin k) → ι i) where
  toFun x := (x.state, x.workTapes, x.workTapePos)
  invFun := fun ⟨state, workTapes, workTapePos⟩ => ⟨state, workTapes, workTapePos⟩

instance (Symbol State : Type*) [Fintype Symbol] [Fintype State]
    (ι : Fin k → Type*) [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)] :
    Fintype (Storage Symbol State ι) :=
  Fintype.ofEquiv _ (Storage.equivProd Symbol State ι).symm

/-- A `Storage` using the tape index type `ℤ`. -/
abbrev UnboundedStorage (Symbol State : Type*) (k : ℕ) := Storage Symbol State (fun _ : Fin k => ℤ)

/-- The window `[-s, s]` of tape positions allotted to a tape that uses `s` cells. -/
@[scoped grind =]
def window (s : ℕ) : Finset ℤ := Finset.Icc (-(s : ℤ)) s

@[scoped grind =]
lemma Storage.mem_window {s : ℕ} {z : ℤ} : z ∈ window s ↔ z.natAbs ≤ s := by
  grind

@[simp]
lemma Storage.card_window (s : ℕ) : (window s).card = 2 * s + 1 := by
  grind [Int.card_Icc]

/-- A bounded storage: a `Storage` whose tape `i` is restricted to the finite window
`[-(w i), w i]`. -/
abbrev BoundedStorage (Symbol State : Type*) {k : ℕ} (w : Fin k → ℕ) :=
  Storage Symbol State (fun i => window (w i))

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
    if h : x.workTapePos j ∈ window (w j) then ⟨x.workTapePos j, h⟩
    else ⟨0, Storage.mem_window.mpr (Nat.zero_le _)⟩

/-- The restriction is injective on storages that fit in the windows. -/
lemma Storage.toBounded_injOn (w : Fin k → ℕ) :
    Set.InjOn (Storage.toBounded (Symbol := Symbol) (State := State) · w) {x | x.FitsIn w} := by
  rintro x ⟨hxp, hxc⟩ y ⟨hyp, hyc⟩ hxy
  simp only [Storage.toBounded, Storage.mk.injEq] at hxy
  obtain ⟨hstate, htapes, hpos⟩ := hxy
  refine Storage.ext hstate (funext₂ fun j z => ?_) (funext fun j => ?_)
  · by_cases hz : z ∈ window (w j)
    · exact congrFun (congrFun htapes j) ⟨z, hz⟩
    · grind
  · grind [congrFun hpos j]

/-! ## Counting storages

This section is purely combinatorial: it counts how many values a `Storage` restricted to given
windows can take, without reference to a machine or a run.
-/

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

/-- An upper bound on the number of storages a `k`-tape machine can be in while using
at most `s` cells of total work-tape space, over the given alphabet and state set. The `(2s + 1)^k`
factor counts the possible head positions; the dominant factor `(|Symbol| + 1)^(2s + k)` uses the
*total* space `s` in the exponent (the `k` tapes share the space budget). -/
def storageBound (Symbol State : Type*) [Fintype Symbol] [Fintype State] (k s : ℕ) : ℕ :=
  (Fintype.card State + 1) * ((2 * s + 1) ^ k * (Fintype.card Symbol + 1) ^ (2 * s + k))

/-- The per-tape product is bounded by `storageBound`: each tape uses at most the total space `s`,
and the tapes together use at most `s`, which collapses the alphabet exponent to `2s + k`. -/
lemma card_boundedStorage_le [Fintype Symbol] [Fintype State]
    {w : Fin k → ℕ} {s : ℕ} (hsum : ∑ i, w i ≤ s) :
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

/-- The counting result at the heart of this file: a `Storage` whose non-blank cells and head
positions stay within per-tape windows of total size at most `s` can take at most
`storageBound Symbol State k s` different values. -/
theorem encard_fitsIn_le [Fintype Symbol] [Fintype State]
    {w : Fin k → ℕ} {s : ℕ} (hsum : ∑ i, w i ≤ s) :
    {x : UnboundedStorage Symbol State k | x.FitsIn w}.encard
      ≤ storageBound Symbol State k s := by
  calc {x : UnboundedStorage Symbol State k | x.FitsIn w}.encard
      = ((Storage.toBounded · w) '' {x | x.FitsIn w}).encard :=
        ((Storage.toBounded_injOn w).encard_image).symm
    _ ≤ (Set.univ : Set (BoundedStorage Symbol State w)).encard :=
        Set.encard_le_encard (Set.subset_univ _)
    _ = Fintype.card (BoundedStorage Symbol State w) := by
        simp [Set.encard_univ, ENat.card_eq_coe_fintype_card]
    _ ≤ storageBound Symbol State k s := by
        exact_mod_cast card_boundedStorage_le hsum

/-! ### The exponential form of `storageBound`

This proves that `storageBound` is exponential in the space `s`.
 -/

/-- The base factor in the resulting exponential form of `storageBound`. -/
def storageBoundBase (Symbol State : Type*) [Fintype Symbol] [Fintype State] (k : ℕ) : ℕ :=
  (Fintype.card State + 1) * 2 ^ ((Fintype.card Symbol + 1) * k + k)

/-- The factor in the exponent of the exponential form of `storageBound`. -/
def storageBoundExp (Symbol : Type*) [Fintype Symbol] (k : ℕ) : ℕ :=
  2 * (Fintype.card Symbol + 1) + k

/-- `storageBound` grows at most exponentially in the space `s`, with a constant factor and a
factor in the exponent that only depend on the machine's alphabet, state set and tape count. -/
lemma storageBound_le_base_mul_pow [Fintype Symbol] [Fintype State] (s : ℕ) :
    storageBound Symbol State k s
      ≤ storageBoundBase Symbol State k * 2 ^ (storageBoundExp Symbol k * s) := by
  set syms := Fintype.card Symbol + 1 with hB
  set states := Fintype.card State + 1 with hQ
  -- The strategy is to bound each factor of `storageBound` by a power of `2`, using
  -- `syms ≤ 2 ^ syms` and `2 * s + 1 ≤ 2 ^ (s + 1)`. Collecting the exponents then yields
  -- `(s + 1) * k + syms * (2 * s + k)`, which splits into the constant part `syms * k + k`
  -- (which is in `storageBoundBase`) and the part `(2 * syms + k) * s` linear in `s`.
  have hB2 : syms ≤ 2 ^ syms := Nat.lt_two_pow_self.le
  have h2s1 : 2 * s + 1 ≤ 2 ^ (s + 1) := by grind [pow_succ, Nat.lt_two_pow_self]
  calc storageBound Symbol State k s
      = states * ((2 * s + 1) ^ k * syms ^ (2 * s + k)) := rfl
    _ ≤ states * ((2 ^ (s + 1)) ^ k * (2 ^ syms) ^ (2 * s + k)) := by
        gcongr <;> exact Nat.zero_le _
    _ = states * 2 ^ ((s + 1) * k + syms * (2 * s + k)) := by ring
    _ = states * 2 ^ ((syms * k + k) + (2 * syms + k) * s) := by ring_nf
    _ = states * 2 ^ (syms * k + k) * 2 ^ ((2 * syms + k) * s) := by ring

/-- `storageBound` grows at most exponentially in the space `s`: there exist constants `a` and `c`
(depending on the machine's alphabet, state set and tape count) with
`storageBound Symbol State k s ≤ a * 2 ^ (c * s)` for all `s`. -/
lemma storageBound_le_pow [Fintype Symbol] [Fintype State] :
    ∃ a c : ℕ, ∀ s : ℕ, storageBound Symbol State k s ≤ a * 2 ^ (c * s) :=
  ⟨_, _, storageBound_le_base_mul_pow⟩

/-! ## The storage and the core of a configuration

Now we relate `Cfg` and `Storage` by givin the projection.
-/

/-- This function maps a `Cfg` to `Storage`, using `ℤ` as the index type for the tapes. -/
def Cfg.storage (c : Cfg k Symbol State input) : UnboundedStorage Symbol State k :=
  ⟨c.state, c.workTapes, c.workTapePos⟩

/-- The part of a configuration that the machine can still read: the input head position together
with the `Storage`, i.e. the configuration without the write-only output tape. -/
def Cfg.core (c : Cfg k Symbol State input) :
    Fin (input.length + 2) × UnboundedStorage Symbol State k :=
  (c.inputPos, c.storage)

/-- `step` never reads the output tape, so the core of the next configuration is determined by the
core of the current one. -/
lemma core_step_eq_of_core_eq {c₁ c₂ : Cfg k Symbol State input} (h : c₁.core = c₂.core) :
    (tm.step c₁).core = (tm.step c₂).core := by
  simp only [Cfg.core, Cfg.storage, Prod.mk.injEq, Storage.mk.injEq] at h
  obtain ⟨hpos, hstate, hwt, hwp⟩ := h
  have hsym : c₁.inputSymbol = c₂.inputSymbol := by simp [Cfg.inputSymbol, hpos]
  have hws : c₁.workTapeSymbols = c₂.workTapeSymbols := by
    funext i
    simp [Cfg.workTapeSymbols, hwt, hwp]
  simp only [Cfg.core, Cfg.storage, step, hstate, hsym, hws]
  cases c₂.state <;> simp [hpos, hstate, hwt, hwp]

/-! ## The storages and cores of a space-bounded run

These are the main results giving upper bounds on the number of storages and configuration cores
reachable in bounded space.
-/

/-- The storage reached after `t` steps fits in the windows given by the per-tape space usage up
to step `t`. -/
lemma storage_fitsIn (t : ℕ) :
    (tm.runFrom (tm.initCfg input) t).storage.FitsIn (tm.spaceUsedByTape (tm.initCfg input) t) := by
  refine ⟨?_, ?_⟩
  · intro j
    simpa [Cfg.storage] using tm.natAbs_le_spaceUsedByTape_of_mem_visited
      (tm.mem_visitedByTapeHead_self (tm.initCfg input) t j)
  · intro j
    exact content_natAbs_le_spaceUsedByTape t

/-- A machine that uses at most `s` cells of work-tape space at every point in time passes through
at most `storageBound Symbol State k s` different storages during its whole run — independently of
the length of the input and of how long it runs. -/
theorem encard_storages_le [Fintype Symbol] [Fintype State] {s : ℕ}
    (hs : ∀ t, tm.spaceUsed (tm.initCfg input) t ≤ s) :
    (Set.range fun t => (tm.runFrom (tm.initCfg input) t).storage).encard
      ≤ storageBound Symbol State k s := by
  obtain ⟨T, hT⟩ := tm.exists_spaceUsedByTape_max (tm.initCfg input) hs
  refine le_trans (Set.encard_le_encard ?_) (encard_fitsIn_le (hs T))
  rintro _ ⟨t, rfl⟩
  exact Storage.FitsIn_mono (fun i => hT t i) (tm.storage_fitsIn t)

/-- The number of configuration cores that a machine bounded by space `s` can reach is at most
`(n + 2) * storageBound Symbol State k s`, where `n` is the length of the input. -/
theorem encard_cores_le [Fintype Symbol] [Fintype State] {s : ℕ}
    (hs : ∀ t, tm.spaceUsed (tm.initCfg input) t ≤ s) :
    (Set.range fun t => (tm.runFrom (tm.initCfg input) t).core).encard
      ≤ (input.length + 2) * storageBound Symbol State k s := by
  calc (Set.range fun t => (tm.runFrom (tm.initCfg input) t).core).encard
      ≤ ((Set.univ : Set (Fin (input.length + 2)))
          ×ˢ (Set.range fun t => (tm.runFrom (tm.initCfg input) t).storage)).encard := by
        refine Set.encard_le_encard ?_
        rintro _ ⟨t, rfl⟩
        exact ⟨Set.mem_univ _, t, rfl⟩
    _ = (Set.univ : Set (Fin (input.length + 2))).encard
          * (Set.range fun t => (tm.runFrom (tm.initCfg input) t).storage).encard := Set.encard_prod
    _ ≤ (input.length + 2) * storageBound Symbol State k s := by
        refine mul_le_mul' ?_ (tm.encard_storages_le hs)
        simp [Set.encard_univ, ENat.card_eq_coe_fintype_card]

/-- The storage bound in exponential form: the number of storages a space-`s`-bounded machine
passes through is at most `2 ^ (O(s))`, with constants depending only on the machine. -/
theorem encard_storages_le_pow [Finite Symbol] [Finite State] :
    ∃ a c : ℕ, ∀ (input : List Symbol) (s : ℕ),
      (∀ t, tm.spaceUsed (tm.initCfg input) t ≤ s) →
      (Set.range fun t => (tm.runFrom (tm.initCfg input) t).storage).encard ≤ a * 2 ^ (c * s) := by
  have : Fintype Symbol := Fintype.ofFinite Symbol
  have : Fintype State := Fintype.ofFinite State
  obtain ⟨a, c, hpow⟩ := storageBound_le_pow (Symbol := Symbol) (State := State) (k := k)
  refine ⟨a, c, fun input s hs => (tm.encard_storages_le hs).trans ?_⟩
  exact_mod_cast hpow s

/-- The core bound in exponential form: the number of cores a space-`s`-bounded machine can reach
is at most `(n + 2) * 2 ^ (O(s))`, with constants depending only on the machine and not on the
input. -/
theorem encard_cores_le_pow [Finite Symbol] [Finite State] :
    ∃ a c : ℕ, ∀ (input : List Symbol) (s : ℕ),
      (∀ t, tm.spaceUsed (tm.initCfg input) t ≤ s) →
      (Set.range fun t => (tm.runFrom (tm.initCfg input) t).core).encard
        ≤ (input.length + 2) * a * 2 ^ (c * s) := by
  have : Fintype Symbol := Fintype.ofFinite Symbol
  have : Fintype State := Fintype.ofFinite State
  obtain ⟨a, c, hpow⟩ := storageBound_le_pow (Symbol := Symbol) (State := State) (k := k)
  refine ⟨a, c, fun input s hs => (tm.encard_cores_le hs).trans ?_⟩
  calc ((input.length + 2) * storageBound Symbol State k s : ℕ∞)
      ≤ ((input.length + 2) * (a * 2 ^ (c * s)) : ℕ) := by
        exact_mod_cast Nat.mul_le_mul_left _ (hpow s)
    _ = (input.length + 2) * a * 2 ^ (c * s) := by push_cast; ring

end Turing.MultiTapeTM
