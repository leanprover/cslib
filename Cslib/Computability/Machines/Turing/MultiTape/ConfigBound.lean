/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Tactic.Ring

/-!
# Bounds on the number of reachable configurations in bounded space

A finite computation using at most `s` cells of work-tape space can only reach a number
of configurations that differ in their storage content (state and work tapes) that is bounded
exponentially in `s`. Together with the `n + 2` possible positions of the input head this bounds
the number of configurations the machine can be in, disregarding the write-only output tape.

## Important Definitions

The results are layered, from the purely combinatorial to the machine-specific:

* `encard_fitsIn_le` is a counting statement about the type `Storage` alone and does
  not mention Turing machines: a memory whose non-blank cells and heads stay within per-tape
  windows of total size `s` can hold at most `storageBound Symbol State k s` different values.
* `MultiTapeNTM.RunPath.storage_fitsIn` is the geometric input: the final storage fits in the
  windows given by the path's per-tape space.
* `MultiTapeNTM.RunPath.encard_storages_le` combines the two: a space-bounded computation passes
  through at most `storageBound Symbol State k s` storages, independently of its time and input
  length. This is useful below logarithmic space, where the number of storages can be much smaller
  than the number of input head positions.
* `MultiTapeNTM.RunPath.encard_cores_le` adds the input head position, giving the bound
  `(n + 2) * storageBound Symbol State k s` on the number of visited *cores* (`Cfg.core`,
  a configuration without its output tape) for an input of length `n`.
* `MultiTapeTM.encard_storages_le` and `MultiTapeTM.encard_cores_le` extend these bounds to all
  times of a deterministic computation, provided every finite path respects the same space bound.
* `storageBound_le_base_mul_pow` restates `storageBound Symbol State k s` as
  `storageBoundBase Symbol State k * 2 ^ (storageBoundExp Symbol k * s)`, so that the bounds can
  be used to time-bound space-bounded machines.

## Design

The write-only output tape is never read by `Step`, so it can be dropped: what a machine can still
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

Each configuration on a finite path fits in that path's windows. For deterministic computations,
any finite set of visited storages or cores occurs within some finite path, so a uniform bound on
finite paths bounds all times as well. No separate infinite-run object is needed.
-/

@[expose] public section

namespace Turing

variable {k : ℕ}
variable {State Symbol : Type*}
variable {input : List Symbol}
variable {ntm : MultiTapeNTM k Symbol State}

/-!
## Storage

Defines the core data structure for this file, `Storage`, which contains the state and the work
tapes of a multi-tape Turing machine, with the work tape cells indexed over all of `ℤ`. It is
thus equivalent to a projection of `Cfg`.

Then `BoundedStorage` is introduced, which restricts the cells and the head position of each tape
to a window `[-s, s]` (with a different `s` for each tape) and is therefore a finite type. It is
proven that the restriction map is injective on those `Storage`s whose non-blank cells and head
positions all lie inside the `[-s, s]` windows, so that counting `BoundedStorage` bounds the
number of such `Storage`s.
-/

/-- The state and work-tape data of a machine. -/
@[ext]
structure Storage (Symbol State : Type*) (k : ℕ) where
  /-- the state of the TM (cf. `Cfg.state`) -/
  state : Option State
  /-- the contents of work tape `i` (cf. `Cfg.workTapes`) -/
  workTapes (i : Fin k) : ℤ → Option Symbol
  /-- the position of the head on work tape `i` (cf. `Cfg.workTapePos`) -/
  workTapePos (i : Fin k) : ℤ

/-- The window `[-s, s]` of tape positions allotted to a tape that uses `s` cells. -/
@[scoped grind =]
def window (s : ℕ) : Finset ℤ := Finset.Icc (-(s : ℤ)) s

@[scoped grind =]
lemma mem_window {s : ℕ} {z : ℤ} : z ∈ window s ↔ z.natAbs ≤ s := by
  grind

@[simp]
lemma card_window (s : ℕ) : (window s).card = 2 * s + 1 := by
  grind [Int.card_Icc]

/-- A bounded storage: the state and work-tape data of a machine, but with the cells and the head
position of tape `i` restricted to the finite window `[-(w i), w i]`. -/
abbrev BoundedStorage (Symbol State : Type*) {k : ℕ} (w : Fin k → ℕ) :=
  Option State × ((i : Fin k) → window (w i) → Option Symbol) × ((i : Fin k) → window (w i))

/-- A storage fits in the per-tape windows `w`: on each tape `j`, the head position and every
non-blank cell have absolute value `≤ w j`. -/
structure Storage.FitsIn (x : Storage Symbol State k) (w : Fin k → ℕ) : Prop where
  /-- the head position on every tape lies within its window -/
  pos_le : ∀ j, (x.workTapePos j).natAbs ≤ w j
  /-- every non-blank cell on every tape lies within its window -/
  cell_le : ∀ j z, x.workTapes j z ≠ none → z.natAbs ≤ w j

/-- If a `Storage` fits in a smaller window, it also fits in the larger window. -/
lemma Storage.FitsIn_mono {x : Storage Symbol State k} : Monotone x.FitsIn := by
  intro w₁ w₂ h_le h_fits
  refine ⟨?_, ?_⟩
  · intro j
    exact (h_fits.pos_le j).trans (h_le j)
  · intro j z h_ne
    exact (h_fits.cell_le j z h_ne).trans (h_le j)

/-- Restriction of a storage to the finite windows `w` (with heads outside their window
clamped to `0`). -/
def Storage.toBounded (x : Storage Symbol State k) (w : Fin k → ℕ) :
    BoundedStorage Symbol State w :=
  (x.state, fun j z => x.workTapes j z.1,
    fun j => if h : x.workTapePos j ∈ window (w j) then ⟨x.workTapePos j, h⟩
      else ⟨0, mem_window.mpr (Nat.zero_le _)⟩)

/-- The restriction is injective on storages that fit in the windows. -/
lemma Storage.toBounded_injOn (w : Fin k → ℕ) :
    Set.InjOn (Storage.toBounded (Symbol := Symbol) (State := State) · w) {x | x.FitsIn w} := by
  rintro x ⟨_, _⟩ y ⟨_, _⟩ hxy
  simp only [Storage.toBounded, Prod.mk.injEq] at hxy
  obtain ⟨hstate, htapes, hpos⟩ := hxy
  apply Storage.ext hstate (funext₂ fun j z => ?_) (funext fun j => ?_)
  · by_cases hz : z ∈ window (w j)
    · exact congrFun (congrFun htapes j) ⟨z, hz⟩
    · grind
  · grind [congrFun hpos j]

/-! ## Counting storages

This section is purely combinatorial: it counts how many values a `Storage` restricted to given
windows can take, without reference to a machine or a run.
-/

/-- An upper bound on the number of storages a `k`-tape machine can be in while using
at most `s` cells of total work-tape space, over the given alphabet and state set. The `(2s + 1)^k`
factor counts the possible head positions; the dominant factor `(|Symbol| + 1)^(2s + k)` uses the
*total* space `s` in the exponent (the `k` tapes share the space budget). -/
def storageBound (Symbol State : Type*) [Fintype Symbol] [Fintype State] (k s : ℕ) : ℕ :=
  (Fintype.card State + 1) * ((2 * s + 1) ^ k * (Fintype.card Symbol + 1) ^ (2 * s + k))

/-- The number of bounded storages is at most `storageBound`. Counting the tapes separately gives
the per-tape product `∏ᵢ (2 wᵢ + 1) · (|Symbol| + 1) ^ (2 wᵢ + 1)`; each tape uses at most the
total space `s`, and the tapes together use at most `s`, which collapses the alphabet exponent
to `2s + k`. -/
lemma card_boundedStorage_le [Fintype Symbol] [Fintype State]
    {w : Fin k → ℕ} {s : ℕ} (hsum : ∑ i, w i ≤ s) :
    Fintype.card (BoundedStorage Symbol State w) ≤ storageBound Symbol State k s := by
  have hle : ∀ i, w i ≤ s := fun i =>
    (Finset.single_le_sum (fun i _ => Nat.zero_le (w i)) (Finset.mem_univ i)).trans hsum
  simp only [BoundedStorage, storageBound, Fintype.card_prod, Fintype.card_option,
    Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_coe, card_window]
  rw [mul_comm (∏ i, (Fintype.card Symbol + 1) ^ (2 * w i + 1)), Finset.prod_pow_eq_pow_sum]
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
    {x : Storage Symbol State k | x.FitsIn w}.encard
      ≤ storageBound Symbol State k s := by
  calc {x : Storage Symbol State k | x.FitsIn w}.encard
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
    _ ≤ states * ((2 ^ (s + 1)) ^ k * (2 ^ syms) ^ (2 * s + k)) := by gcongr <;> omega
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

Now we relate `Cfg` and `Storage` by giving the projection.
-/

/-- This function maps a `Cfg` to `Storage`, forgetting the input head position and the
write-only output tape. -/
def Cfg.storage (c : Cfg k Symbol State input) : Storage Symbol State k :=
  ⟨c.state, c.workTapes, c.workTapePos⟩

/-- The part of a configuration that the machine can still read: the input head position together
with the `Storage`, i.e. the configuration without the write-only output tape. -/
def Cfg.core (c : Cfg k Symbol State input) :
    Fin (input.length + 2) × Storage Symbol State k :=
  (c.inputPos, c.storage)

/-- Steps do not read the output tape. Configurations with the same core can match each other's
steps while preserving equality of cores, even when transitions are nondeterministic. -/
lemma MultiTapeNTM.Step.exists_core_eq {c₁ c₂ d₁ : Cfg k Symbol State input}
    (hstep : ntm.Step c₁ d₁) (h : c₁.core = c₂.core) :
    ∃ d₂, ntm.Step c₂ d₂ ∧ d₁.core = d₂.core := by
  simp only [Cfg.core, Cfg.storage, Prod.mk.injEq, Storage.mk.injEq] at h
  obtain ⟨hpos, hstate, hwt, hwp⟩ := h
  have hsym : c₁.inputSymbol = c₂.inputSymbol := by simp [Cfg.inputSymbol, hpos]
  have hws : c₁.workTapeSymbols = c₂.workTapeSymbols := by
    funext i
    simp [Cfg.workTapeSymbols, hwt, hwp]
  cases hq : c₁.state with
  | none =>
    obtain rfl := (MultiTapeNTM.step_of_halt hq).mp hstep
    exact ⟨c₂, (MultiTapeNTM.step_of_halt (hstate.symm.trans hq)).mpr rfl,
      by simp [Cfg.core, Cfg.storage, hpos, hstate, hwt, hwp]⟩
  | some q =>
    obtain ⟨a, ha, rfl⟩ := (show ∃ a, ntm.Tr q c₁.inputSymbol c₁.workTapeSymbols a ∧
      d₁ = a.apply c₁ from by simpa [MultiTapeNTM.Step, hq] using hstep)
    refine ⟨a.apply c₂, ?_, ?_⟩
    · simpa [MultiTapeNTM.Step, ← hstate, hq, ← hsym, ← hws] using
        (show ∃ b, ntm.Tr q c₁.inputSymbol c₁.workTapeSymbols b ∧ a.apply c₂ = b.apply c₂ from
          ⟨a, ha, rfl⟩)
    · simp [Cfg.core, Cfg.storage, hpos, hwt, hwp]

/-! ## The storages and cores of a space-bounded run

These are the main results giving upper bounds on the number of storages and configuration cores
reachable in bounded space.
-/

namespace MultiTapeNTM

/-- The final storage of a computation fits in the windows given by its per-tape space. -/
lemma RunPath.storage_fitsIn (p : ntm.ComputationPath input) :
    p.last.storage.FitsIn p.spaceByTape := by
  constructor
  · intro j
    simpa [Cfg.storage] using p.natAbs_le_spaceByTape_of_mem_visited j
      (p.last_workTapePos_mem_visited j)
  · exact p.content_natAbs_le_spaceByTape

namespace RunPath

variable (p : ntm.ComputationPath input)

/-- Every storage on a computation fits in the windows given by the whole path's per-tape space. -/
lemma storage_fitsIn_of_mem {cfg : Cfg k Symbol State input} (h : cfg ∈ p.cfgs) :
    cfg.storage.FitsIn p.spaceByTape := by
  obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.mp h
  exact Storage.FitsIn_mono
    ((p.take n hn).spaceByTape_mono p (List.take_subset ..)) (p.take n hn).storage_fitsIn

/-- A computation using at most `s` work-tape cells visits at most
`storageBound Symbol State k s` storages, independently of its time and input length. -/
theorem encard_storages_le [Fintype Symbol] [Fintype State] {s : ℕ} (hs : p.space ≤ s) :
    (Cfg.storage '' {cfg | cfg ∈ p.cfgs}).encard ≤ storageBound Symbol State k s := by
  refine le_trans (Set.encard_le_encard ?_) (encard_fitsIn_le hs)
  rintro _ ⟨cfg, hcfg, rfl⟩
  exact p.storage_fitsIn_of_mem hcfg

/-- A space-`s`-bounded computation visits at most
`(input.length + 2) * storageBound Symbol State k s` configuration cores. -/
theorem encard_cores_le [Fintype Symbol] [Fintype State] {s : ℕ} (hs : p.space ≤ s) :
    (Cfg.core '' {cfg | cfg ∈ p.cfgs}).encard
      ≤ (input.length + 2) * storageBound Symbol State k s := by
  calc (Cfg.core '' {cfg | cfg ∈ p.cfgs}).encard
      ≤ ((Set.univ : Set (Fin (input.length + 2)))
          ×ˢ (Cfg.storage '' {cfg | cfg ∈ p.cfgs})).encard := by
        apply Set.encard_le_encard
        rintro _ ⟨cfg, hcfg, rfl⟩
        exact ⟨Set.mem_univ _, cfg, hcfg, rfl⟩
    _ = (Set.univ : Set (Fin (input.length + 2))).encard
          * (Cfg.storage '' {cfg | cfg ∈ p.cfgs}).encard := Set.encard_prod
    _ ≤ (input.length + 2) * storageBound Symbol State k s := by
        refine mul_le_mul' ?_ (p.encard_storages_le hs)
        simp [Set.encard_univ, ENat.card_eq_coe_fintype_card]

/-- The number of storages on a space-`s`-bounded computation is at most `2 ^ (O(s))`,
with constants depending only on the machine. -/
theorem encard_storages_le_pow [Finite Symbol] [Finite State] :
    ∃ a c : ℕ, ∀ (input : List Symbol) (p : ntm.ComputationPath input) (s : ℕ),
      p.space ≤ s → (Cfg.storage '' {cfg | cfg ∈ p.cfgs}).encard ≤ a * 2 ^ (c * s) := by
  have : Fintype Symbol := Fintype.ofFinite Symbol
  have : Fintype State := Fintype.ofFinite State
  obtain ⟨a, c, hpow⟩ := storageBound_le_pow (Symbol := Symbol) (State := State) (k := k)
  refine ⟨a, c, fun input p s hs => (p.encard_storages_le hs).trans ?_⟩
  exact_mod_cast hpow s

/-- The number of cores on a space-`s`-bounded computation is at most `(n + 2) * 2 ^ (O(s))`,
with constants depending only on the machine. -/
theorem encard_cores_le_pow [Finite Symbol] [Finite State] :
    ∃ a c : ℕ, ∀ (input : List Symbol) (p : ntm.ComputationPath input) (s : ℕ),
      p.space ≤ s → (Cfg.core '' {cfg | cfg ∈ p.cfgs}).encard
        ≤ (input.length + 2) * a * 2 ^ (c * s) := by
  have : Fintype Symbol := Fintype.ofFinite Symbol
  have : Fintype State := Fintype.ofFinite State
  obtain ⟨a, c, hpow⟩ := storageBound_le_pow (Symbol := Symbol) (State := State) (k := k)
  refine ⟨a, c, fun input p s hs => (p.encard_cores_le hs).trans ?_⟩
  calc ((input.length + 2) * storageBound Symbol State k s : ℕ∞)
      ≤ ((input.length + 2) * (a * 2 ^ (c * s)) : ℕ) := by
        exact_mod_cast Nat.mul_le_mul_left _ (hpow s)
    _ = (input.length + 2) * a * 2 ^ (c * s) := by push_cast; ring

end RunPath

end MultiTapeNTM

-- A uniform bound on finite prefixes also bounds the full range: any larger finite subset
-- of the range would already be contained in one prefix.
private lemma encard_range_le_of_prefixes {α : Type*} (f : ℕ → α) (b : ℕ)
    (h : ∀ t, (f '' Set.Iic t).encard ≤ b) : (Set.range f).encard ≤ b := by
  by_contra! hcard
  have hsucc : ((b + 1 : ℕ) : ℕ∞) ≤ (Set.range f).encard := by
    simpa using ENat.natCast_add_one_le_iff.mpr hcard
  obtain ⟨s, hs, hsize⟩ := Set.exists_subset_encard_eq hsucc
  obtain ⟨u, _, hu, rfl⟩ := (Set.finite_of_encard_eq_coe hsize).exists_subset_finite_image_eq
    (f := f) (s := Set.univ) (by simpa using hs)
  obtain ⟨t, ht⟩ := hu.bddAbove
  have hle := (Set.encard_mono (Set.image_mono ht)).trans (h t)
  rw [hsize] at hle
  exact (Nat.not_succ_le_self b) (by exact_mod_cast hle)

namespace MultiTapeTM

variable (tm : MultiTapeTM k Symbol State)

/-- If every finite computation uses at most `s` cells, the deterministic machine visits at most
`storageBound Symbol State k s` storages over all times. -/
theorem encard_storages_le [Fintype Symbol] [Fintype State] {s : ℕ}
    (hs : ∀ t, tm.spaceUsed (tm.initCfg input) t ≤ s) :
    (Set.range fun t => (tm.runFrom (tm.initCfg input) t).storage).encard
      ≤ storageBound Symbol State k s := by
  apply encard_range_le_of_prefixes
  intro t
  let p : tm.ComputationPath input :=
    { cfgs := List.ofFn fun n : Fin (t + 1) => tm.runFrom (tm.initCfg input) n
      last := tm.runFrom (tm.initCfg input) t
      isChainFromTo :=
        { isChain := by
            simp only [List.isChain_iff_getElem, List.length_ofFn, List.getElem_ofFn]
            intro n hn
            simp [runFrom, Function.iterate_succ_apply']
          ne_nil := by simp
          head_eq := by simp [runFrom]
          getLast_eq := List.getLast_ofFn _ } }
  refine le_trans (Set.encard_mono ?_) (p.encard_storages_le (hs t))
  rintro _ ⟨n, hn, rfl⟩
  refine ⟨tm.runFrom (tm.initCfg input) n, ?_, rfl⟩
  exact List.mem_ofFn.mpr ⟨⟨n, Nat.lt_succ_of_le hn⟩, rfl⟩

/-- A deterministic machine using at most `s` cells at every time visits at most
`(input.length + 2) * storageBound Symbol State k s` configuration cores over all times. -/
theorem encard_cores_le [Fintype Symbol] [Fintype State] {s : ℕ}
    (hs : ∀ t, tm.spaceUsed (tm.initCfg input) t ≤ s) :
    (Set.range fun t => (tm.runFrom (tm.initCfg input) t).core).encard
      ≤ (input.length + 2) * storageBound Symbol State k s := by
  apply encard_range_le_of_prefixes
  intro t
  let p : tm.ComputationPath input :=
    { cfgs := List.ofFn fun n : Fin (t + 1) => tm.runFrom (tm.initCfg input) n
      last := tm.runFrom (tm.initCfg input) t
      isChainFromTo :=
        { isChain := by
            simp only [List.isChain_iff_getElem, List.length_ofFn, List.getElem_ofFn]
            intro n hn
            simp [runFrom, Function.iterate_succ_apply']
          ne_nil := by simp
          head_eq := by simp [runFrom]
          getLast_eq := List.getLast_ofFn _ } }
  refine le_trans (Set.encard_mono ?_) (p.encard_cores_le (hs t))
  rintro _ ⟨n, hn, rfl⟩
  refine ⟨tm.runFrom (tm.initCfg input) n, ?_, rfl⟩
  exact List.mem_ofFn.mpr ⟨⟨n, Nat.lt_succ_of_le hn⟩, rfl⟩

/-- A deterministic space-`s`-bounded computation visits at most `2 ^ (O(s))` storages over all
times, with constants depending only on the machine. -/
theorem encard_storages_le_pow [Finite Symbol] [Finite State] :
    ∃ a c : ℕ, ∀ (input : List Symbol) (s : ℕ),
      (∀ t, tm.spaceUsed (tm.initCfg input) t ≤ s) →
      (Set.range fun t => (tm.runFrom (tm.initCfg input) t).storage).encard ≤ a * 2 ^ (c * s) := by
  have : Fintype Symbol := Fintype.ofFinite Symbol
  have : Fintype State := Fintype.ofFinite State
  obtain ⟨a, c, hpow⟩ := storageBound_le_pow (Symbol := Symbol) (State := State) (k := k)
  refine ⟨a, c, fun input s hs => (tm.encard_storages_le hs).trans ?_⟩
  exact_mod_cast hpow s

/-- A deterministic space-`s`-bounded computation visits at most `(n + 2) * 2 ^ (O(s))` cores over
all times, with constants depending only on the machine. -/
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

end MultiTapeTM

end Turing
