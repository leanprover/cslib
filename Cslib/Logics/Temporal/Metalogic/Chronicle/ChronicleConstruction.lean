/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Temporal.Metalogic.Chronicle.ChronicleTypes
public import Cslib.Logics.Temporal.Metalogic.Chronicle.RRelation
public import Cslib.Logics.Temporal.Metalogic.Chronicle.PointInsertion
public import Cslib.Logics.Temporal.Metalogic.Chronicle.CounterexampleElimination
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Denumerable

/-!
# Chronicle Construction (Omega-Chain and Claim 2.11)

This module implements the omega-chain construction from Burgess 1982 Section 2.
Starting from a singleton chronicle `{0 -> A0}` for a given MCS `A0`, we
iteratively eliminate all C5/C5' counterexamples by inserting new points,
producing in the limit a chronicle satisfying all conditions C0-C5/C5'.

## Main Results

- `singletonChronicle`: The initial chronicle with a single point mapping to
  a given MCS.

- `omegaChain`: The omega-indexed sequence of chronicles, each extending the
  previous by eliminating one counterexample.

- `limit_chronicle`: The limit (union) of the omega-chain.

- `limit_satisfies_c0`: The limit chronicle satisfies C0 (all points map to MCS).

- `limit_satisfies_c5`: The limit chronicle satisfies C5 (all Until obligations
  have witnesses).

## Design Notes

The omega-chain construction uses the countability of potential counterexamples.
Each step either eliminates a counterexample (extending the domain) or leaves
the chronicle unchanged. The limit satisfies C5/C5' because every potential
counterexample is eventually addressed.

The construction indexes potential counterexamples by natural numbers using
an enumeration of `Rat x Formula x Formula x Bool`. Since both `Rat` and
`Formula` are countable, this enumeration exists.

## References

- Burgess 1982: "Axioms for tense logic II: Time periods", Section 2
-/

@[expose] public section

namespace Cslib.Logic.Temporal.Metalogic.Chronicle

set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.flexible false

attribute [local instance] Classical.propDecidable

variable {Atom : Type*}
variable [Denumerable (Formula Atom)]

open Cslib.Logic.Temporal

open Cslib.Logic.Temporal.Metalogic

/-! ## Singleton Chronicle

The initial chronicle with a single point at rational 0, mapping to a given MCS.
-/

/--
The **singleton chronicle** with domain {0} and f(0) = A for a given MCS A.
The interval function g is trivially defined (no adjacent pairs exist in a
singleton domain).
-/
noncomputable def singletonChronicle (A : Set (Formula Atom)) : Chronicle Atom :=
  { f := fun _ => A
    g := fun _ _ => ∅
    dom := {(0 : Rat)} }

/--
The singleton chronicle satisfies C0 when A is an MCS.
-/
theorem singleton_c0 {A : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent A) :
    (singletonChronicle A).c0 := by
  intro x hx
  simp only [singletonChronicle] at hx ⊢
  rw [Finset.mem_singleton] at hx
  subst hx
  exact h_mcs

/--
The domain of the singleton chronicle is {0}.
-/
theorem singleton_dom (A : Set (Formula Atom)) :
    (singletonChronicle A).dom = {(0 : Rat)} := rfl

/--
f(0) = A in the singleton chronicle.
-/
theorem singleton_f_zero (A : Set (Formula Atom)) :
    (singletonChronicle A).f 0 = A := rfl

/--
The singleton chronicle satisfies the full ChronicleInvariant (C0-C3) vacuously.
All pair/triple conditions are vacuously true since {0} has no pairs.
-/
theorem singleton_invariant {A : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent A) :
    ChronicleInvariant (singletonChronicle A) where
  hc0 := singleton_c0 h_mcs
  hc1 := by
    intro x y hx hy hxy
    simp only [singletonChronicle, Finset.mem_singleton] at hx hy
    subst hx; subst hy; exact absurd hxy (lt_irrefl _)
  hc2' := by
    intro x y hadj
    obtain ⟨hx, hy, hxy, _⟩ := hadj
    simp only [singletonChronicle, Finset.mem_singleton] at hx hy
    subst hx; subst hy; exact absurd hxy (lt_irrefl _)
  hc3 := by
    intro x y z hx hy hz hxy hyz
    simp only [singletonChronicle, Finset.mem_singleton] at hx hy
    subst hx; subst hy; exact absurd hxy (lt_irrefl _)

/--
The singleton chronicle satisfies C2' vacuously (no adjacent pairs in {0}).
-/
theorem singleton_c2' {A : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent A) :
    (singletonChronicle A).c2' := by
  intro x y hadj
  obtain ⟨hx, hy, hxy, _⟩ := hadj
  simp only [singletonChronicle, Finset.mem_singleton] at hx hy
  subst hx; subst hy; exact absurd hxy (lt_irrefl _)

/-! ## G-Value Construction

Each elimination step now carries c2' directly: the EliminationResult includes
a proof that the result chronicle satisfies BurgessR3Maximal for all adjacent
pairs. No separate g-rebuild pass is needed.

Previously, a `rebuild_g` function reassigned g-values at every step using
`burgessR3Maximal_exists_general`. That theorem was FALSE (counterexample:
arbitrary MCS A with G(p), C with p.neg). The correct approach is
context-specific seed construction within each elimination function.
-/

/--
The singleton chronicle satisfies C4 vacuously: a singleton domain has no
pairs x < y, so the universal quantifier is vacuously true.
-/
theorem singleton_c4 (A : Set (Formula Atom)) :
    (singletonChronicle A).c4 := by
  intro x y hx hy hxy
  -- dom = {0}, so x = 0 and y = 0, contradicting x < y
  simp only [singletonChronicle, Finset.mem_singleton] at hx hy
  subst hx; subst hy
  exact absurd hxy (lt_irrefl _)

/--
The singleton chronicle satisfies C4' vacuously (mirror of C4).
-/
theorem singleton_c4' (A : Set (Formula Atom)) :
    (singletonChronicle A).c4' := by
  intro x y hx hy hyx
  simp only [singletonChronicle, Finset.mem_singleton] at hx hy
  subst hx; subst hy
  exact absurd hyx (lt_irrefl _)

/-! ## Countability of Potential Counterexamples

PotentialCounterexample is countable (all fields are countable) and infinite
(Rat embeds into it), hence Denumerable (bijection with Nat).
-/

/-- PotentialCounterexample is countable since all its fields are countable. -/
instance : Countable (@PotentialCounterexample Atom) :=
  Function.Injective.countable
    (f := fun pc => (pc.x, pc.y, pc.ξ, pc.η, pc.kind))
    (fun a b h => by
      cases a; cases b
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      subst h1; subst h2; subst h3; subst h4; subst h5; rfl)

/-- PotentialCounterexample is infinite since Rat embeds into it. -/
instance : Infinite (@PotentialCounterexample Atom) :=
  Infinite.of_injective
    (fun (q : ℚ) => PotentialCounterexample.mk q 0 (Formula.bot : Formula Atom) (Formula.bot : Formula Atom) .c5_forward)
    (fun a b h => by injection h)

/-- PotentialCounterexample is Denumerable (countable + infinite). -/
noncomputable instance : Denumerable (@PotentialCounterexample Atom) :=
  Classical.choice (nonempty_denumerable _)

/-! ## Omega-Chain Construction

The key idea: enumerate all potential counterexamples
(Rat x Rat x Formula x Formula x PotentialCounterexampleKind)
and process them one at a time. At step n, process the n-th potential counterexample.
If it is an actual counterexample for the current chronicle, eliminate it.
Otherwise, leave the chronicle unchanged.

The enumeration exists because Rat, Formula, and PotentialCounterexampleKind
are all countable, making PotentialCounterexample Denumerable.
-/

/--
An enumeration of potential counterexamples. Uses the `Denumerable` instance
on `PotentialCounterexample` (which is countable and infinite, hence in
bijection with Nat) to assign a counterexample to each natural number.
-/
noncomputable def counterexampleEnum : Nat → @PotentialCounterexample Atom :=
  fun n => Denumerable.ofNat (@PotentialCounterexample Atom) n

/--
The enumeration covers all potential counterexamples: for any
(x, y, xi, eta, kind), there exists n such that counterexampleEnum n
matches that tuple. This follows from the surjectivity of
`Denumerable.ofNat`.
-/
theorem counterexample_enum_surjective :
    ∀ pc : @PotentialCounterexample Atom, ∃ n : Nat, counterexampleEnum n = pc := by
  intro pc
  exact ⟨Encodable.encode pc, Denumerable.ofNat_encode pc⟩

/--
The counterexample enumeration (via Cantor unpairing) covers all potential
counterexamples above any threshold. For any pc and k, there exists n ≥ k
such that `counterexampleEnum (Nat.unpair n).2 = pc`.

This is the key property needed for the limit argument: even if a counterexample's
canonical index j is below the step where its domain point enters, there exist
arbitrarily large steps n where counterexample j is re-processed.
-/
theorem counterexample_enum_surjective_above (pc : @PotentialCounterexample Atom) (k : Nat) :
    ∃ n : Nat, n ≥ k ∧ counterexampleEnum (Nat.unpair n).2 = pc := by
  have ⟨j, hj⟩ := counterexample_enum_surjective pc
  exact ⟨Nat.pair k j, Nat.left_le_pair k j,
    by simp [Nat.unpair_pair, hj]⟩

/-! ## Omega-Chain: Iterated Counterexample Elimination -/

/--
The **omega-chain**: a sequence of chronicles indexed by Nat, where each
chronicle extends the previous one by eliminating a potential counterexample.

Uses Cantor unpairing: at step n+1, process `counterexampleEnum (Nat.unpair n).2`.
This ensures every counterexample index j is processed at infinitely many steps
(for all i, step `Nat.pair i j + 1` processes counterexample j). This is essential
because a counterexample (x, ξ, η) can only be eliminated when x is already in the
domain, and x may enter the domain at a later step than the counterexample's first
enumeration index.

The invariant maintained at every stage is `c0`:
- c0: every domain point maps to an MCS

Each step calls `eliminatePotentialCounterexample` which produces
a chronicle with c0. The c2' invariant is no longer threaded through
finite stages (Phase 7 change); it is vacuously true at the limit
since the limit domain is dense with no adjacent pairs.

- omegaChain 0 = singletonChronicle A
- omegaChain (n+1) = eliminate(omegaChain n, enum (unpair n).2)
-/
noncomputable def omegaChain (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A) :
    (n : Nat) → { χ : Chronicle Atom // χ.c0 ∧ χ.c2' }
  | 0 => ⟨singletonChronicle A, ⟨singleton_c0 h_mcs, singleton_c2' h_mcs⟩⟩
  | n + 1 =>
    let prev := omegaChain A h_mcs n
    let pc := counterexampleEnum (Nat.unpair n).2
    let elim := eliminatePotentialCounterexample prev.val prev.property.1 prev.property.2 pc
    ⟨elim.val, ⟨elim.c0, elim.c2'⟩⟩

/--
Extract the chronicle at step n.
-/
noncomputable def omegaChainVal (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    (n : Nat) : Chronicle Atom :=
  (omegaChain A h_mcs n).val

/--
The chronicle at step n satisfies C0.
-/
theorem omega_chain_c0 (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    (n : Nat) :
    (omegaChainVal A h_mcs n).c0 :=
  (omegaChain A h_mcs n).property.1

/-- The chronicle at step n satisfies c2'. -/
theorem omega_chain_c2' (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    (n : Nat) :
    (omegaChainVal A h_mcs n).c2' :=
  (omegaChain A h_mcs n).property.2

/--
The elimination result at step n (the intermediate chronicle before g-rebuild).
-/
noncomputable def omegaChainElimResult (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    (n : Nat) : EliminationResult (omegaChain A h_mcs n).val (counterexampleEnum (Nat.unpair n).2) :=
  eliminatePotentialCounterexample
    (omegaChain A h_mcs n).val
    (omegaChain A h_mcs n).property.1
    (omegaChain A h_mcs n).property.2
    (counterexampleEnum (Nat.unpair n).2)


/--
The f function at step n+1 is the same as the elimination result's f function.
-/
theorem omega_chain_f_eq_elim (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    (n : Nat) :
    (omegaChainVal A h_mcs (n + 1)).f = (omegaChainElimResult A h_mcs n).val.f := by
  simp only [omegaChainVal, omegaChain, omegaChainElimResult]

/--
The dom at step n+1 is the same as the elimination result's dom.
-/
theorem omega_chain_dom_eq_elim (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    (n : Nat) :
    (omegaChainVal A h_mcs (n + 1)).dom = (omegaChainElimResult A h_mcs n).val.dom := by
  simp only [omegaChainVal, omegaChain, omegaChainElimResult]

/--
The domain is monotonically increasing along the omega-chain.
-/
theorem omega_chain_dom_mono (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    (n : Nat) :
    (omegaChainVal A h_mcs n).dom ⊆ (omegaChainVal A h_mcs (n + 1)).dom := by
  rw [omega_chain_dom_eq_elim]
  exact (omegaChainElimResult A h_mcs n).dom_sub

/--
The point function agrees on old domain points across the chain.
-/
theorem omega_chain_f_agrees (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    (n : Nat) (x : Rat) (hx : x ∈ (omegaChainVal A h_mcs n).dom) :
    (omegaChainVal A h_mcs (n + 1)).f x = (omegaChainVal A h_mcs n).f x := by
  have := omega_chain_f_eq_elim A h_mcs n
  rw [show (omegaChainVal A h_mcs (n + 1)).f x =
    (omegaChainElimResult A h_mcs n).val.f x from congr_fun this x]
  exact (omegaChainElimResult A h_mcs n).f_agrees x hx

/--
Domain monotonicity extends transitively: for m ≤ n, dom(m) ⊆ dom(n).
-/
theorem omega_chain_dom_mono_le (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    {m n : Nat} (h : m ≤ n) :
    (omegaChainVal A h_mcs m).dom ⊆ (omegaChainVal A h_mcs n).dom := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | step h ih => exact Finset.Subset.trans ih (omega_chain_dom_mono A h_mcs _)

/--
f agreement extends transitively: for m ≤ n and x in dom(m), f_n(x) = f_m(x).
-/
theorem omega_chain_f_agrees_le (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    {m n : Nat} (h : m ≤ n) (x : Rat)
    (hx : x ∈ (omegaChainVal A h_mcs m).dom) :
    (omegaChainVal A h_mcs n).f x = (omegaChainVal A h_mcs m).f x := by
  induction h with
  | refl => rfl
  | step h ih =>
    rw [omega_chain_f_agrees A h_mcs _ x (omega_chain_dom_mono_le A h_mcs h hx)]
    exact ih

theorem omega_chain_g_eq_elim (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    (n : Nat) :
    (omegaChainVal A h_mcs (n + 1)).g = (omegaChainElimResult A h_mcs n).val.g := by
  simp only [omegaChainVal, omegaChain, omegaChainElimResult]

theorem omega_chain_g_agrees (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    (n : Nat) (x y : Rat)
    (hx : x ∈ (omegaChainVal A h_mcs n).dom)
    (hy : y ∈ (omegaChainVal A h_mcs n).dom) :
    (omegaChainVal A h_mcs (n + 1)).g x y = (omegaChainVal A h_mcs n).g x y := by
  have := omega_chain_g_eq_elim A h_mcs n
  rw [show (omegaChainVal A h_mcs (n + 1)).g x y =
    (omegaChainElimResult A h_mcs n).val.g x y from
    congr_fun (congr_fun this x) y]
  exact (omegaChainElimResult A h_mcs n).g_agrees x y hx hy

theorem omega_chain_g_agrees_le (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    {m n : Nat} (h : m ≤ n) (x y : Rat)
    (hx : x ∈ (omegaChainVal A h_mcs m).dom)
    (hy : y ∈ (omegaChainVal A h_mcs m).dom) :
    (omegaChainVal A h_mcs n).g x y = (omegaChainVal A h_mcs m).g x y := by
  induction h with
  | refl => rfl
  | step h ih =>
    rw [omega_chain_g_agrees A h_mcs _ x y
      (omega_chain_dom_mono_le A h_mcs h hx)
      (omega_chain_dom_mono_le A h_mcs h hy)]
    exact ih

/--
C5 witness at step n+1: if `counterexampleEnum (Nat.unpair n).2` is a c5_forward
counterexample with x ∈ dom(n) and U(ξ,η) ∈ f_n(x), then a witness exists in dom(n+1).

This directly exposes the `c5_forward_witness` field of `EliminationResult`,
including the adjacent-pair guard: ξ ∈ g(n+1)(a,b) for all adjacent (a,b)
between x and y. This guard is essential for the strong C5 (Burgess C5a).
-/
theorem omega_chain_c5_witness (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    (n : Nat) (x : Rat) (ξ η : Formula Atom)
    (hx : x ∈ (omegaChainVal A h_mcs n).dom)
    (h_until : (η U ξ) ∈ (omegaChainVal A h_mcs n).f x)
    (hn_eq : counterexampleEnum (Nat.unpair n).2 = ⟨x, 0, ξ, η, .c5_forward⟩) :
    ∃ y ∈ (omegaChainVal A h_mcs (n + 1)).dom,
      x < y ∧ η ∈ (omegaChainVal A h_mcs (n + 1)).f y ∧
      (∀ a b, Adjacent (omegaChainVal A h_mcs (n + 1)).dom a b →
        x ≤ a → b ≤ y → ξ ∈ (omegaChainVal A h_mcs (n + 1)).g a b) ∧
      (∀ w ∈ (omegaChainVal A h_mcs n).dom,
        x < w → w < y → ξ ∈ (omegaChainVal A h_mcs (n + 1)).f w) ∧
      (y ∉ (omegaChainVal A h_mcs n).dom ∨
        ∀ u ∈ (omegaChainVal A h_mcs (n + 1)).dom,
          u ∈ (omegaChainVal A h_mcs n).dom) := by
  -- omegaChain(n+1) = elimination result directly
  rw [omega_chain_dom_eq_elim, omega_chain_f_eq_elim, omega_chain_g_eq_elim]
  have key := (omegaChainElimResult A h_mcs n).c5_forward_witness
    (show (counterexampleEnum (Nat.unpair n).2).kind = .c5_forward by rw [hn_eq])
    (show (counterexampleEnum (Nat.unpair n).2).x ∈ (omegaChainVal A h_mcs n).dom
      by rw [hn_eq]; exact hx)
    (show Formula.untl (counterexampleEnum (Nat.unpair n).2).η
        (counterexampleEnum (Nat.unpair n).2).ξ ∈
        (omegaChainVal A h_mcs n).f (counterexampleEnum (Nat.unpair n).2).x
      by rw [hn_eq]; exact h_until)
  obtain ⟨y, hy_dom, hy_lt, hy_η, hy_adj_guard, hy_dom_guard, hy_new_or_id⟩ := key
  refine ⟨y, hy_dom, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hn_eq] at hy_lt; exact hy_lt
  · simp only [hn_eq] at hy_η; exact hy_η
  · intro a b h_adj ha hb
    simp only [hn_eq] at hy_adj_guard
    exact hy_adj_guard a b h_adj ha hb
  · intro w hw hxw hwy
    simp only [hn_eq] at hy_dom_guard
    exact hy_dom_guard w hw hxw hwy
  · exact hy_new_or_id

/--
C5' witness at step n+1 (mirror for Since), including the adjacent-pair guard.
-/
theorem omega_chain_c5'_witness (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    (n : Nat) (x : Rat) (ξ η : Formula Atom)
    (hx : x ∈ (omegaChainVal A h_mcs n).dom)
    (h_since : (η S ξ) ∈ (omegaChainVal A h_mcs n).f x)
    (hn_eq : counterexampleEnum (Nat.unpair n).2 = ⟨x, 0, ξ, η, .c5_backward⟩) :
    ∃ y ∈ (omegaChainVal A h_mcs (n + 1)).dom,
      y < x ∧ η ∈ (omegaChainVal A h_mcs (n + 1)).f y ∧
      (∀ a b, Adjacent (omegaChainVal A h_mcs (n + 1)).dom a b →
        y ≤ a → b ≤ x → ξ ∈ (omegaChainVal A h_mcs (n + 1)).g a b) ∧
      (∀ w ∈ (omegaChainVal A h_mcs n).dom,
        y < w → w < x → ξ ∈ (omegaChainVal A h_mcs (n + 1)).f w) ∧
      (y ∉ (omegaChainVal A h_mcs n).dom ∨
        ∀ u ∈ (omegaChainVal A h_mcs (n + 1)).dom,
          u ∈ (omegaChainVal A h_mcs n).dom) := by
  rw [omega_chain_dom_eq_elim, omega_chain_f_eq_elim, omega_chain_g_eq_elim]
  have key := (omegaChainElimResult A h_mcs n).c5_backward_witness
    (show (counterexampleEnum (Nat.unpair n).2).kind = .c5_backward by rw [hn_eq])
    (show (counterexampleEnum (Nat.unpair n).2).x ∈ (omegaChainVal A h_mcs n).dom
      by rw [hn_eq]; exact hx)
    (show Formula.snce (counterexampleEnum (Nat.unpair n).2).η
        (counterexampleEnum (Nat.unpair n).2).ξ ∈
        (omegaChainVal A h_mcs n).f (counterexampleEnum (Nat.unpair n).2).x
      by rw [hn_eq]; exact h_since)
  obtain ⟨y, hy_dom, hy_lt, hy_η, hy_adj_guard, hy_dom_guard, hy_new_or_id⟩ := key
  refine ⟨y, hy_dom, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hn_eq] at hy_lt; exact hy_lt
  · simp only [hn_eq] at hy_η; exact hy_η
  · intro a b h_adj ha hb
    simp only [hn_eq] at hy_adj_guard
    exact hy_adj_guard a b h_adj ha hb
  · intro w hw hyw hwx
    simp only [hn_eq] at hy_dom_guard
    exact hy_dom_guard w hw hyw hwx
  · exact hy_new_or_id

/--
C4 witness at step n+1.
-/
theorem omega_chain_c4_witness (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    (n : Nat) (x y : Rat) (ξ η : Formula Atom)
    (hx : x ∈ (omegaChainVal A h_mcs n).dom)
    (hy : y ∈ (omegaChainVal A h_mcs n).dom)
    (hxy : x < y)
    (h_neg_until : (Formula.untl η ξ).neg ∈ (omegaChainVal A h_mcs n).f x)
    (h_event : η ∈ (omegaChainVal A h_mcs n).f y)
    (hn_eq : counterexampleEnum (Nat.unpair n).2 = ⟨x, y, ξ, η, .c4_forward⟩) :
    ∃ z ∈ (omegaChainVal A h_mcs (n + 1)).dom,
      x < z ∧ z < y ∧ (¬ξ) ∈ (omegaChainVal A h_mcs (n + 1)).f z := by
  rw [omega_chain_dom_eq_elim, omega_chain_f_eq_elim]
  have key := (omegaChainElimResult A h_mcs n).c4_forward_witness
    (show (counterexampleEnum (Nat.unpair n).2).kind = .c4_forward by rw [hn_eq])
    (show (counterexampleEnum (Nat.unpair n).2).x ∈ (omegaChainVal A h_mcs n).dom
      by rw [hn_eq]; exact hx)
    (show (counterexampleEnum (Nat.unpair n).2).y ∈ (omegaChainVal A h_mcs n).dom
      by rw [hn_eq]; exact hy)
    (show (counterexampleEnum (Nat.unpair n).2).x < (counterexampleEnum (Nat.unpair n).2).y
      by rw [hn_eq]; exact hxy)
    (show (Formula.untl (counterexampleEnum (Nat.unpair n).2).η
        (counterexampleEnum (Nat.unpair n).2).ξ).neg ∈
        (omegaChainVal A h_mcs n).f (counterexampleEnum (Nat.unpair n).2).x
      by rw [hn_eq]; exact h_neg_until)
    (show (counterexampleEnum (Nat.unpair n).2).η ∈
        (omegaChainVal A h_mcs n).f (counterexampleEnum (Nat.unpair n).2).y
      by rw [hn_eq]; exact h_event)
  obtain ⟨z, hz_dom, hxz, hzy, hz_neg⟩ := key
  refine ⟨z, hz_dom, ?_, ?_, ?_⟩
  · simp only [hn_eq] at hxz; exact hxz
  · simp only [hn_eq] at hzy; exact hzy
  · simp only [hn_eq] at hz_neg; exact hz_neg

/--
C4' witness at step n+1 (mirror for Since).
-/
theorem omega_chain_c4'_witness (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    (n : Nat) (x y : Rat) (ξ η : Formula Atom)
    (hx : x ∈ (omegaChainVal A h_mcs n).dom)
    (hy : y ∈ (omegaChainVal A h_mcs n).dom)
    (hyx : y < x)
    (h_neg_since : (Formula.snce η ξ).neg ∈ (omegaChainVal A h_mcs n).f x)
    (h_event : η ∈ (omegaChainVal A h_mcs n).f y)
    (hn_eq : counterexampleEnum (Nat.unpair n).2 = ⟨x, y, ξ, η, .c4_backward⟩) :
    ∃ z ∈ (omegaChainVal A h_mcs (n + 1)).dom,
      y < z ∧ z < x ∧ (¬ξ) ∈ (omegaChainVal A h_mcs (n + 1)).f z := by
  rw [omega_chain_dom_eq_elim, omega_chain_f_eq_elim]
  have key := (omegaChainElimResult A h_mcs n).c4_backward_witness
    (show (counterexampleEnum (Nat.unpair n).2).kind = .c4_backward by rw [hn_eq])
    (show (counterexampleEnum (Nat.unpair n).2).x ∈ (omegaChainVal A h_mcs n).dom
      by rw [hn_eq]; exact hx)
    (show (counterexampleEnum (Nat.unpair n).2).y ∈ (omegaChainVal A h_mcs n).dom
      by rw [hn_eq]; exact hy)
    (show (counterexampleEnum (Nat.unpair n).2).y < (counterexampleEnum (Nat.unpair n).2).x
      by rw [hn_eq]; exact hyx)
    (show (Formula.snce (counterexampleEnum (Nat.unpair n).2).η
        (counterexampleEnum (Nat.unpair n).2).ξ).neg ∈
        (omegaChainVal A h_mcs n).f (counterexampleEnum (Nat.unpair n).2).x
      by rw [hn_eq]; exact h_neg_since)
    (show (counterexampleEnum (Nat.unpair n).2).η ∈
        (omegaChainVal A h_mcs n).f (counterexampleEnum (Nat.unpair n).2).y
      by rw [hn_eq]; exact h_event)
  obtain ⟨z, hz_dom, hyz, hzx, hz_neg⟩ := key
  refine ⟨z, hz_dom, ?_, ?_, ?_⟩
  · simp only [hn_eq] at hyz; exact hyz
  · simp only [hn_eq] at hzx; exact hzx
  · simp only [hn_eq] at hz_neg; exact hz_neg

/-! ## Limit Chronicle

The limit of the omega-chain is defined by taking:
- dom = union of all dom(n)
- f(x) = f_n(x) for any n such that x in dom(n)
- g(x,y) = g_n(x,y) for appropriate n

Since the domains are increasing and f agrees on old points, the limit
is well-defined.
-/

/--
The **limit domain**: union of all domains in the omega-chain.
Note: This is potentially infinite (countable), so we model it as a Set Rat
rather than a Finset Rat.
-/
noncomputable def limitDom (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    :
    Set Rat :=
  { x | ∃ n : Nat, x ∈ (omegaChainVal A h_mcs n).dom }

/--
The **limit point function**: for each x in the limit domain, f(x) is
f_n(x) for the first n such that x in dom(n).
-/
noncomputable def limitF (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    :
    Rat → Set (Formula Atom) :=
  fun x =>
    have : Decidable (∃ n, x ∈ (omegaChainVal A h_mcs n).dom) :=
      Classical.dec _
    if h : ∃ n, x ∈ (omegaChainVal A h_mcs n).dom
    then (omegaChainVal A h_mcs h.choose).f x
    else ∅

/--
The limit f is well-defined: for any n with x in dom(n), f_n(x) equals the
limit value.
-/
theorem limit_f_eq (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    (x : Rat) (n : Nat) (hx : x ∈ (omegaChainVal A h_mcs n).dom) :
    limitF A h_mcs x = (omegaChainVal A h_mcs n).f x := by
  -- Unfold the definition
  unfold limitF
  have h_ex : ∃ m, x ∈ (omegaChainVal A h_mcs m).dom := ⟨n, hx⟩
  simp only [h_ex, dite_true]
  set m := Classical.choose h_ex with hm_def
  have hxm : x ∈ (omegaChainVal A h_mcs m).dom := Classical.choose_spec h_ex
  have h1 := omega_chain_f_agrees_le A h_mcs (Nat.le_max_left m n) x hxm
  have h2 := omega_chain_f_agrees_le A h_mcs (Nat.le_max_right m n) x hx
  rw [← h2, h1]

/--
Every point in the limit domain maps to an MCS.
-/
theorem limit_c0 (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    (x : Rat) (hx : x ∈ limitDom A h_mcs) :
    Temporal.SetMaximalConsistent (limitF A h_mcs x) := by
  obtain ⟨n, hn⟩ := hx
  rw [limit_f_eq A h_mcs x n hn]
  exact omega_chain_c0 A h_mcs n x hn

/--
A in the limit: A = f(0) in the limit chronicle.
-/
theorem limit_f_zero (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    :
    limitF A h_mcs 0 = A := by
  have h0 : (0 : Rat) ∈ (omegaChainVal A h_mcs 0).dom := by
    simp only [omegaChainVal, omegaChain, singletonChronicle]
    exact Finset.mem_singleton.mpr rfl
  rw [limit_f_eq A h_mcs 0 0 h0]
  simp only [omegaChainVal, omegaChain, singletonChronicle]

/--
0 is in the limit domain.
-/
theorem zero_mem_limit_dom (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    :
    (0 : Rat) ∈ limitDom A h_mcs := by
  exact ⟨0, by simp [omegaChainVal, omegaChain, singletonChronicle]⟩

/-! ## C5 Satisfaction in the Limit

The key theorem: the limit chronicle satisfies C5 (every Until obligation
has a witness). The proof uses the surjectivity of the counterexample
enumeration: for any potential C5 counterexample (x, xi, eta), there
exists n such that counterexampleEnum n = (x, 0, xi, eta, c5_forward).
At step n+1, this counterexample is either eliminated (a witness is
inserted) or it was already not a counterexample (a witness already exists).
-/

/--
The limit chronicle satisfies C5: for every x in the limit domain and
every xi U eta in limitF(x), there exists a witness y in the limit domain
with y > x and eta in limitF(y).

The full guard condition (xi at intermediate points) requires the interval
function g, which is handled in the integration phase. Here we prove the
weaker version: a witness y with eta in f(y) exists.
-/
theorem limit_satisfies_c5_weak (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    (x : Rat) (hx : x ∈ limitDom A h_mcs)
    (ξ η : Formula Atom)
    (h_until : (η U ξ) ∈ limitF A h_mcs x) :
    ∃ y ∈ limitDom A h_mcs, x < y ∧ η ∈ limitF A h_mcs y := by
  obtain ⟨n₀, hn₀⟩ := hx
  obtain ⟨n, hn_ge, hn_eq⟩ := counterexample_enum_surjective_above
    ⟨x, 0, ξ, η, .c5_forward⟩ n₀
  have hx_n : x ∈ (omegaChainVal A h_mcs n).dom :=
    omega_chain_dom_mono_le A h_mcs hn_ge hn₀
  have h_until_n : (η U ξ) ∈ (omegaChainVal A h_mcs n).f x := by
    rw [omega_chain_f_agrees_le A h_mcs hn_ge x hn₀]
    rwa [← limit_f_eq A h_mcs x n₀ hn₀]
  obtain ⟨y, hy_dom, hy_lt, hy_η, _, _, _⟩ :=
    omega_chain_c5_witness A h_mcs n x ξ η hx_n h_until_n hn_eq
  exact ⟨y, ⟨n + 1, hy_dom⟩, hy_lt,
    by rw [limit_f_eq A h_mcs y (n + 1) hy_dom]; exact hy_η⟩

/--
Mirror: the limit chronicle satisfies C5' (Since witnesses).
-/
theorem limit_satisfies_c5'_weak (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    (x : Rat) (hx : x ∈ limitDom A h_mcs)
    (ξ η : Formula Atom)
    (h_since : (η S ξ) ∈ limitF A h_mcs x) :
    ∃ y ∈ limitDom A h_mcs, y < x ∧ η ∈ limitF A h_mcs y := by
  obtain ⟨n₀, hn₀⟩ := hx
  obtain ⟨n, hn_ge, hn_eq⟩ := counterexample_enum_surjective_above
    ⟨x, 0, ξ, η, .c5_backward⟩ n₀
  have hx_n : x ∈ (omegaChainVal A h_mcs n).dom :=
    omega_chain_dom_mono_le A h_mcs hn_ge hn₀
  have h_since_n : (η S ξ) ∈ (omegaChainVal A h_mcs n).f x := by
    rw [omega_chain_f_agrees_le A h_mcs hn_ge x hn₀]
    rwa [← limit_f_eq A h_mcs x n₀ hn₀]
  obtain ⟨y, hy_dom, hy_lt, hy_η, _, _, _⟩ :=
    omega_chain_c5'_witness A h_mcs n x ξ η hx_n h_since_n hn_eq
  exact ⟨y, ⟨n + 1, hy_dom⟩, hy_lt,
    by rw [limit_f_eq A h_mcs y (n + 1) hy_dom]; exact hy_η⟩

/-! ## F/P Resolution in the Limit

Key derived properties: F(phi) and P(phi) formulas in the limit domain
are resolved by witnesses, using BX12 to convert F to Until and then
applying C5_weak.
-/

/--
F-resolution for the limit: F(phi) in limitF(x) implies there exists
y > x in limitDom with phi in limitF(y).

Proof: F(phi) in limitF(x) -> (top U phi) in limitF(x) by BX12.
Then limit_satisfies_c5_weak gives y > x with phi in limitF(y).
-/
theorem limit_F_resolution (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    (x : Rat) (hx : x ∈ limitDom A h_mcs)
    (φ : Formula Atom)
    (h_F : (𝐅φ) ∈ limitF A h_mcs x) :
    ∃ y ∈ limitDom A h_mcs, x < y ∧ φ ∈ limitF A h_mcs y := by
  have h_mcs_x := limit_c0 A h_mcs x hx
  have h_bx12 : DerivationTree FrameClass.Base [] ((Formula.someFuture φ).imp
      (Formula.untl φ (Formula.bot.imp Formula.bot))) :=
    DerivationTree.axiom [] _ (Axiom.F_until_equiv φ) trivial
  have h_until : Formula.untl φ (Formula.bot.imp Formula.bot) ∈ limitF A h_mcs x :=
    temporal_implication_property h_mcs_x
      (theoremInMcs h_mcs_x h_bx12) h_F
  exact limit_satisfies_c5_weak A h_mcs x hx _ φ h_until

/--
P-resolution for the limit: P(phi) in limitF(x) implies there exists
y < x in limitDom with phi in limitF(y).

Proof: P(phi) in limitF(x) -> (top S phi) in limitF(x) by BX12'.
Then limit_satisfies_c5'_weak gives y < x with phi in limitF(y).
-/
theorem limit_P_resolution (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    (x : Rat) (hx : x ∈ limitDom A h_mcs)
    (φ : Formula Atom)
    (h_P : (𝐏φ) ∈ limitF A h_mcs x) :
    ∃ y ∈ limitDom A h_mcs, y < x ∧ φ ∈ limitF A h_mcs y := by
  have h_mcs_x := limit_c0 A h_mcs x hx
  have h_bx12' : DerivationTree FrameClass.Base [] ((Formula.somePast φ).imp
      (Formula.snce φ (Formula.bot.imp Formula.bot))) :=
    DerivationTree.axiom [] _ (Axiom.P_since_equiv φ) trivial
  have h_since : Formula.snce φ (Formula.bot.imp Formula.bot) ∈ limitF A h_mcs x :=
    temporal_implication_property h_mcs_x
      (theoremInMcs h_mcs_x h_bx12') h_P
  exact limit_satisfies_c5'_weak A h_mcs x hx _ φ h_since

/-! ## C4 Satisfaction in the Limit

The limit chronicle satisfies C4: for any x < y in limitDom, if
neg(untl(gamma, delta)) in limitF(x) and delta in limitF(y), then
there exists z in limitDom with x < z < y and gamma.neg in limitF(z).

The proof parallels limit_satisfies_c5_weak: use surjectivity of the
counterexample enumeration to find a step where the counterexample is
processed. At that step, either the witness already exists or one is
inserted by eliminatePotentialCounterexample (C4 case).
-/

/--
The limit chronicle satisfies C4 (generalized Burgess C4a): for all x < y in
limitDom, if neg(untl(ξ,η)) in limitF(x) and η in limitF(y), then there
exists z in limitDom with x < z < y and ξ.neg in limitF(z).
-/
theorem limit_satisfies_c4 (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    (x y : Rat) (hx : x ∈ limitDom A h_mcs) (hy : y ∈ limitDom A h_mcs)
    (hxy : x < y) (ξ η : Formula Atom)
    (h_neg_until : (Formula.untl η ξ).neg ∈ limitF A h_mcs x)
    (h_event : η ∈ limitF A h_mcs y) :
    ∃ z ∈ limitDom A h_mcs, x < z ∧ z < y ∧ (¬ξ) ∈ limitF A h_mcs z := by
  obtain ⟨nx, hnx⟩ := hx
  obtain ⟨ny, hny⟩ := hy
  set n₀ := max nx ny with hn₀_def
  have hx_n₀ : x ∈ (omegaChainVal A h_mcs n₀).dom :=
    omega_chain_dom_mono_le A h_mcs (le_max_left nx ny) hnx
  have hy_n₀ : y ∈ (omegaChainVal A h_mcs n₀).dom :=
    omega_chain_dom_mono_le A h_mcs (le_max_right nx ny) hny
  obtain ⟨n, hn_ge, hn_eq⟩ := counterexample_enum_surjective_above
    ⟨x, y, ξ, η, .c4_forward⟩ n₀
  have hx_n : x ∈ (omegaChainVal A h_mcs n).dom :=
    omega_chain_dom_mono_le A h_mcs hn_ge hx_n₀
  have hy_n : y ∈ (omegaChainVal A h_mcs n).dom :=
    omega_chain_dom_mono_le A h_mcs hn_ge hy_n₀
  have h_nu_n : (Formula.untl η ξ).neg ∈ (omegaChainVal A h_mcs n).f x := by
    rw [omega_chain_f_agrees_le A h_mcs hn_ge x hx_n₀]
    rw [omega_chain_f_agrees_le A h_mcs (le_max_left nx ny) x hnx]
    rwa [← limit_f_eq A h_mcs x nx hnx]
  have h_ev_n : η ∈ (omegaChainVal A h_mcs n).f y := by
    rw [omega_chain_f_agrees_le A h_mcs hn_ge y hy_n₀]
    rw [omega_chain_f_agrees_le A h_mcs (le_max_right nx ny) y hny]
    rwa [← limit_f_eq A h_mcs y ny hny]
  obtain ⟨z, hz_dom, hxz, hzy, hz_neg⟩ :=
    omega_chain_c4_witness A h_mcs n x y ξ η hx_n hy_n hxy h_nu_n h_ev_n hn_eq
  exact ⟨z, ⟨n + 1, hz_dom⟩, hxz, hzy,
    by rw [limit_f_eq A h_mcs z (n + 1) hz_dom]; exact hz_neg⟩

/--
Mirror: the limit chronicle satisfies C4' (Since).
-/
theorem limit_satisfies_c4' (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    (x y : Rat) (hx : x ∈ limitDom A h_mcs) (hy : y ∈ limitDom A h_mcs)
    (hyx : y < x) (ξ η : Formula Atom)
    (h_neg_since : (Formula.snce η ξ).neg ∈ limitF A h_mcs x)
    (h_event : η ∈ limitF A h_mcs y) :
    ∃ z ∈ limitDom A h_mcs, y < z ∧ z < x ∧ (¬ξ) ∈ limitF A h_mcs z := by
  obtain ⟨nx, hnx⟩ := hx
  obtain ⟨ny, hny⟩ := hy
  set n₀ := max nx ny with hn₀_def
  have hx_n₀ : x ∈ (omegaChainVal A h_mcs n₀).dom :=
    omega_chain_dom_mono_le A h_mcs (le_max_left nx ny) hnx
  have hy_n₀ : y ∈ (omegaChainVal A h_mcs n₀).dom :=
    omega_chain_dom_mono_le A h_mcs (le_max_right nx ny) hny
  obtain ⟨n, hn_ge, hn_eq⟩ := counterexample_enum_surjective_above
    ⟨x, y, ξ, η, .c4_backward⟩ n₀
  have hx_n : x ∈ (omegaChainVal A h_mcs n).dom :=
    omega_chain_dom_mono_le A h_mcs hn_ge hx_n₀
  have hy_n : y ∈ (omegaChainVal A h_mcs n).dom :=
    omega_chain_dom_mono_le A h_mcs hn_ge hy_n₀
  have h_ns_n : (Formula.snce η ξ).neg ∈ (omegaChainVal A h_mcs n).f x := by
    rw [omega_chain_f_agrees_le A h_mcs hn_ge x hx_n₀]
    rw [omega_chain_f_agrees_le A h_mcs (le_max_left nx ny) x hnx]
    rwa [← limit_f_eq A h_mcs x nx hnx]
  have h_ev_n : η ∈ (omegaChainVal A h_mcs n).f y := by
    rw [omega_chain_f_agrees_le A h_mcs hn_ge y hy_n₀]
    rw [omega_chain_f_agrees_le A h_mcs (le_max_right nx ny) y hny]
    rwa [← limit_f_eq A h_mcs y ny hny]
  obtain ⟨z, hz_dom, hyz, hzx, hz_neg⟩ :=
    omega_chain_c4'_witness A h_mcs n x y ξ η hx_n hy_n hyx h_ns_n h_ev_n hn_eq
  exact ⟨z, ⟨n + 1, hz_dom⟩, hyz, hzx,
    by rw [limit_f_eq A h_mcs z (n + 1) hz_dom]; exact hz_neg⟩

/-! ## Limit Interval Function

The limit interval function is defined by the C3 identity for the dense limit
domain. Since the limit domain is dense (no adjacent pairs), the interval function
is uniquely determined by the point function:

  limitG(x,z) = {phi | forall y in limitDom, x < y -> y < z -> phi in limitF(y)}

This is the set of formulas that hold at ALL intermediate points between x and z.
It automatically satisfies C3 by construction and gives limitG(x,z) subset limitF(y)
for any y between x and z.
-/

/--
The **limit interval function**: for each pair (x, z) of rationals,
the set of formulas in limitF(y) for ALL y strictly between x and z
in the limit domain.

This definition is the C3-derived g: it captures the formulas that hold at
every intermediate point. For the dense limit domain, this is the unique
definition satisfying C3 (since C3 forces g(x,z) subset f(y) for all y between).
-/
noncomputable def limitG (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    :
    Rat → Rat → Set (Formula Atom) :=
  fun x z => { φ | ∀ y ∈ limitDom A h_mcs, x < y → y < z → φ ∈ limitF A h_mcs y }

/--
C3 at the limit: for all x < y < z in limitDom,
`limitG(x,z) = limitG(x,y) inter limitF(y) inter limitG(y,z)`.

Proof: Both sides equal {phi | forall w in limitDom, x < w < z -> phi in limitF(w)}.
The LHS is this by definition. The RHS breaks the interval (x,z) at y:
phi in g(x,y) iff phi in f(w) for all w in (x,y),
phi in f(y) iff phi in f(y),
phi in g(y,z) iff phi in f(w) for all w in (y,z).
Together: phi in f(w) for all w in (x,z) in limitDom.
-/
theorem limit_c3 (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    (x y z : Rat)
    (hx : x ∈ limitDom A h_mcs) (hy : y ∈ limitDom A h_mcs)
    (hz : z ∈ limitDom A h_mcs) (hxy : x < y) (hyz : y < z) :
    limitG A h_mcs x z = limitG A h_mcs x y ∩ limitF A h_mcs y ∩ limitG A h_mcs y z := by
  ext φ
  simp only [Set.mem_inter_iff, limitG, Set.mem_setOf_eq]
  constructor
  · intro h
    exact ⟨⟨fun w hw hxw hwy => h w hw hxw (lt_trans hwy hyz),
            h y hy hxy hyz⟩,
           fun w hw hyw hwz => h w hw (lt_trans hxy hyw) hwz⟩
  · intro ⟨⟨h_xy, h_y⟩, h_yz⟩ w hw hxw hwz
    rcases lt_trichotomy w y with hwl | rfl | hwg
    · exact h_xy w hw hxw hwl
    · exact h_y
    · exact h_yz w hw hwg hwz

/--
Key consequence of C3 at the limit: limitG(x,z) subset limitF(y) for x < y < z.

Since limitG(x,z) = limitG(x,y) inter limitF(y) inter limitG(y,z), the
intersection is contained in limitF(y). This is the critical property for
Phase 5B (the guard phi propagates to intermediate points).
-/
theorem limit_c3_interval_subset_point (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    (x y z : Rat)
    (hx : x ∈ limitDom A h_mcs) (hy : y ∈ limitDom A h_mcs)
    (hz : z ∈ limitDom A h_mcs) (hxy : x < y) (hyz : y < z) :
    limitG A h_mcs x z ⊆ limitF A h_mcs y := by
  have h_eq := limit_c3 A h_mcs x y z hx hy hz hxy hyz
  intro φ hφ
  rw [h_eq] at hφ
  exact hφ.1.2

/--
C3 at the limit: limitG(x,z) subset limitG(x,y) for x < y < z.
-/
theorem limit_c3_interval_subset_left (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    (x y z : Rat)
    (hx : x ∈ limitDom A h_mcs) (hy : y ∈ limitDom A h_mcs)
    (hz : z ∈ limitDom A h_mcs) (hxy : x < y) (hyz : y < z) :
    limitG A h_mcs x z ⊆ limitG A h_mcs x y := by
  have h_eq := limit_c3 A h_mcs x y z hx hy hz hxy hyz
  intro φ hφ
  rw [h_eq] at hφ
  exact hφ.1.1

/--
C3 at the limit: limitG(x,z) subset limitG(y,z) for x < y < z.
-/
theorem limit_c3_interval_subset_right (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    (x y z : Rat)
    (hx : x ∈ limitDom A h_mcs) (hy : y ∈ limitDom A h_mcs)
    (hz : z ∈ limitDom A h_mcs) (hxy : x < y) (hyz : y < z) :
    limitG A h_mcs x z ⊆ limitG A h_mcs y z := by
  have h_eq := limit_c3 A h_mcs x y z hx hy hz hxy hyz
  intro φ hφ
  rw [h_eq] at hφ
  exact hφ.2

/-! ## Forward_G / Backward_H for Domain Points

The key coherence properties for the truth lemma (ParametricTruthLemma.lean).
The FMCS structure requires forward_G as a field (it IS an input to the
truth lemma, not a consequence).

**Proof** (plan v12, Phase 4): Uses the generalized C4 + C0 argument.

G(φ) = allFuture(φ). In an MCS, G(φ) implies G(φ^{nn}) (by DNI + temporal
necessitation + K distribution). Then F(neg φ) = neg(G(φ^{nn})) ∉ MCS. By
BX10 contrapositive, (⊤ U neg φ) ∉ MCS. By MCS negation completeness,
neg(⊤ U neg φ) ∈ MCS. Applying generalized C4 (for ALL pairs x < y, not just
adjacent): neg(untl(⊤, neg φ)) ∈ f(x) and neg φ ∈ f(y) gives ⊤.neg ∈ f(z)
for some z. Since ⊤ is a theorem, ⊤ and ⊤.neg both in f(z) contradicts C0.

The prior obstruction (plan v11) was that C4 only applied to adjacent pairs,
making it vacuously true at the dense limit. Plan v12 Phase 1 fixed this by
generalizing C4 to all pairs x < y (matching Burgess 1982 C4a).
-/

/--
Forward_G for domain points: G(φ) ∈ limitF(x) and x < y implies φ ∈ limitF(y).

**Proof**: By contradiction using generalized C4 + C0. See section docstring.
-/
theorem limit_forward_G (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    (x y : Rat) (hx : x ∈ limitDom A h_mcs) (hy : y ∈ limitDom A h_mcs)
    (hxy : x < y) (φ : Formula Atom) (h_G : (𝐆φ) ∈ limitF A h_mcs x) :
    φ ∈ limitF A h_mcs y := by
  by_contra h_not
  have h_mcs_x := limit_c0 A h_mcs x hx
  have h_mcs_y := limit_c0 A h_mcs y hy
  have h_neg_phi : (¬φ) ∈ limitF A h_mcs y := by
    rcases temporal_negation_complete h_mcs_y φ with h | h
    · exact absurd h h_not
    · exact h
  -- Step 1: G(φ) ∈ f(x) implies G(φ^{nn}) ∈ f(x) by DNI + temporal necessitation + K
  have h_dni : DerivationTree FrameClass.Base [] (φ.imp φ.neg.neg) :=
    dni φ
  have h_G_dni : DerivationTree FrameClass.Base [] (Formula.allFuture (φ.imp φ.neg.neg)) :=
    DerivationTree.temporal_necessitation _ h_dni
  have h_G_dist : DerivationTree FrameClass.Base [] ((Formula.allFuture (φ.imp φ.neg.neg)).imp
      (Formula.allFuture φ |>.imp (Formula.allFuture φ.neg.neg))) :=
    tempKDistDerived φ φ.neg.neg
  have h_G_nn : Formula.allFuture φ.neg.neg ∈ limitF A h_mcs x := by
    have h1 := theoremInMcs h_mcs_x h_G_dni
    have h2 := theoremInMcs h_mcs_x h_G_dist
    have h3 := temporal_implication_property h_mcs_x h2 h1
    exact temporal_implication_property h_mcs_x h3 h_G
  have h_F_not : (𝐅(¬φ)) ∉ limitF A h_mcs x := by
    intro h_abs
    exact someFuture_allFuture_neg_absurd h_mcs_x φ.neg h_abs h_G_nn
  set top := Formula.bot.imp Formula.bot with htop_def
  have h_bx10 : DerivationTree FrameClass.Base [] ((Formula.untl φ.neg top).imp (Formula.someFuture φ.neg)) :=
    DerivationTree.axiom [] _ (Axiom.until_F top φ.neg) trivial
  have h_until_not : Formula.untl φ.neg top ∉ limitF A h_mcs x := by
    intro h_in
    exact h_F_not (temporal_implication_property h_mcs_x
      (theoremInMcs h_mcs_x h_bx10) h_in)
  have h_neg_until : (Formula.untl φ.neg top).neg ∈ limitF A h_mcs x := by
    rcases temporal_negation_complete h_mcs_x (Formula.untl φ.neg top) with h | h
    · exact absurd h h_until_not
    · exact h
  obtain ⟨z, hz_dom, _hxz, _hzy, h_top_neg⟩ :=
    limit_satisfies_c4 A h_mcs x y hx hy hxy top φ.neg h_neg_until h_neg_phi
  have h_mcs_z := limit_c0 A h_mcs z hz_dom
  have h_top_in : top ∈ limitF A h_mcs z := by
    apply theoremInMcs h_mcs_z
    exact DerivationTree.axiom [] _ (Axiom.efq Formula.bot) trivial
  exact absurd h_top_in (mcs_not_mem_of_neg h_mcs_z h_top_neg)

/--
Backward_H for domain points (dual of forward_G).
H(φ) ∈ limitF(x) and y < x implies φ ∈ limitF(y).

**Proof**: Mirror of forward_G using generalized C4' + C0. Uses BX10' (since_P)
and past temporal necessitation.
-/
theorem limit_backward_H (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    (x y : Rat) (hx : x ∈ limitDom A h_mcs) (hy : y ∈ limitDom A h_mcs)
    (hyx : y < x) (φ : Formula Atom) (h_H : (𝐇φ) ∈ limitF A h_mcs x) :
    φ ∈ limitF A h_mcs y := by
  by_contra h_not
  have h_mcs_x := limit_c0 A h_mcs x hx
  have h_mcs_y := limit_c0 A h_mcs y hy
  have h_neg_phi : (¬φ) ∈ limitF A h_mcs y := by
    rcases temporal_negation_complete h_mcs_y φ with h | h
    · exact absurd h h_not
    · exact h
  -- H(φ) → H(φ^{nn}) by DNI + past necessitation + past K
  have h_dni : DerivationTree FrameClass.Base [] (φ.imp φ.neg.neg) :=
    dni φ
  have h_H_dni : DerivationTree FrameClass.Base [] (Formula.allPast (φ.imp φ.neg.neg)) :=
    pastNecessitation _ h_dni
  have h_H_dist : DerivationTree FrameClass.Base [] ((Formula.allPast (φ.imp φ.neg.neg)).imp
      (Formula.allPast φ |>.imp (Formula.allPast φ.neg.neg))) :=
    pastKDist φ φ.neg.neg
  have h_H_nn : Formula.allPast φ.neg.neg ∈ limitF A h_mcs x := by
    have h1 := theoremInMcs h_mcs_x h_H_dni
    have h2 := theoremInMcs h_mcs_x h_H_dist
    have h3 := temporal_implication_property h_mcs_x h2 h1
    exact temporal_implication_property h_mcs_x h3 h_H
  have h_P_not : (𝐏(¬φ)) ∉ limitF A h_mcs x := by
    intro h_abs
    exact somePast_allPast_neg_absurd h_mcs_x φ.neg h_abs h_H_nn
  set top := Formula.bot.imp Formula.bot with htop_def
  have h_bx10' : DerivationTree FrameClass.Base [] ((Formula.snce φ.neg top).imp (Formula.somePast φ.neg)) :=
    DerivationTree.axiom [] _ (Axiom.since_P top φ.neg) trivial
  have h_since_not : Formula.snce φ.neg top ∉ limitF A h_mcs x := by
    intro h_in
    exact h_P_not (temporal_implication_property h_mcs_x
      (theoremInMcs h_mcs_x h_bx10') h_in)
  have h_neg_since : (Formula.snce φ.neg top).neg ∈ limitF A h_mcs x := by
    rcases temporal_negation_complete h_mcs_x (Formula.snce φ.neg top) with h | h
    · exact absurd h h_since_not
    · exact h
  obtain ⟨z, hz_dom, _hyz, _hzx, h_top_neg⟩ :=
    limit_satisfies_c4' A h_mcs x y hx hy hyx top φ.neg h_neg_since h_neg_phi
  have h_mcs_z := limit_c0 A h_mcs z hz_dom
  have h_top_in : top ∈ limitF A h_mcs z := by
    apply theoremInMcs h_mcs_z
    exact DerivationTree.axiom [] _ (Axiom.efq Formula.bot) trivial
  exact absurd h_top_in (mcs_not_mem_of_neg h_mcs_z h_top_neg)

/-! ## Claim 2.11: Truth Claim

The truth claim states that the valuation V(alpha) = {x : alpha in f(x)}
satisfies the bimodal truth conditions for all formulas, by induction
on formula complexity:

- Atom: V(p) = {x : p in f(x)} by definition
- Bot: V(bot) = empty (since f(x) is consistent for all x)
- Imp: V(phi -> psi) = V(phi)^c union V(psi) (by MCS imp property)
- Box: V(box phi) = {x : forall y ~ x, phi in f(y)} (by MCS box property)
- G: V(G phi) = {x : forall y > x, phi in f(y)} (by gContent and C3)
- H: V(H phi) = {x : forall y < x, phi in f(y)} (by hContent and C3')
- Until: V(phi U psi) = {x : exists y > x, psi(y) and forall z in (x,y), phi(z)}
  Forward direction: from phi U psi in f(x), get witness y by C5
  Backward direction: from the semantic condition, phi U psi in f(x) by C5-completeness
- Since: Mirror of Until
-/

/-! ## Chronicle Model Construction

Package the limit chronicle into a structure suitable for the completeness
theorem. The key output is: given any MCS A, there exists a model where
A is satisfied (at point 0).
-/

/--
Given an MCS A, the limit chronicle construction produces:
1. A set of points (limitDom) containing 0
2. A point function (limitF) mapping each point to an MCS
3. The property that A = limitF(0)
4. C5/C5' satisfaction (Until/Since witnesses exist)

This is the key input for the completeness theorem: any consistent formula
belongs to some MCS A, and the chronicle model witnesses its satisfiability.
-/
theorem chronicle_model_exists (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    :
    ∃ (D : Set Rat) (f : Rat → Set (Formula Atom)),
      (0 : Rat) ∈ D ∧
      f 0 = A ∧
      (∀ x ∈ D, Temporal.SetMaximalConsistent (f x)) ∧
      (∀ x ∈ D, ∀ ξ η : Formula Atom,
        (η U ξ) ∈ f x →
        ∃ y ∈ D, x < y ∧ η ∈ f y) ∧
      (∀ x ∈ D, ∀ ξ η : Formula Atom,
        (η S ξ) ∈ f x →
        ∃ y ∈ D, y < x ∧ η ∈ f y) :=
  ⟨limitDom A h_mcs,
   limitF A h_mcs,
   zero_mem_limit_dom A h_mcs,
   limit_f_zero A h_mcs,
   limit_c0 A h_mcs,
   fun x hx ξ η h => limit_satisfies_c5_weak A h_mcs x hx ξ η h,
   fun x hx ξ η h => limit_satisfies_c5'_weak A h_mcs x hx ξ η h⟩

/-! ## Omega Chain Single-Point Insertion

Each elimination step inserts at most one new domain point.
-/

theorem omega_chain_dom_new_unique (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    (n : Nat)
    (u v : Rat)
    (hu : u ∈ (omegaChainVal A h_mcs (n + 1)).dom)
    (hu_not : u ∉ (omegaChainVal A h_mcs n).dom)
    (hv : v ∈ (omegaChainVal A h_mcs (n + 1)).dom)
    (hv_not : v ∉ (omegaChainVal A h_mcs n).dom) :
    u = v := by
  have hu' : u ∈ (omegaChainElimResult A h_mcs n).val.dom := by
    rw [← omega_chain_dom_eq_elim]; exact hu
  have hv' : v ∈ (omegaChainElimResult A h_mcs n).val.dom := by
    rw [← omega_chain_dom_eq_elim]; exact hv
  exact (omegaChainElimResult A h_mcs n).dom_new_unique u v hu' hu_not hv' hv_not

/-- When the C5 forward counterexample at step n is already resolved (a witness exists
in dom_n with proper guard), the elimination is identity: dom_{n+1} ⊆ dom_n. -/
theorem omega_chain_c5_forward_resolved_no_new (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    (n : Nat) (x : Rat) (ξ η : Formula Atom)
    (hn_eq : counterexampleEnum (Nat.unpair n).2 = ⟨x, 0, ξ, η, .c5_forward⟩)
    (hx : x ∈ (omegaChainVal A h_mcs n).dom)
    (h_until : (η U ξ) ∈ (omegaChainVal A h_mcs n).f x)
    (h_wit : ∃ y ∈ (omegaChainVal A h_mcs n).dom, x < y ∧
      η ∈ (omegaChainVal A h_mcs n).f y ∧
      (∀ a b, Adjacent (omegaChainVal A h_mcs n).dom a b →
        x ≤ a → b ≤ y → ξ ∈ (omegaChainVal A h_mcs n).g a b) ∧
      (∀ w ∈ (omegaChainVal A h_mcs n).dom,
        x < w → w < y → ξ ∈ (omegaChainVal A h_mcs n).f w))
    (u : Rat) (hu : u ∈ (omegaChainVal A h_mcs (n + 1)).dom) :
    u ∈ (omegaChainVal A h_mcs n).dom := by
  have hu' : u ∈ (omegaChainElimResult A h_mcs n).val.dom := by
    rw [← omega_chain_dom_eq_elim]; exact hu
  exact (omegaChainElimResult A h_mcs n).c5_forward_resolved_no_new
    (show (counterexampleEnum (Nat.unpair n).2).kind = .c5_forward by rw [hn_eq])
    (show (counterexampleEnum (Nat.unpair n).2).x ∈ _ by rw [hn_eq]; exact hx)
    (show Formula.untl (counterexampleEnum (Nat.unpair n).2).η
        (counterexampleEnum (Nat.unpair n).2).ξ ∈ _ by rw [hn_eq]; exact h_until)
    (by rw [hn_eq]; exact h_wit) u hu'

/-- Mirror: when the C5 backward counterexample at step n is already resolved. -/
theorem omega_chain_c5_backward_resolved_no_new (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    (n : Nat) (x : Rat) (ξ η : Formula Atom)
    (hn_eq : counterexampleEnum (Nat.unpair n).2 = ⟨x, 0, ξ, η, .c5_backward⟩)
    (hx : x ∈ (omegaChainVal A h_mcs n).dom)
    (h_since : (η S ξ) ∈ (omegaChainVal A h_mcs n).f x)
    (h_wit : ∃ y ∈ (omegaChainVal A h_mcs n).dom, y < x ∧
      η ∈ (omegaChainVal A h_mcs n).f y ∧
      (∀ a b, Adjacent (omegaChainVal A h_mcs n).dom a b →
        y ≤ a → b ≤ x → ξ ∈ (omegaChainVal A h_mcs n).g a b) ∧
      (∀ w ∈ (omegaChainVal A h_mcs n).dom,
        y < w → w < x → ξ ∈ (omegaChainVal A h_mcs n).f w))
    (u : Rat) (hu : u ∈ (omegaChainVal A h_mcs (n + 1)).dom) :
    u ∈ (omegaChainVal A h_mcs n).dom := by
  have hu' : u ∈ (omegaChainElimResult A h_mcs n).val.dom := by
    rw [← omega_chain_dom_eq_elim]; exact hu
  exact (omegaChainElimResult A h_mcs n).c5_backward_resolved_no_new
    (show (counterexampleEnum (Nat.unpair n).2).kind = .c5_backward by rw [hn_eq])
    (show (counterexampleEnum (Nat.unpair n).2).x ∈ _ by rw [hn_eq]; exact hx)
    (show Formula.snce (counterexampleEnum (Nat.unpair n).2).η
        (counterexampleEnum (Nat.unpair n).2).ξ ∈ _ by rw [hn_eq]; exact h_since)
    (by rw [hn_eq]; exact h_wit) u hu'

/-! ## Omega Chain g-value Lifting

Lift EliminationResult.g_sub_f_insert and g_sub_g_new to the omega chain level.
-/

theorem omega_chain_g_sub_f_insert (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    (n : Nat)
    (a b : Rat) (h_adj : Adjacent (omegaChainVal A h_mcs n).dom a b)
    (w : Rat) (hw : w ∈ (omegaChainVal A h_mcs (n + 1)).dom)
    (hw_not : w ∉ (omegaChainVal A h_mcs n).dom)
    (haw : a < w) (hwb : w < b) :
    (omegaChainVal A h_mcs n).g a b ⊆
    (omegaChainVal A h_mcs (n + 1)).f w := by
  have hw' : w ∈ (omegaChainElimResult A h_mcs n).val.dom := by
    rw [← omega_chain_dom_eq_elim]; exact hw
  intro φ hφ
  have := (omegaChainElimResult A h_mcs n).g_sub_f_insert a b h_adj w hw' hw_not haw hwb hφ
  rw [omega_chain_f_eq_elim]; exact this

theorem omega_chain_g_sub_g_new (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    (n : Nat)
    (a b : Rat) (h_adj : Adjacent (omegaChainVal A h_mcs n).dom a b)
    (w : Rat) (hw : w ∈ (omegaChainVal A h_mcs (n + 1)).dom)
    (hw_not : w ∉ (omegaChainVal A h_mcs n).dom)
    (haw : a < w) (hwb : w < b) :
    (omegaChainVal A h_mcs n).g a b ⊆
    (omegaChainVal A h_mcs (n + 1)).g a w ∧
    (omegaChainVal A h_mcs n).g a b ⊆
    (omegaChainVal A h_mcs (n + 1)).g w b := by
  have hw' : w ∈ (omegaChainElimResult A h_mcs n).val.dom := by
    rw [← omega_chain_dom_eq_elim]; exact hw
  have key := (omegaChainElimResult A h_mcs n).g_sub_g_new a b h_adj w hw' hw_not haw hwb
  constructor
  · intro φ hφ
    have := key.1 hφ
    rw [omega_chain_g_eq_elim]; exact this
  · intro φ hφ
    have := key.2 hφ
    rw [omega_chain_g_eq_elim]; exact this

/-! ## Adjacent Pair g-value Propagation to Limit f-values

The key bridge between finite-stage g-values and limit f-values:
if φ ∈ g_k(a,b) for adjacent (a,b) in dom(k), then φ ∈ limitF(w)
for any w ∈ limitDom with a < w < b.

Proof: By strong induction on the first stage m where w enters the domain.
At stage m, w was inserted between adjacent (a',b') in dom(m-1) with a' < w < b'.
By g_sub_f_insert, g_{m-1}(a',b') ⊆ f_m(w). We show g_k(a,b) ⊆ g_{m-1}(a',b')
by tracking g-value propagation through insertions via g_sub_g_new.
-/

theorem adj_g_mem_f_at_stage (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A) :
    ∀ (d : Nat) (n : Nat) (a b : Rat),
      Adjacent (omegaChainVal A h_mcs n).dom a b →
      ∀ φ, φ ∈ (omegaChainVal A h_mcs n).g a b →
      ∀ (w : Rat), w ∈ (omegaChainVal A h_mcs (n + d)).dom →
        a < w → w < b → φ ∈ (omegaChainVal A h_mcs (n + d)).f w := by
  intro d
  induction d with
  | zero =>
    intro n a b h_adj _ _ w hw haw hwb
    exact absurd hw (h_adj.2.2.2 w · ⟨haw, hwb⟩)
  | succ d ih =>
    intro n a b h_adj φ hφ w hw haw hwb
    rw [show n + (d + 1) = (n + 1) + d from by omega] at hw ⊢
    by_cases hz_ex : ∃ z, z ∈ (omegaChainVal A h_mcs (n + 1)).dom ∧
        z ∉ (omegaChainVal A h_mcs n).dom ∧ a < z ∧ z < b
    · obtain ⟨z, hz_in, hz_not, haz, hzb⟩ := hz_ex
      have h_gsub := omega_chain_g_sub_g_new A h_mcs n a b h_adj z hz_in hz_not haz hzb
      by_cases hwz : w = z
      · subst hwz
        have hφ_fw : φ ∈ (omegaChainVal A h_mcs (n + 1)).f w :=
          omega_chain_g_sub_f_insert A h_mcs n a b h_adj w hz_in hz_not haw hwb hφ
        have hw_n1 : w ∈ (omegaChainVal A h_mcs (n + 1)).dom := hz_in
        rw [omega_chain_f_agrees_le A h_mcs (by omega : n + 1 ≤ (n + 1) + d) w hw_n1]
        exact hφ_fw
      · rcases lt_or_gt_of_ne hwz with hwz_lt | hwz_gt
        · have h_adj_az : Adjacent (omegaChainVal A h_mcs (n + 1)).dom a z := by
            refine ⟨omega_chain_dom_mono A h_mcs n h_adj.1, hz_in, haz, ?_⟩
            intro u hu ⟨hau, huz⟩
            have hu_old : u ∈ (omegaChainVal A h_mcs n).dom := by
              by_contra hu_not
              have := omega_chain_dom_new_unique A h_mcs n u z hu hu_not hz_in hz_not
              linarith
            exact h_adj.2.2.2 u hu_old ⟨hau, lt_trans huz hzb⟩
          exact ih (n + 1) a z h_adj_az φ (h_gsub.1 hφ) w hw haw hwz_lt
        · have h_adj_zb : Adjacent (omegaChainVal A h_mcs (n + 1)).dom z b := by
            refine ⟨hz_in, omega_chain_dom_mono A h_mcs n h_adj.2.1, hzb, ?_⟩
            intro u hu ⟨hzu, hub⟩
            have hu_old : u ∈ (omegaChainVal A h_mcs n).dom := by
              by_contra hu_not
              have := omega_chain_dom_new_unique A h_mcs n u z hu hu_not hz_in hz_not
              linarith
            exact h_adj.2.2.2 u hu_old ⟨lt_trans haz hzu, hub⟩
          exact ih (n + 1) z b h_adj_zb φ (h_gsub.2 hφ) w hw hwz_gt hwb
    · push_neg at hz_ex
      have h_adj_n1 : Adjacent (omegaChainVal A h_mcs (n + 1)).dom a b := by
        refine ⟨omega_chain_dom_mono A h_mcs n h_adj.1,
               omega_chain_dom_mono A h_mcs n h_adj.2.1,
               h_adj.2.2.1, ?_⟩
        intro u hu ⟨hau, hub⟩
        have hu_old : u ∈ (omegaChainVal A h_mcs n).dom := by
          by_contra hu_not
          exact absurd hub (not_lt.mpr (hz_ex u hu hu_not hau))
        exact h_adj.2.2.2 u hu_old ⟨hau, hub⟩
      have hφ_n1 : φ ∈ (omegaChainVal A h_mcs (n + 1)).g a b := by
        rw [omega_chain_g_agrees A h_mcs n a b h_adj.1 h_adj.2.1]; exact hφ
      exact ih (n + 1) a b h_adj_n1 φ hφ_n1 w hw haw hwb

theorem adj_g_mem_limit_f (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    (k : Nat)
    (a b : Rat) (h_adj : Adjacent (omegaChainVal A h_mcs k).dom a b)
    (φ : Formula Atom) (hφ : φ ∈ (omegaChainVal A h_mcs k).g a b)
    (w : Rat) (hw : w ∈ limitDom A h_mcs) (haw : a < w) (hwb : w < b) :
    φ ∈ limitF A h_mcs w := by
  obtain ⟨m, hm⟩ := hw
  have hkm : k ≤ m := by
    by_contra h; push_neg at h
    exact h_adj.2.2.2 w (omega_chain_dom_mono_le A h_mcs (le_of_lt h) hm) ⟨haw, hwb⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkm
  rw [limit_f_eq A h_mcs w (k + d) hm]
  exact adj_g_mem_f_at_stage A h_mcs d k a b h_adj φ hφ w hm haw hwb

/-! ### Helper: Containing Adjacent Pair

Given a finite set D with points x, y ∈ D (x < y) and a point w ∉ D with x < w < y,
there exists an adjacent pair (a, b) in D with x ≤ a < w < b ≤ y.
-/

/-- For a point between two domain members that is not itself in the domain,
there exists an adjacent pair in the domain that contains it. -/
theorem exists_containing_adjacent (D : Finset Rat) (x y w : Rat)
    (hx : x ∈ D) (hy : y ∈ D) (hxy : x < y) (hw_not : w ∉ D)
    (hxw : x < w) (hwy : w < y) :
    ∃ a b, Adjacent D a b ∧ x ≤ a ∧ b ≤ y ∧ a < w ∧ w < b := by
  -- Let L = {d ∈ D | d < w}, R = {d ∈ D | w < d}
  -- x ∈ L (since x < w), y ∈ R (since w < y)
  -- Take a = max(L), b = min(R)
  have hL_ne : (D.filter (· < w)).Nonempty :=
    ⟨x, Finset.mem_filter.mpr ⟨hx, hxw⟩⟩
  have hR_ne : (D.filter (w < ·)).Nonempty :=
    ⟨y, Finset.mem_filter.mpr ⟨hy, hwy⟩⟩
  set a := (D.filter (· < w)).max' hL_ne with ha_def
  set b := (D.filter (w < ·)).min' hR_ne with hb_def
  have ha_mem : a ∈ D.filter (· < w) := Finset.max'_mem _ hL_ne
  have hb_mem : b ∈ D.filter (w < ·) := Finset.min'_mem _ hR_ne
  have ha_D : a ∈ D := (Finset.mem_filter.mp ha_mem).1
  have hb_D : b ∈ D := (Finset.mem_filter.mp hb_mem).1
  have haw : a < w := (Finset.mem_filter.mp ha_mem).2
  have hwb : w < b := (Finset.mem_filter.mp hb_mem).2
  have hab : a < b := lt_trans haw hwb
  have ha_ge_x : x ≤ a := Finset.le_max' _ x (Finset.mem_filter.mpr ⟨hx, hxw⟩)
  have hb_le_y : b ≤ y := Finset.min'_le _ y (Finset.mem_filter.mpr ⟨hy, hwy⟩)
  refine ⟨a, b, ⟨ha_D, hb_D, hab, ?_⟩, ha_ge_x, hb_le_y, haw, hwb⟩
  -- Adjacency: no u ∈ D with a < u < b
  intro u hu ⟨hau, hub⟩
  -- u ∈ D with a < u < b. Since a < u < w or u = w or w < u < b:
  rcases lt_trichotomy u w with huw | rfl | hwu
  · -- u < w: u ∈ L, so u ≤ a = max(L). But a < u, contradiction.
    exact absurd (Finset.le_max' _ u (Finset.mem_filter.mpr ⟨hu, huw⟩)) (not_le.mpr hau)
  · -- u = w: w ∉ D, contradiction
    exact hw_not hu
  · -- w < u: u ∈ R, so b = min(R) ≤ u. But u < b, contradiction.
    exact absurd (Finset.min'_le _ u (Finset.mem_filter.mpr ⟨hu, hwu⟩)) (not_le.mpr hub)

/-! ## Strong C5: Full Burgess C5a with Guard

The full C5a condition from Burgess 2.11: if U(ξ,η) ∈ limitF(x), then there exists
y > x in limitDom with η ∈ limitF(y) AND ξ ∈ limitG(x,y).

The guard condition ξ ∈ limitG(x,y) means: for all w ∈ limitDom with x < w < y,
ξ ∈ limitF(w). This is the key property for the truth lemma (Burgess Claim 2.11).

Proof strategy: The C5 elimination at finite stage n+1 produces a witness y with both
adj_guard (ξ ∈ g for adjacent pairs between x and y) and domain_guard (ξ ∈ f(w)
for old domain points between x and y). For any w in limitDom between x and y:
- If w ∈ dom_n (old point): domain_guard gives ξ ∈ f_{n+1}(w) = limitF(w).
- If w ∉ dom_{n+1} (added later): find containing adjacent pair (a,b) in dom_{n+1},
  adj_guard gives ξ ∈ g_{n+1}(a,b), then adj_g_mem_limit_f gives ξ ∈ limitF(w).
- If w ∈ dom_{n+1} \ dom_n (unique new point): w = y by dom_new_unique, contradicts w < y.
-/

theorem limit_satisfies_c5_strong (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    (x : Rat) (hx : x ∈ limitDom A h_mcs)
    (ξ η : Formula Atom)
    (h_until : (η U ξ) ∈ limitF A h_mcs x) :
    ∃ y ∈ limitDom A h_mcs, x < y ∧ η ∈ limitF A h_mcs y ∧
      ξ ∈ limitG A h_mcs x y := by
  obtain ⟨n₀, hn₀⟩ := hx
  obtain ⟨n, hn_ge, hn_eq⟩ := counterexample_enum_surjective_above
    ⟨x, 0, ξ, η, .c5_forward⟩ n₀
  have hx_n : x ∈ (omegaChainVal A h_mcs n).dom :=
    omega_chain_dom_mono_le A h_mcs hn_ge hn₀
  have h_until_n : (η U ξ) ∈ (omegaChainVal A h_mcs n).f x := by
    rw [omega_chain_f_agrees_le A h_mcs hn_ge x hn₀]
    rwa [← limit_f_eq A h_mcs x n₀ hn₀]
  obtain ⟨y, hy_dom_n1, hxy, hy_η_n1, h_adj_guard, h_dom_guard, h_new_or_id⟩ :=
    omega_chain_c5_witness A h_mcs n x ξ η hx_n h_until_n hn_eq
  refine ⟨y, ⟨n + 1, hy_dom_n1⟩, hxy, ?_, ?_⟩
  · rw [limit_f_eq A h_mcs y (n + 1) hy_dom_n1]; exact hy_η_n1
  -- Guard: ξ ∈ limitG(x,y), i.e., ∀ w ∈ limitDom, x < w → w < y → ξ ∈ limitF(w)
  intro w hw hxw hwy
  have hx_n1 : x ∈ (omegaChainVal A h_mcs (n + 1)).dom :=
    omega_chain_dom_mono A h_mcs n hx_n
  -- Three cases based on w's relationship to stages n and n+1
  by_cases hw_n : w ∈ (omegaChainVal A h_mcs n).dom
  · -- w ∈ dom_n: domain_guard gives ξ ∈ f_{n+1}(w), convert to limitF
    rw [limit_f_eq A h_mcs w (n + 1) (omega_chain_dom_mono A h_mcs n hw_n)]
    exact h_dom_guard w hw_n hxw hwy
  · -- w ∉ dom_n: use h_new_or_id to show w ∉ dom_{n+1}, then find adjacent pair.
    by_cases hw_n1 : w ∈ (omegaChainVal A h_mcs (n + 1)).dom
    · -- w ∈ dom_{n+1} \ dom_n.
      by_cases hy_n : y ∈ (omegaChainVal A h_mcs n).dom
      · -- y ∈ dom_n: by h_new_or_id, either y ∉ dom_n (contradiction) or dom_{n+1} ⊆ dom_n.
        -- In both cases we get contradiction with w ∉ dom_n.
        cases h_new_or_id with
        | inl h_new => exact absurd hy_n h_new
        | inr h_id => exact absurd (h_id w hw_n1) hw_n
      · exact absurd (omega_chain_dom_new_unique A h_mcs n w y hw_n1 hw_n hy_dom_n1 hy_n)
          (ne_of_lt hwy)
    · obtain ⟨a, b, h_adj_n1, ha_ge_x, hb_le_y, haw, hwb⟩ :=
        exists_containing_adjacent _ x y w hx_n1 hy_dom_n1 hxy hw_n1 hxw hwy
      exact adj_g_mem_limit_f A h_mcs (n + 1) a b h_adj_n1 ξ
        (h_adj_guard a b h_adj_n1 ha_ge_x hb_le_y) w hw haw hwb

theorem limit_satisfies_c5'_strong (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A)
    (x : Rat) (hx : x ∈ limitDom A h_mcs)
    (ξ η : Formula Atom)
    (h_since : (η S ξ) ∈ limitF A h_mcs x) :
    ∃ y ∈ limitDom A h_mcs, y < x ∧ η ∈ limitF A h_mcs y ∧
      ξ ∈ limitG A h_mcs y x := by
  obtain ⟨n₀, hn₀⟩ := hx
  obtain ⟨n, hn_ge, hn_eq⟩ := counterexample_enum_surjective_above
    ⟨x, 0, ξ, η, .c5_backward⟩ n₀
  have hx_n : x ∈ (omegaChainVal A h_mcs n).dom :=
    omega_chain_dom_mono_le A h_mcs hn_ge hn₀
  have h_since_n : (η S ξ) ∈ (omegaChainVal A h_mcs n).f x := by
    rw [omega_chain_f_agrees_le A h_mcs hn_ge x hn₀]
    rwa [← limit_f_eq A h_mcs x n₀ hn₀]
  obtain ⟨y, hy_dom_n1, hyx, hy_η_n1, h_adj_guard, h_dom_guard, h_new_or_id⟩ :=
    omega_chain_c5'_witness A h_mcs n x ξ η hx_n h_since_n hn_eq
  refine ⟨y, ⟨n + 1, hy_dom_n1⟩, hyx, ?_, ?_⟩
  · rw [limit_f_eq A h_mcs y (n + 1) hy_dom_n1]; exact hy_η_n1
  intro w hw hyw hwx
  have hx_n1 : x ∈ (omegaChainVal A h_mcs (n + 1)).dom :=
    omega_chain_dom_mono A h_mcs n hx_n
  by_cases hw_n : w ∈ (omegaChainVal A h_mcs n).dom
  · rw [limit_f_eq A h_mcs w (n + 1) (omega_chain_dom_mono A h_mcs n hw_n)]
    exact h_dom_guard w hw_n hyw hwx
  · by_cases hw_n1 : w ∈ (omegaChainVal A h_mcs (n + 1)).dom
    · by_cases hy_n : y ∈ (omegaChainVal A h_mcs n).dom
      · -- y ∈ dom_n: by h_new_or_id, either y ∉ dom_n (contradiction) or dom_{n+1} ⊆ dom_n.
        cases h_new_or_id with
        | inl h_new => exact absurd hy_n h_new
        | inr h_id => exact absurd (h_id w hw_n1) hw_n
      · exact absurd (omega_chain_dom_new_unique A h_mcs n w y hw_n1 hw_n hy_dom_n1 hy_n)
          (ne_of_gt hyw)
    · obtain ⟨a, b, h_adj_n1, ha_ge_y, hb_le_x, haw, hwb⟩ :=
        exists_containing_adjacent _ y x w hy_dom_n1 hx_n1 hyx hw_n1 hyw hwx
      exact adj_g_mem_limit_f A h_mcs (n + 1) a b h_adj_n1 ξ
        (h_adj_guard a b h_adj_n1 ha_ge_y hb_le_x) w hw haw hwb

end Cslib.Logic.Temporal.Metalogic.Chronicle
