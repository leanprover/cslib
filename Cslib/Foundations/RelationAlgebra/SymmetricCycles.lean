/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.AtomStructure
public import Mathlib.Data.Sym.NatCard
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Symmetric integral cycle tables

An unordered triple of diversity atoms specifies a cycle in a symmetric integral algebra.
If any two pairs of diversity atoms have a common composition witness, the cycle table is
associative. The exceptional tables can be bounded by counting failures for a fixed pair of pairs.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.SymmetricCycles

variable {α : Type*}

/-- A table records which unordered diversity triples are cycles. -/
abbrev Table (α : Type*) := Set (Sym α 3)

/-- The unordered pair of two diversity atoms. -/
abbrev pair (a b : α) := a ::ₛ b ::ₛ Sym.nil

/-- Extend the diversity cycles with the forced identity cycles. -/
def cycle (T : Table α) : Option α → Option α → Option α → Prop
  | none, y, z => y = z
  | some x, none, z => some x = z
  | some x, some y, none => x = y
  | some x, some y, some z => z ::ₛ pair x y ∈ T

/-- Adjoin one identity atom to a symmetric diversity table. -/
def atomStructure (T : Table α) : AtomStructure (Option α) where
  conv := id
  id := {none}
  cycles := {c | cycle T c.1 c.2.1 c.2.2}

private theorem swap (T : Table α) {a b c : Option α} : cycle T a b c → cycle T a c b := by
  cases a <;> cases b <;> cases c <;> try (solve | simp [cycle, eq_comm])
  rename_i a b c
  change _ ::ₛ _ ∈ T → _ ::ₛ _ ∈ T
  suffices c ::ₛ pair a b = b ::ₛ pair a c by rw [this]; exact id
  apply Sym.ext
  simp only [pair, Sym.coe_cons, ← Multiset.singleton_add]
  ac_rfl

private theorem rot (T : Table α) {a b c : Option α} : cycle T a b c → cycle T b c a := by
  cases a <;> cases b <;> cases c <;> try (solve | simp [cycle, eq_comm])
  rename_i a b c
  change _ ::ₛ _ ∈ T → _ ::ₛ _ ∈ T
  suffices c ::ₛ pair a b = a ::ₛ pair b c by rw [this]; exact id
  apply Sym.ext
  simp only [pair, Sym.coe_cons, ← Multiset.singleton_add]
  ac_rfl

/-- Every two unordered pairs of diversity atoms have a common witness in the cycle table. -/
def HasWitnesses (T : Table α) : Prop :=
  ∀ p q : Sym α 2, ∃ w, w ::ₛ p ∈ T ∧ w ::ₛ q ∈ T

/-- A common witness supplies the missing edge in the associativity axiom. -/
theorem lawful_of_hasWitnesses {T : Table α} (h : HasWitnesses T) :
    LawfulAtomStructure (atomStructure T) where
  id_cycle_right := by
    rintro e a b (rfl : e = none) (h : cycle T a none b)
    cases a <;> exact h.symm
  exists_id_cycle_right a := ⟨none, rfl, by cases a <;> rfl⟩
  cycle_left := swap T
  assoc {r q p s t} h₁ h₂ := by
    change cycle T r q p at h₁
    change cycle T s t q at h₂
    change ∃ u, cycle T u t p ∧ cycle T r s u
    cases r with
    | none => obtain rfl : q = p := h₁; exact ⟨s, h₂, rfl⟩
    | some r =>
    cases s with
    | none =>
      obtain rfl : t = q := h₂
      exact ⟨some r, h₁, rfl⟩
    | some s =>
    cases t with
    | none =>
      obtain rfl : some s = q := h₂
      exact ⟨p, by cases p <;> rfl, h₁⟩
    | some t =>
    cases p with
    | none =>
      obtain rfl : q = some r := (rot T (rot T h₁)).symm
      exact ⟨some t, rfl, rot T (rot T h₂)⟩
    | some p =>
      obtain ⟨w, h₃, h₄⟩ := h (pair t p) (pair r s)
      exact ⟨some w, rot T (rot T (a := some t) (b := some p) (c := some w) h₃), h₄⟩

/-- For each disjoint pair of coordinates, three of the four subsets omit at least
one coordinate. All remaining coordinates can be chosen freely. -/
private theorem card_missing_pairs {X W : Type*} [Finite X] [Finite W] (e : W × Bool ↪ X) :
    (Nat.card {T : Set X // ∀ w, ¬(e (w, false) ∈ T ∧ e (w, true) ∈ T)} : ℝ) ≤
      2 ^ Nat.card X * (3 / 4 : ℝ) ^ Nat.card W := by
  classical
  let B := {T : Set X // ∀ w, ¬(e (w, false) ∈ T ∧ e (w, true) ∈ T)}
  let R := Set.range e
  let bits (T : B) (w : W) : Fin 3 :=
    if e (w, false) ∈ T.val then 0 else if e (w, true) ∈ T.val then 1 else 2
  let code (T : B) : (W → Fin 3) × Set ↥(Rᶜ : Set X) := (bits T, Subtype.val ⁻¹' T.val)
  have hinj : Function.Injective code := by
    intro S T he
    apply Subtype.ext
    ext x
    by_cases hx : x ∈ R
    · obtain ⟨⟨w, b⟩, rfl⟩ := hx
      have h : bits S w = bits T w := congrFun (congrArg Prod.fst he) w
      have hs := S.prop w
      have ht := T.prop w
      cases b <;> grind
    · exact Set.ext_iff.mp (congrArg Prod.snd he) ⟨x, hx⟩
  have h := Nat.card_le_card_of_injective _ hinj
  have hset : Nat.card (Set ↥(Rᶜ : Set X)) = 2 ^ (Rᶜ : Set X).ncard := by
    let _ := Fintype.ofFinite ↥(Rᶜ : Set X)
    change Nat.card (Set ↥(Rᶜ : Set X)) = 2 ^ Nat.card ↥(Rᶜ : Set X)
    simp [Nat.card_eq_fintype_card]
  rw [Nat.card_prod, Nat.card_fun, Nat.card_fin, hset] at h
  have hR : R.ncard = Nat.card W * 2 := by
    rw [Set.ncard_range_of_injective e.injective, Nat.card_prod]
    simp [Nat.card_eq_fintype_card]
  have hX := R.ncard_add_ncard_compl
  rw [hR] at hX
  change (Nat.card B : ℝ) ≤ _
  calc
    (Nat.card B : ℝ) ≤ (3 : ℝ) ^ Nat.card W * 2 ^ (Rᶜ : Set X).ncard := by exact_mod_cast h
    _ = 2 ^ Nat.card X * (3 / 4 : ℝ) ^ Nat.card W := by
      rw [← hX, pow_add, Nat.mul_comm, pow_mul, div_pow]
      norm_num
      field_simp

private theorem card_failed_witness {α : Type*} [Finite α] (p q : Sym α 2) (hpq : p ≠ q) :
    (Nat.card {T : Table α // ¬ ∃ w, w ::ₛ p ∈ T ∧ w ::ₛ q ∈ T} : ℝ) ≤
      2 ^ Nat.card (Sym α 3) * (3 / 4 : ℝ) ^ (Nat.card α - 4) := by
  classical
  let U : Finset α := p.val.toFinset ∪ q.val.toFinset
  let W := {w : α // w ∉ U}
  let e : W × Bool → Sym α 3 := fun (w, b) => w.val ::ₛ (if b then q else p)
  have free (w : W) : w.val ∉ p ∧ w.val ∉ q := by
    simpa [U, ← Sym.mem_coe] using w.prop
  have inj : Function.Injective e := by
    rintro ⟨x, b⟩ ⟨y, c⟩ h
    have hmem : x.val ∈ e (y, c) := h ▸ Sym.mem_cons_self _ _
    have hxy : x = y := by
      apply Subtype.ext
      cases c <;> simp_all [e]
    subst y
    cases b <;> cases c <;> simp_all [e, Ne.symm hpq]
  have h := card_missing_pairs (⟨e, inj⟩ : W × Bool ↪ Sym α 3)
  have hle := Nat.card_le_card_of_injective
    (fun T : {T : Table α // ¬ ∃ w, w ::ₛ p ∈ T ∧ w ::ₛ q ∈ T} =>
      (⟨T.val, fun w h => T.prop ⟨w.val, h⟩⟩ :
        {T : Table α // ∀ w : W, ¬(e (w, false) ∈ T ∧ e (w, true) ∈ T)}))
    (fun _ _ h => Subtype.ext (Subtype.mk.inj h))
  have hU : U.card ≤ 4 := by
    have hp := Multiset.toFinset_card_le p.val
    have hq := Multiset.toFinset_card_le q.val
    exact (Finset.card_union_le ..).trans (by simpa using Nat.add_le_add hp hq)
  have hW : Nat.card α - 4 ≤ Nat.card W := by
    have hh := (U : Set α).ncard_add_ncard_compl
    rw [Set.ncard_coe_finset] at hh
    change U.card + Nat.card W = Nat.card α at hh
    omega
  exact (Nat.cast_le.mpr hle).trans (h.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) hW) (by positivity)))

/-- Union bound for tables without common witnesses. -/
theorem card_not_hasWitnesses_le (n : ℕ) (hn : 2 ≤ n) :
    (Nat.card {T : Table (Fin n) // ¬ HasWitnesses T} : ℝ) ≤
      (n : ℝ) ^ 4 * (2 ^ ((n + 2).choose 3) * (3 / 4 : ℝ) ^ (n - 4)) := by
  classical
  let P := Sym (Fin n) 2
  let X (pq : P × P) :=
    {T : Table (Fin n) // ¬ ∃ w, w ::ₛ pq.1 ∈ T ∧ w ::ₛ pq.2 ∈ T}
  let B := {T : Table (Fin n) // ¬ HasWitnesses T}
  have hle : Nat.card B ≤ Nat.card (Σ pq, X pq) := by
    have h (T : B) : ∃ pq, ∃ z : X pq, z.val = T.val := by
      have h := T.prop
      simp only [HasWitnesses, not_forall] at h
      obtain ⟨p, q, hp⟩ := h
      exact ⟨(p, q), ⟨T.val, hp⟩, rfl⟩
    choose pq z hz using h
    exact Nat.card_le_card_of_injective (fun T => Sigma.mk (pq T) (z T)) fun x y h =>
      Subtype.ext <| (hz x).symm.trans ((congrArg (fun t : Σ pq, X pq => t.2.val) h).trans (hz y))
  have bound (pq : P × P) (hpq : pq.1 ≠ pq.2) :
      (Nat.card (X pq) : ℝ) ≤ 2 ^ ((n + 2).choose 3) * (3 / 4 : ℝ) ^ (n - 4) := by
    simpa only [Sym.natCard_sym_eq_choose, Nat.card_fin, Nat.add_succ_sub_one] using
      card_failed_witness pq.1 pq.2 hpq
  have hdiff : Nontrivial P := by
    let a : Fin n := ⟨0, by omega⟩
    let b : Fin n := ⟨1, by omega⟩
    exact ⟨pair a a, pair b b, fun h => by
      have hm : a ∈ pair b b := h ▸ Sym.mem_cons_self _ _
      simp [pair, a, b] at hm⟩
  have hX (pq : P × P) : (Nat.card (X pq) : ℝ) ≤
      2 ^ ((n + 2).choose 3) * (3 / 4 : ℝ) ^ (n - 4) := by
    by_cases hpq : pq.1 = pq.2
    · obtain ⟨p, hp⟩ := exists_ne pq.1
      have h := Nat.card_le_card_of_injective (fun T : X pq =>
        (⟨T.val, fun ⟨w, hw, _⟩ => T.prop
          ⟨w, hw, (congrArg (fun a => w ::ₛ a ∈ T.val) hpq).mp hw⟩⟩ : X (pq.1, p)))
        (fun _ _ he => Subtype.ext (Subtype.mk.inj he))
      exact (Nat.cast_le.mpr h).trans (bound _ hp.symm)
    · exact bound _ hpq
  have hP : Nat.card P ≤ n ^ 2 := by
    rw [Sym.natCard_sym_eq_choose, Nat.card_fin, Nat.choose_two_right]
    simp only [Nat.add_succ_sub_one, Nat.add_sub_cancel]
    rw [pow_two, Nat.add_mul, one_mul]
    have := Nat.mul_le_mul_left n (show 1 ≤ n by omega)
    omega
  have hPP : (Fintype.card (P × P) : ℝ) ≤ (n : ℝ) ^ 4 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_prod]
    exact_mod_cast (Nat.mul_le_mul hP hP).trans_eq (by ring)
  calc
    (Nat.card B : ℝ) ≤ Nat.card (Σ pq, X pq) := Nat.cast_le.mpr hle
    _ = ∑ pq, (Nat.card (X pq) : ℝ) := by rw [Nat.card_sigma, Nat.cast_sum]
    _ ≤ _ := (Finset.sum_le_sum fun pq _ => hX pq).trans <| by
      simpa using mul_le_mul_of_nonneg_right hPP (show
        0 ≤ (2 : ℝ) ^ ((n + 2).choose 3) * (3 / 4 : ℝ) ^ (n - 4) by positivity)

open Filter
open scoped Topology

/-- For sufficiently many diversity atoms, at least half of all symmetric tables
have common witnesses. -/
theorem eventually_half_le_card_hasWitnesses :
    ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ ((n + 2).choose 3) / 2 ≤
      Nat.card {T : Table (Fin n) // HasWitnesses T} := by
  have hlim := (tendsto_pow_const_mul_const_pow_of_lt_one 4 (r := (3 / 4 : ℝ))
    (by norm_num) (by norm_num)).mul_const ((3 / 4 : ℝ) ^ 4)⁻¹
  rw [zero_mul] at hlim
  filter_upwards [eventually_ge_atTop 4, hlim.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2)]
    with n hn hsmall
  have hn' : n - 4 + 4 = n := Nat.sub_add_cancel hn
  have hpow : (3 / 4 : ℝ) ^ n = (3 / 4 : ℝ) ^ (n - 4) * (3 / 4 : ℝ) ^ 4 := by
    rw [← pow_add, hn']
  change (n : ℝ) ^ 4 * (3 / 4 : ℝ) ^ n * _ ≤ _ at hsmall
  rw [hpow] at hsmall
  let G := {T : Table (Fin n) | HasWitnesses T}
  have hc := G.ncard_add_ncard_compl
  have htotal : Nat.card (Table (Fin n)) = 2 ^ ((n + 2).choose 3) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_set, ← Nat.card_eq_fintype_card,
      Sym.natCard_sym_eq_choose, Nat.card_fin]
    rfl
  rw [htotal] at hc
  have hr : (G.ncard : ℝ) + (Gᶜ.ncard : ℝ) = (2 : ℝ) ^ ((n + 2).choose 3) := by
    exact_mod_cast hc
  have hb := card_not_hasWitnesses_le n (by omega)
  change (Gᶜ.ncard : ℝ) ≤ _ at hb
  change _ ≤ (G.ncard : ℝ)
  norm_num at hsmall
  have hs : (n : ℝ) ^ 4 * (3 / 4 : ℝ) ^ (n - 4) ≤ 1 / 2 := by linarith only [hsmall]
  have h := mul_le_mul_of_nonneg_right hs (show 0 ≤ (2 : ℝ) ^ ((n + 2).choose 3) by positivity)
  linarith only [hr, hb, h]

end Cslib.RelationAlgebra.SymmetricCycles
