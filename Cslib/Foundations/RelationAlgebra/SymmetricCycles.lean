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

/-- Maddux's common-witness condition for a family of `k` pairs of diversity atoms. -/
def HasCommonWitnesses (k : ℕ) (T : Table α) : Prop :=
  ∀ p : Fin k → Sym α 2, ∃ w, ∀ i, w ::ₛ p i ∈ T

/-- Pad a nonempty family by repeating one pair. -/
theorem HasCommonWitnesses.mono {k l : ℕ} {T : Table α} (h : HasCommonWitnesses l T)
    (hk : 0 < k) (hl : k ≤ l) : HasCommonWitnesses k T := by
  intro p
  let f := Fin.castLEEmb hl
  obtain ⟨w, hw⟩ := h (Function.extend f p fun _ => p ⟨0, hk⟩)
  exact ⟨w, fun i => by simpa only [f.injective.extend_apply] using hw (f i)⟩

/-- In a network on at most `k + 1` vertices, a consistent partial assignment of diversity
labels to the edges incident to a new vertex extends to all those edges. This is the extension
step in Maddux's construction of a finite-dimensional relational basis (Theorem 14). -/
theorem HasCommonWitnesses.extend {k : ℕ} {T : Table α} (h : HasCommonWitnesses k T)
    {V : Type*} [Fintype V] (hV : Fintype.card V ≤ k + 1)
    (edge : V → V → α) (hsymm : ∀ i j, edge i j = edge j i) (s : Finset V) (c : V → α)
    (hc : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → c i ::ₛ pair (c j) (edge i j) ∈ T) :
    ∃ d : V → α, (∀ i ∈ s, d i = c i) ∧ ∀ i j, i ≠ j → d i ::ₛ pair (d j) (edge i j) ∈ T := by
  classical
  by_cases hall : ∀ i, i ∈ s
  · exact ⟨c, fun _ _ => rfl, fun i j => hc i (hall i) j (hall j)⟩
  obtain ⟨v, hv⟩ := not_forall.mp hall
  have hcard : s.card < Fintype.card V := by
    simpa [Finset.card_insert_of_notMem hv] using (insert v s).card_le_univ
  let f : s ↪ Fin k := s.equivFin.toEmbedding.trans (Fin.castLEEmb (by omega))
  let pairs (i : s) := pair (c i) (edge v i)
  let pad (_ : Fin k) := pair (c v) (c v)
  obtain ⟨w, hw⟩ := h (Function.extend f pairs pad)
  have hw' (i : V) (hi : i ∈ s) : w ::ₛ pair (c i) (edge v i) ∈ T := by
    simpa only [f.injective.extend_apply, pairs] using hw (f ⟨i, hi⟩)
  let c' := Function.update c v w
  have hc' : ∀ i ∈ insert v s, ∀ j ∈ insert v s, i ≠ j → c' i ::ₛ pair (c' j) (edge i j) ∈ T := by
    intro i hi j hj hij
    rcases Finset.mem_insert.mp hi with rfl | his
    · have hj := Finset.mem_of_mem_insert_of_ne hj hij.symm
      simpa [c', hij.symm] using hw' j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · rw [hsymm i j, pair, Sym.cons_swap]
      simpa [c', hij, pair] using hw' i his
    · simpa [c', ne_of_mem_of_not_mem his hv, ne_of_mem_of_not_mem hj hv] using hc i his j hj hij
  obtain ⟨d, hd, ht⟩ := h.extend hV edge hsymm (insert v s) c' hc'
  exact ⟨d, fun i hi => (hd i (Finset.mem_insert_of_mem hi)).trans
    (Function.update_of_ne (ne_of_mem_of_not_mem hi hv) ..), ht⟩
termination_by Fintype.card V - s.card
decreasing_by
  classical
  rw [Finset.card_insert_of_notMem hv]
  omega

private theorem card_missing_blocks {X W I : Type*} [Finite X] [Finite W] [Finite I]
    (e : W × I ↪ X) :
    (Nat.card {T : Set X // ∀ w, ¬ ∀ i, e (w, i) ∈ T} : ℝ) ≤
      2 ^ Nat.card X * (1 - (1 / 2 : ℝ) ^ Nat.card I) ^ Nat.card W := by
  classical
  let _ := Fintype.ofFinite X
  let _ := Fintype.ofFinite W
  let _ := Fintype.ofFinite I
  let B := {T : Set X // ∀ w, ¬ ∀ i, e (w, i) ∈ T}
  let R := Set.range e
  let row (T : B) (w : W) : {s : Set I // s ≠ Set.univ} :=
    ⟨{i | e (w, i) ∈ T.val}, fun h => T.prop w (Set.eq_univ_iff_forall.mp h)⟩
  let code (T : B) := (row T, (Subtype.val ⁻¹' T.val : Set ↥(Rᶜ : Set X)))
  have hinj : Function.Injective code := by
    intro S T h
    apply Subtype.ext
    ext x
    by_cases hx : x ∈ R
    · obtain ⟨⟨w, i⟩, rfl⟩ := hx
      exact Set.ext_iff.mp (congrArg Subtype.val (congrFun (congrArg Prod.fst h) w)) i
    · exact Set.ext_iff.mp (congrArg Prod.snd h) ⟨x, hx⟩
  have h := Nat.card_le_card_of_injective _ hinj
  have hrow : Nat.card {s : Set I // s ≠ Set.univ} = 2 ^ Nat.card I - 1 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  have hset : Nat.card (Set ↥(Rᶜ : Set X)) = 2 ^ (Rᶜ : Set X).ncard := by
    change _ = 2 ^ Nat.card ↥(Rᶜ : Set X)
    simp [Nat.card_eq_fintype_card]
  rw [Nat.card_prod, Nat.card_fun, hrow, hset] at h
  have hR := R.ncard_add_ncard_compl
  rw [show R.ncard = Nat.card W * Nat.card I from
    (Set.ncard_range_of_injective e.injective).trans (Nat.card_prod W I)] at hR
  calc
    (Nat.card B : ℝ) ≤ ((2 : ℝ) ^ Nat.card I - 1) ^ Nat.card W * 2 ^ (Rᶜ : Set X).ncard := by
      simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub Nat.one_le_two_pow, Nat.cast_one,
        Nat.cast_ofNat] using (Nat.cast_le (α := ℝ)).mpr h
    _ = _ := by
      rw [← hR, pow_add, Nat.mul_comm (Nat.card W), pow_mul, mul_right_comm,
        ← mul_pow, one_div, inv_pow, mul_sub, mul_inv_cancel₀ (by positivity), mul_one]

private theorem card_failed_family {n k : ℕ} (p : Fin k → Sym (Fin n) 2) :
    (Nat.card {T : Table (Fin n) // ¬ ∃ w, ∀ i, w ::ₛ p i ∈ T} : ℝ) ≤
      2 ^ ((n + 2).choose 3) * (1 - (1 / 2 : ℝ) ^ k) ^ (n - 2 * k) := by
  classical
  let U := Finset.univ.biUnion fun i => (p i).val.toFinset
  let W := {w : Fin n // w ∉ U}
  let I := Set.range p
  let e : W × I → Sym (Fin n) 3 := fun (w, q) => w.val ::ₛ q.val
  have free (w : W) (q : I) : w.val ∉ q.val := by
    obtain ⟨i, hi⟩ := q.prop
    rw [← hi, ← Sym.mem_coe]
    exact fun hw => w.prop (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simpa using hw⟩)
  have inj : Function.Injective e := by
    rintro ⟨w, a⟩ ⟨v, b⟩ h
    change w.val ::ₛ a.val = v.val ::ₛ b.val at h
    have hm : w.val ∈ v.val ::ₛ b.val := h ▸ Sym.mem_cons_self _ _
    obtain rfl : w = v := Subtype.ext ((Sym.mem_cons.mp hm).resolve_right (free w b))
    exact Prod.ext rfl (Subtype.ext (by simpa using h))
  have hmap := Nat.card_le_card_of_injective
    (fun T : {T : Table (Fin n) // ¬ ∃ w, ∀ i, w ::ₛ p i ∈ T} =>
      (⟨T.val, fun w hw => T.prop ⟨w.val, fun i => hw ⟨p i, i, rfl⟩⟩⟩ :
        {T : Table (Fin n) // ∀ w : W, ¬ ∀ q : I, e (w, q) ∈ T}))
    (fun _ _ h => Subtype.ext (Subtype.mk.inj h))
  have h := ((Nat.cast_le (α := ℝ)).mpr hmap).trans (card_missing_blocks ⟨e, inj⟩)
  have hU : U.card ≤ 2 * k := by
    simpa [U, Nat.mul_comm] using Finset.card_biUnion_le_card_mul Finset.univ
      (fun i => (p i).val.toFinset) 2 (fun i _ => by
        simpa using Multiset.toFinset_card_le (p i).val)
  have hW : n - 2 * k ≤ Nat.card W := by
    have hc := (U : Set (Fin n)).ncard_add_ncard_compl
    rw [Set.ncard_coe_finset, Nat.card_fin] at hc
    change U.card + Nat.card W = n at hc
    omega
  have hI : Nat.card I ≤ k := by
    simpa [I, Nat.card_eq_fintype_card] using Fintype.card_range_le p
  rw [Sym.natCard_sym_eq_choose, Nat.card_fin, Nat.add_succ_sub_one] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have hbase := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) hI
  have hnn (j : ℕ) : 0 ≤ 1 - (1 / 2 : ℝ) ^ j := sub_nonneg.mpr (pow_le_one₀ (by norm_num)
    (by norm_num))
  exact (pow_le_pow_left₀ (hnn _) (sub_le_sub_left hbase _) _).trans
    (pow_le_pow_of_le_one (hnn _) (sub_le_self _ (by positivity)) hW)

/-- A union bound over the families of pairs. For fixed `k`, the exceptional fraction decays
exponentially up to a polynomial factor. -/
theorem card_not_hasCommonWitnesses_le (k n : ℕ) :
    (Nat.card {T : Table (Fin n) // ¬ HasCommonWitnesses k T} : ℝ) ≤
      (n : ℝ) ^ (2 * k) * (2 ^ ((n + 2).choose 3) * (1 - (1 / 2 : ℝ) ^ k) ^ (n - 2 * k)) := by
  classical
  let X (p : Fin k → Sym (Fin n) 2) := {T : Table (Fin n) // ¬ ∃ w, ∀ i, w ::ₛ p i ∈ T}
  let B := {T : Table (Fin n) // ¬ HasCommonWitnesses k T}
  have fails (T : B) : ∃ p : Fin k → Sym (Fin n) 2, ¬ ∃ w, ∀ i, w ::ₛ p i ∈ T.val :=
    not_forall.mp T.prop
  choose p hp using fails
  let encode (T : B) : Σ p, X p := ⟨p T, T.val, hp T⟩
  have h := Nat.card_le_card_of_injective encode fun _ _ he =>
    Subtype.ext (congrArg (fun t : Σ p, X p => t.2.val) he)
  have hpairs : Nat.card (Sym (Fin n) 2) ≤ n ^ 2 := by
    rw [Sym.natCard_sym_eq_choose, Nat.card_fin, Nat.choose_two_right]
    simp only [Nat.add_succ_sub_one, Nat.add_sub_cancel]
    rw [pow_two, Nat.add_mul, one_mul]
    have := Nat.le_mul_self n
    omega
  have hf : (Fintype.card (Fin k → Sym (Fin n) 2) : ℝ) ≤ (n : ℝ) ^ (2 * k) := by
    rw [← Nat.card_eq_fintype_card, Nat.card_fun, Nat.card_fin, pow_mul]
    exact_mod_cast Nat.pow_le_pow_left hpairs k
  calc
    (Nat.card B : ℝ) ≤ Nat.card (Σ p, X p) := Nat.cast_le.mpr h
    _ = ∑ p, (Nat.card (X p) : ℝ) := by rw [Nat.card_sigma, Nat.cast_sum]
    _ ≤ _ := (Finset.sum_le_sum fun p _ => card_failed_family p).trans <| by
      simpa using mul_le_mul_of_nonneg_right hf (mul_nonneg (by positivity)
        (pow_nonneg (sub_nonneg.mpr (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num))) (n - 2 * k)))

theorem hasCommonWitnesses_two_iff (T : Table α) :
    HasCommonWitnesses 2 T ↔ HasWitnesses T := by
  constructor
  · intro h p q
    obtain ⟨w, hw⟩ := h ![p, q]
    exact ⟨w, hw 0, hw 1⟩
  · intro h p
    obtain ⟨w, hw, hw'⟩ := h (p 0) (p 1)
    exact ⟨w, fun i => by fin_cases i <;> assumption⟩

/-- Union bound for tables without common witnesses. -/
theorem card_not_hasWitnesses_le (n : ℕ) (hn : 2 ≤ n) :
    (Nat.card {T : Table (Fin n) // ¬ HasWitnesses T} : ℝ) ≤
      (n : ℝ) ^ 4 * (2 ^ ((n + 2).choose 3) * (3 / 4 : ℝ) ^ (n - 4)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa only [hasCommonWitnesses_two_iff, show 2 * 2 = 4 by decide,
    show 1 - (1 / 2 : ℝ) ^ 2 = 3 / 4 by norm_num] using card_not_hasCommonWitnesses_le 2 (2 + m)

open Filter
open scoped Topology

/-- Number of labelled symmetric tables on `n` diversity atoms. -/
theorem card_table (n : ℕ) : Nat.card (Table (Fin n)) = 2 ^ ((n + 2).choose 3) := by
  rw [Nat.card_eq_fintype_card, Fintype.card_set, ← Nat.card_eq_fintype_card,
    Sym.natCard_sym_eq_choose, Nat.card_fin]
  rfl

/-- Almost every labelled symmetric table supplies a common witness for every family of
`k` pairs, for each fixed `k`. This is the symmetric case of Maddux's Theorem 10. -/
theorem tendsto_card_hasCommonWitnesses_div_all (k : ℕ) :
    Tendsto (fun n => (Nat.card {T : Table (Fin n) // HasCommonWitnesses k T} : ℝ) /
      Nat.card (Table (Fin n))) atTop (𝓝 1) := by
  let r := 1 - (1 / 2 : ℝ) ^ k
  have hr : 0 ≤ r := sub_nonneg.mpr (pow_le_one₀ (by norm_num) (by norm_num))
  have hr' : r < 1 := sub_lt_self _ (by positivity)
  have hbound : Tendsto (fun n : ℕ => (n : ℝ) ^ (2 * k) * r ^ (n - 2 * k)) atTop (𝓝 0) := by
    by_cases hz : r = 0
    · apply tendsto_const_nhds.congr' _
      filter_upwards [eventually_gt_atTop (2 * k)] with n hn
      simp [hz, zero_pow (by omega : n - 2 * k ≠ 0)]
    have h := (tendsto_pow_const_mul_const_pow_of_lt_one (2 * k) hr hr').div_const (r ^ (2 * k))
    rw [zero_div] at h
    apply h.congr' _
    filter_upwards [eventually_ge_atTop (2 * k)] with n hn
    rw [← Nat.sub_add_cancel hn, pow_add r, Nat.sub_add_cancel hn]
    field_simp
  have hbad : Tendsto (fun n => (Nat.card {T : Table (Fin n) // ¬ HasCommonWitnesses k T} : ℝ) /
      Nat.card (Table (Fin n))) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => by positivity) _ hbound
    intro n
    rw [card_table, Nat.cast_pow, Nat.cast_ofNat, div_le_iff₀ (by positivity)]
    simpa only [r, mul_assoc, mul_left_comm, mul_comm] using card_not_hasCommonWitnesses_le k n
  have h := tendsto_const_nhds (x := (1 : ℝ)) |>.sub hbad
  rw [sub_zero] at h
  apply h.congr fun n => ?_
  let G := {T : Table (Fin n) | HasCommonWitnesses k T}
  have hc : (G.ncard : ℝ) + Gᶜ.ncard = Nat.card (Table (Fin n)) := by
    exact_mod_cast G.ncard_add_ncard_compl
  change 1 - (Gᶜ.ncard : ℝ) / _ = (G.ncard : ℝ) / _
  have hp : (Nat.card (Table (Fin n)) : ℝ) ≠ 0 := by rw [card_table]; positivity
  field_simp
  linarith

/-- For sufficiently many diversity atoms, at least half of all symmetric tables
have common witnesses. -/
theorem eventually_half_le_card_hasWitnesses :
    ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ ((n + 2).choose 3) / 2 ≤
      Nat.card {T : Table (Fin n) // HasWitnesses T} := by
  filter_upwards [(tendsto_card_hasCommonWitnesses_div_all 2).eventually_const_le
    (by norm_num : (1 / 2 : ℝ) < 1)] with n hn
  simp only [hasCommonWitnesses_two_iff, card_table, Nat.cast_pow, Nat.cast_ofNat] at hn
  linarith only [(le_div_iff₀ (by positivity)).mp hn]

end Cslib.RelationAlgebra.SymmetricCycles
