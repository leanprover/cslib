/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Asymptotics
public import Mathlib.Data.Finite.Perm

/-!
# Unlabelled symmetric cycle tables

A nonidentity permutation carrying `a` to `b` forces the entries for all triples
`{b, g x, g y}` with `x, y` outside `{a, b}`. Burnside's lemma then bounds the correction
to the labelled count divided by the number of labellings. This gives the symmetric case
of the passage to isomorphism classes in Maddux, *Finite integral relation algebras*, Theorem 11.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.SymmetricCycles

variable {α : Type*}

/-- Permutations relabel every diversity atom in a table. -/
@[instance_reducible]
def tableAction : MulAction (Equiv.Perm α) (Table α) where
  smul g T := Sym.map g.symm ⁻¹' T
  one_smul T := Set.ext fun x => by
    change x.map id ∈ T ↔ x ∈ T
    rw [Sym.map_id]
  mul_smul g h T := Set.ext fun x => by
    change x.map _ ∈ T ↔ (x.map g.symm).map h.symm ∈ T
    rw [Sym.map_map]
    rfl

attribute [local instance] tableAction

/-- Symmetric diversity tables up to relabelling their atoms. -/
abbrev UnlabelledTable (α : Type*) := MulAction.orbitRel.Quotient (Equiv.Perm α) (Table α)

private theorem mem_smul (g : Equiv.Perm α) (T : Table α) (x : Sym α 3) :
    x.map g ∈ g • T ↔ x ∈ T := by
  change (x.map g).map g.symm ∈ T ↔ _
  rw [Sym.map_map, Equiv.symm_comp_self, Sym.map_id]

private theorem witnesses_smul {k : ℕ} {T : Table α} (g : Equiv.Perm α)
    (h : HasCommonWitnesses k T) : HasCommonWitnesses k (g • T) := by
  intro p
  obtain ⟨w, hw⟩ := h fun i => (p i).map g.symm
  refine ⟨g w, fun i => ?_⟩
  simpa only [Sym.map_cons, Sym.map_map, Equiv.self_comp_symm, Sym.map_id] using
    (mem_smul g T _).mpr (hw i)

/-- Having common witnesses is invariant under relabelling. -/
def UnlabelledTable.HasCommonWitnesses (k : ℕ) (q : UnlabelledTable α) : Prop :=
  Quotient.liftOn q (SymmetricCycles.HasCommonWitnesses k) fun _ T ⟨g, hg⟩ => by
    subst_vars
    exact propext ⟨fun h => by simpa using witnesses_smul g⁻¹ h, witnesses_smul g⟩

theorem UnlabelledTable.hasCommonWitnesses_out {k : ℕ} {q : UnlabelledTable α} :
    SymmetricCycles.HasCommonWitnesses k q.out ↔ q.HasCommonWitnesses k :=
  (congrArg (UnlabelledTable.HasCommonWitnesses k) q.out_eq).to_iff

/-- Every unlabelled table with witnesses for two pairs defines an integral relation algebra. -/
noncomputable def UnlabelledTable.toIsoClass {n : ℕ}
    (q : {q : UnlabelledTable (Fin n) // q.HasCommonWitnesses 2}) :
    RelationAlgebra.IsoClass.ofAtoms (n + 1) :=
  letI := lawful_of_hasWitnesses ((hasCommonWitnesses_two_iff _).mp
    (UnlabelledTable.hasCommonWitnesses_out.mpr q.prop))
  RelationAlgebra.IsoClass.ofAlgebra (A := ComplexAlgebra (atomStructure q.val.out)) <| by
    rw [ComplexAlgebra.card_atoms]
    simp [Nat.card_eq_fintype_card]

theorem UnlabelledTable.isIntegral_toIsoClass {n : ℕ}
    (q : {q : UnlabelledTable (Fin n) // q.HasCommonWitnesses 2}) :
    RelationAlgebra.IsoClass.IsIntegral (UnlabelledTable.toIsoClass q) := by
  let _ := lawful_of_hasWitnesses ((hasCommonWitnesses_two_iff _).mp
    (UnlabelledTable.hasCommonWitnesses_out.mpr q.prop))
  unfold UnlabelledTable.toIsoClass
  exact (RelationAlgebra.IsoClass.isIntegral_ofAlgebra _).mpr
    ((ComplexAlgebra.isIntegral_iff _).mpr ⟨none, rfl⟩)

theorem UnlabelledTable.toIsoClass_injective (n : ℕ) :
    Function.Injective (@UnlabelledTable.toIsoClass n) := by
  intro x y h
  let S := atomStructure x.val.out
  let R := atomStructure y.val.out
  let _ := lawful_of_hasWitnesses ((hasCommonWitnesses_two_iff _).mp
    (UnlabelledTable.hasCommonWitnesses_out.mpr x.prop))
  let _ := lawful_of_hasWitnesses ((hasCommonWitnesses_two_iff _).mp
    (UnlabelledTable.hasCommonWitnesses_out.mpr y.prop))
  obtain ⟨e⟩ : Nonempty (RelationAlgebraEquiv (ComplexAlgebra S) (ComplexAlgebra R)) :=
    (RelationAlgebra.IsoClass.ofAlgebra_eq_iff ..).mp h
  let f := ComplexAlgebra.atomEquiv S e
  have hn : f none = none := by
    have hl : ({none} : ComplexAlgebra S) = 1 := rfl
    have hr : (1 : ComplexAlgebra R) = {none} := rfl
    have h := ComplexAlgebra.map_singleton_eq S e none
    rw [hl, map_one, hr] at h
    have he : ({none} : Set (Option (Fin n))) = {f none} := congrArg ComplexAlgebra.carrier h
    simpa only [Set.singleton_eq_singleton_iff] using he.symm
  have hf (a : Fin n) : some (f.removeNone a) = f (some a) := by
    apply f.removeNone_some
    cases ha : f (some a) with
    | none => exact False.elim (Option.some_ne_none _ (f.injective (ha.trans hn.symm)))
    | some b => exact ⟨b, rfl⟩
  apply Subtype.ext
  apply x.val.out_eq.symm.trans
  apply Eq.trans _ y.val.out_eq
  apply Quotient.sound
  refine ⟨f.removeNone⁻¹, ?_⟩
  ext t
  obtain ⟨a,t,rfl⟩ := t.exists_eq_cons_of_succ
  obtain ⟨b,t,rfl⟩ := t.exists_eq_cons_of_succ
  obtain ⟨c,t,rfl⟩ := t.exists_eq_cons_of_succ
  rw [Sym.eq_nil_of_card_zero t]
  change ((a ::ₛ pair b c).map f.removeNone) ∈ y.val.out ↔ _
  have hcy := ComplexAlgebra.atomEquiv_mem_cycles S e (some b) (some c) (some a)
  change (f (some b), f (some c), f (some a)) ∈ R.cycles ↔ _ at hcy
  rw [← hf, ← hf, ← hf] at hcy
  simpa only [pair, Sym.map_cons, Sym.eq_nil_of_card_zero (Sym.nil.map f.removeNone)] using
    (show f.removeNone a ::ₛ pair (f.removeNone b) (f.removeNone c) ∈ y.val.out ↔
      a ::ₛ pair b c ∈ x.val.out from hcy)

/-- A table fixed by a nonidentity permutation is determined by the entries outside a set
of at least `(n - 1).choose 2` forced coordinates. -/
theorem card_fixedBy_mul_le (n : ℕ) (g : Equiv.Perm (Fin n)) (hg : g ≠ 1) :
    Nat.card (MulAction.fixedBy (Table (Fin n)) g) * 2 ^ ((n - 1).choose 2) ≤
      Nat.card (Table (Fin n)) := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, g a ≠ a := not_forall.mp fun h => hg (Equiv.ext h)
  let U : Finset (Fin n) := {a, g a}
  let V := ↥(Uᶜ : Finset (Fin n))
  let old (p : Sym V 2) := a ::ₛ p.map Subtype.val
  let forced (p : Sym V 2) := (old p).map g
  have hinj : Function.Injective forced := by
    intro x y h
    have h' := Sym.map_injective g.injective 3 h
    exact Sym.map_injective Subtype.val_injective 2 (by simpa [old] using h')
  let R := Set.range forced
  have outside (p : Sym V 2) : old p ∉ R := by
    rintro ⟨q, h⟩
    have hmem : g a ∈ old p := h ▸ (show g a ∈ forced q by
      simp [forced, old, Sym.map_cons])
    rcases Sym.mem_cons.mp hmem with he | hm
    · exact ha he
    obtain ⟨x, _, hx⟩ := Sym.mem_map.mp hm
    have := x.prop
    simp [U, hx] at this
  let code (T : MulAction.fixedBy (Table (Fin n)) g) : Set ↥(Rᶜ : Set (Sym (Fin n) 3)) :=
    Subtype.val ⁻¹' T.val
  have inj : Function.Injective code := by
    intro S T he
    have hmem (x) (hx : x ∉ R) := Set.ext_iff.mp he ⟨x, hx⟩
    have hf (A : MulAction.fixedBy (Table (Fin n)) g) (p) : forced p ∈ A.val ↔ old p ∈ A.val := by
      have he : g • A.val = A.val := A.prop
      simpa only [forced, he] using mem_smul g A.val (old p)
    apply Subtype.ext
    ext x
    by_cases hx : x ∈ R
    · obtain ⟨p, rfl⟩ := hx
      exact (hf S p).trans ((hmem (old p) (outside p)).trans (hf T p).symm)
    · exact hmem x hx
  have hV : Nat.card V = n - 2 := by
    change Nat.card ↥(Uᶜ : Finset (Fin n)) = _
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_compl, Fintype.card_fin,
      Finset.card_pair ha.symm]
  have hR : R.ncard = (n - 1).choose 2 := by
    rw [Set.ncard_range_of_injective hinj, Sym.natCard_sym_eq_choose, hV]
    have h := U.card_le_univ
    simp [U, ha.symm] at h
    congr 1
    omega
  have hc := R.ncard_add_ncard_compl
  rw [hR] at hc
  calc
    _ ≤ Nat.card (Set ↥(Rᶜ : Set (Sym (Fin n) 3))) * 2 ^ ((n - 1).choose 2) :=
      Nat.mul_le_mul_right _ (Nat.card_le_card_of_injective _ inj)
    _ = _ := by
      change _ = Nat.card (Set (Sym (Fin n) 3))
      simp only [Nat.card_eq_fintype_card, Fintype.card_set]
      rw [← pow_add]
      congr 1
      change (n - 1).choose 2 + Nat.card ↥(Rᶜ : Set _) = Nat.card (Sym (Fin n) 3) at hc
      simpa only [Nat.card_eq_fintype_card, add_comm] using hc

private theorem card_le_card_orbits_mul (n : ℕ) (P : UnlabelledTable (Fin n) → Prop) :
    Nat.card {T : Table (Fin n) // P ⟦T⟧} ≤
      Nat.card {q : UnlabelledTable (Fin n) // P q} * n.factorial := by
  classical
  let X := {T : Table (Fin n) // P ⟦T⟧}
  let q (x : X) : {q : UnlabelledTable (Fin n) // P q} := ⟨⟦x.val⟧, x.prop⟩
  have h (x : X) : ∃ g : Equiv.Perm (Fin n), g • (q x).val.out = x.val :=
    Quotient.exact (q x).val.out_eq.symm
  choose g hg using h
  have hinj : Function.Injective (fun x : X => (q x, g x)) := by
    intro x y he
    apply Subtype.ext
    rw [← hg x, ← hg y, show q x = q y from congrArg Prod.fst he,
      show g x = g y from congrArg Prod.snd he]
  simpa only [Nat.card_prod, Nat.card_perm, Nat.card_fin] using Nat.card_le_card_of_injective _ hinj

open Filter
open scoped Topology

private theorem eventually_factorial_le :
    ∀ᶠ n : ℕ in atTop, 2 ^ n * n.factorial ≤ 2 ^ ((n - 1).choose 2) := by
  filter_upwards [IsoClass.eventually_pow_le_choose, eventually_ge_atTop 1] with n h hn
  apply Nat.le_of_mul_le_mul_right (c := 2 ^ (n - 1)) _ (by positivity)
  calc
    _ ≤ 2 ^ n * n ^ n * 2 ^ n := by
      gcongr
      · exact n.factorial_le_pow
      · omega
    _ = (4 * n) ^ n := by rw [show 4 = 2 * 2 by decide, mul_pow, mul_pow]; ring
    _ ≤ (4 * n ^ 3) ^ n := by gcongr; exact Nat.le_self_pow (by decide) _
    _ ≤ 2 ^ n.choose 2 := h
    _ = _ := by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
      simp [← pow_add, Nat.choose_succ_succ', Nat.add_comm]

/-- Dividing the labelled count by the number of permutations gives the asymptotic number
of symmetric tables up to relabelling. -/
theorem tendsto_card_orbits_mul_factorial_div_tables :
    Tendsto (fun n => (Nat.card (UnlabelledTable (Fin n)) : ℝ) * n.factorial /
      Nat.card (Table (Fin n))) atTop (𝓝 1) := by
  classical
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  have hupper := (tendsto_const_nhds (x := (1 : ℝ))).add hlim
  rw [add_zero] at hupper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · filter_upwards with n
    have low := card_le_card_orbits_mul n (fun _ => True)
    simp only [Nat.card_subtype_true] at low
    exact (one_le_div (by exact_mod_cast Nat.card_pos)).mpr (by exact_mod_cast low)
  · filter_upwards [eventually_factorial_le] with n hn
    let G := Equiv.Perm (Fin n)
    let X := Table (Fin n)
    let _ := Fintype.ofFinite G
    let c (g : G) : ℝ := Nat.card (MulAction.fixedBy X g)
    let _ := Fintype.ofFinite (UnlabelledTable (Fin n))
    have hG : Nat.card G = n.factorial := (Nat.card_perm (α := Fin n)).trans (by rw [Nat.card_fin])
    have hb : ∑ g, c g = (Nat.card (UnlabelledTable (Fin n)) : ℝ) * n.factorial := by
      have he := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G X
      simp only [← Nat.card_eq_fintype_card] at he
      rw [hG] at he
      simpa only [c, Nat.cast_sum, Nat.cast_mul] using congrArg Nat.cast (α := ℕ) (β := ℝ) he
    have h1 : c 1 = Nat.card X := by
      simp [c]
    have hg (g : G) (hg : g ∈ Finset.univ.erase 1) :
        c g ≤ (Nat.card X : ℝ) / 2 ^ ((n - 1).choose 2) := by
      apply (le_div_iff₀ (by positivity)).mpr
      dsimp only [c]
      exact_mod_cast card_fixedBy_mul_le n g (Finset.mem_erase.mp hg).1
    have hc : ((Finset.univ.erase (1 : G)).card : ℝ) ≤ n.factorial := by
      exact_mod_cast (Finset.card_le_univ _).trans_eq (Nat.card_eq_fintype_card.symm.trans hG)
    have hsum := (Finset.sum_le_sum hg).trans (show ∑ _g ∈ Finset.univ.erase (1 : G),
        (Nat.card X : ℝ) / 2 ^ ((n - 1).choose 2) ≤
        n.factorial * ((Nat.card X : ℝ) / 2 ^ ((n - 1).choose 2)) by
      simpa using mul_le_mul_of_nonneg_right hc (show 0 ≤ (Nat.card X : ℝ) / 2 ^ _ by positivity))
    rw [← hb, ← Finset.sum_erase_add _ _ (Finset.mem_univ 1), h1]
    have hpos : (0 : ℝ) < Nat.card X := by exact_mod_cast Nat.card_pos
    apply (div_le_iff₀ hpos).mpr
    have hfrac : (n.factorial : ℝ) / 2 ^ ((n - 1).choose 2) ≤ (1 / 2 : ℝ) ^ n := by
      rw [div_le_iff₀ (by positivity), one_div, inv_pow, inv_mul_eq_div,
        le_div_iff₀ (by positivity)]
      rw [mul_comm] at hn
      exact_mod_cast hn
    have hmul := mul_le_mul_of_nonneg_right hfrac hpos.le
    rw [add_mul, one_mul, add_comm (Nat.card X : ℝ)]
    apply add_le_add_left (hsum.trans ?_)
    convert hmul using 1
    ring

/-- For each fixed number of pairs, almost all symmetric tables up to relabelling have
common witnesses. -/
theorem tendsto_card_hasCommonWitnesses_div_orbits (k : ℕ) :
    Tendsto (fun n => (Nat.card {q : UnlabelledTable (Fin n) // q.HasCommonWitnesses k} : ℝ) /
      Nat.card (UnlabelledTable (Fin n))) atTop (𝓝 1) := by
  have h := (tendsto_card_hasCommonWitnesses_div_all k).div
    tendsto_card_orbits_mul_factorial_div_tables (by norm_num)
  rw [div_one] at h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' h tendsto_const_nhds
  · filter_upwards with n
    have hT : (0 : ℝ) < Nat.card (Table (Fin n)) := by exact_mod_cast Nat.card_pos
    have hQ : (0 : ℝ) < Nat.card (UnlabelledTable (Fin n)) := by exact_mod_cast Nat.card_pos
    have hF : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
    have hc := card_le_card_orbits_mul n (UnlabelledTable.HasCommonWitnesses k)
    change (Nat.card _ : ℝ) / _ / (_ * _ / _) ≤ _ / _
    rw [div_div_div_cancel_right₀ hT.ne', div_le_div_iff₀ (mul_pos hQ hF) hQ]
    have hle : (Nat.card {T : Table (Fin n) // HasCommonWitnesses k T} : ℝ) ≤
        Nat.card {q : UnlabelledTable (Fin n) // q.HasCommonWitnesses k} * (n.factorial : ℝ) := by
      exact_mod_cast hc
    simpa only [mul_assoc, mul_comm, mul_left_comm] using mul_le_mul_of_nonneg_right hle hQ.le
  · filter_upwards with n
    apply (div_le_one (by exact_mod_cast Nat.card_pos)).mpr
    exact Nat.cast_le.mpr (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective)

end Cslib.RelationAlgebra.SymmetricCycles
