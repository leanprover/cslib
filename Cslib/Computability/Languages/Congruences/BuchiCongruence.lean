/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Automata.NA.Pair
public import Cslib.Foundations.Combinatorics.InfiniteGraphRamsey
public import Cslib.Foundations.Data.Set.Saturation

/-!
# Buchi Congruence

A special type of right congruences used by J.R. Büchi to prove the closure
of ω-regular languages under complementation.
-/

@[expose] public section

namespace Cslib.Automata.NA.Buchi

open Function Set Filter ωAcceptor ωLanguage ωSequence LTS.Execution
open _root_.Language RightCongruence

variable {Symbol : Type*} {State : Type}

set_option linter.tacticAnalysis.verifyGrindOnly false in
/-- Given a Buchi automaton `na`, two finite words `u` and `v` are Buchi-congruent
according to `na` iff for every pair of states `s` and `t` of `na`, both of the
following two conditions hold:
(1) `u` can move `na` from `s` to `t` iff `v` can move `na` from `s` to `t`;
(2) `u` can move `na` from `s` to `t` via an accepting states iff `v` can move `na`
from `s` to `t` via an accepting states. -/
@[implicit_reducible]
def BuchiCongruence (na : Buchi State Symbol) : RightCongruence Symbol where
  eq.r u v :=
    ∀ s t, (u ∈ na.pairLang s t ↔ v ∈ na.pairLang s t) ∧
      (u ∈ na.pairViaLang na.accept s t ↔ v ∈ na.pairViaLang na.accept s t)
  eq.iseqv.refl := by grind
  eq.iseqv.symm := by grind
  eq.iseqv.trans := by grind
  right_cov.elim := by
    grind only [Covariant, → LTS.pairLang_split, <= LTS.pairLang_append, → LTS.pairViaLang_split,
      <= LTS.pairViaLang_append_pairLang, <= LTS.pairLang_append_pairViaLang]

open scoped Classical in
/-- `BuchiCongrParam` is a parameterization of the equivalence classes of `na.BuchiCongruence`
using the type `State → State → Prop × Prop`, which is finite if `State` is. -/
noncomputable def BuchiCongrParam (na : Buchi State Symbol)
    (f : State → State → Prop × Prop) : Quotient na.BuchiCongruence.eq :=
  if h : ∃ u, ∀ s t, ((f s t).1 ↔ u ∈ na.pairLang s t) ∧
      ((f s t).2 ↔ u ∈ na.pairViaLang na.accept s t)
  then ⟦ Classical.choose h ⟧
  else ⟦ [] ⟧

variable {na : Buchi State Symbol}

/-- `BuchiCongrParam` is surjective. -/
lemma buchiCongrParam_surjective : Surjective na.BuchiCongrParam := by
  intro q
  let f s t := (q.out ∈ na.pairLang s t, q.out ∈ na.pairViaLang na.accept s t)
  have h : ∃ u, ∀ s t, ((f s t).1 ↔ u ∈ na.pairLang s t) ∧
        ((f s t).2 ↔ u ∈ na.pairViaLang na.accept s t) := by
    use q.out
    grind
  use f
  simp only [BuchiCongrParam, h, ↓reduceDIte]
  rw [← Quotient.out_eq q]
  apply Quotient.sound
  intro s t
  grind

/-- `na.BuchiCongruence` is of finite index if `na` has only finitely many states. -/
theorem buchiCongruence_fin_index [Finite State] : Finite (Quotient na.BuchiCongruence.eq) :=
  Finite.of_surjective na.BuchiCongrParam buchiCongrParam_surjective

/-- If `xl` and `yl` belong to the same equivalence class of `na.BuchiCongruence`
and `xl` can move `na` from state `s` to state `t`, then so can `yl` and, furthermore,
if `xl` makes `na` go through an accepting state of `na`, then so can `yl`. -/
lemma buchiCongruence_transfer
    {a : Quotient na.BuchiCongruence.eq} {xl yl : List Symbol} {s t : State}
    (hc : xl ∈ na.BuchiCongruence.eqvCls a) (hc' : yl ∈ na.BuchiCongruence.eqvCls a)
    (hp : xl ∈ na.pairLang s t) : ∃ sl, na.Execution s yl t sl ∧
      ( xl ∈ na.pairViaLang na.accept s t → ∃ r ∈ na.accept, r ∈ sl ) := by
  have h_eq : na.BuchiCongruence.eq xl yl := by
    apply Quotient.exact
    #adaptation_note
    /-- A grind regression found moving to nightly-2026-03-31 (changes from lean#13166) -/
    have : ⟦xl⟧ = a := mem_singleton_iff.mp <| mem_preimage.mp hc
    have : ⟦yl⟧ = a := mem_singleton_iff.mp <| mem_preimage.mp hc'
    grind
  obtain ⟨l, r⟩ := h_eq s t
  by_cases h_xl : xl ∈ na.pairViaLang na.accept s t
  · obtain ⟨r, hr, xs₁, xs₂, h₁, h₂, rfl⟩ := LTS.mem_pairViaLang.mp (r.mp h_xl)
    obtain ⟨sl₁, he₁⟩ := LTS.Execution.of_mTr h₁
    obtain ⟨sl₂, he₂⟩ := LTS.Execution.of_mTr h₂
    refine ⟨sl₁ ++ sl₂.tail, he₁.comp he₂, fun _ ↦ ⟨_, hr, ?_⟩⟩
    grind [he₁.last]
  · use LTS.Execution.of_mTr (l.mp hp) |>.choose
    grind

/-- `na.buchiFamily` is a family of ω-languages indexed by a pair of equivalence classes
of `na.BuchiCongruence` which will turn out to saturate the ω-language accepted by `na`
and cover all possible ω-sequences. -/
def buchiFamily [Inhabited Symbol] (na : Buchi State Symbol) :
    Quotient na.BuchiCongruence.eq × Quotient na.BuchiCongruence.eq → ωLanguage Symbol
  | (a, b) => na.BuchiCongruence.eqvCls a * (na.BuchiCongruence.eqvCls b)^ω

theorem mem_buchiFamily [Inhabited Symbol]
    {xs : ωSequence Symbol} {a b : Quotient na.BuchiCongruence.eq} :
    xs ∈ na.buchiFamily (a, b) ↔ ∃ xl, ∃ xls : ωSequence (List Symbol),
      xl ∈ na.BuchiCongruence.eqvCls a ∧ (∀ k, xls k ∈ na.BuchiCongruence.eqvCls b - 1) ∧
      xl ++ω xls.flatten = xs := by
  grind [buchiFamily]

open Finset in
/-- `na.buchiFamily` is a cover if `na` has only finitely many states.
This theorem uses the Ramsey theorem for infinite graphs and does not depend on any details
of `na.BuchiCongruence` other than that it is of finite index. -/
theorem buchiFamily_cover [Inhabited Symbol] [Finite State] :
    ⨆ i, na.buchiFamily i = ⊤ := by
  apply mem_ext
  intro xs
  have : Finite (Quotient na.BuchiCongruence.eq) := buchiCongruence_fin_index
  let color (t : Finset ℕ) : Quotient na.BuchiCongruence.eq :=
    if h : t.Nonempty then ⟦ xs.extract (t.min' h) (t.max' h) ⟧ else ⟦ [] ⟧
  obtain ⟨b, ns, h_ns, h_color⟩ := infinite_graph_ramsey color
  obtain ⟨f, h_mono, rfl⟩ := strictMono_of_infinite h_ns
  simp only [ωLanguage.mem_iSup, Prod.exists, ωLanguage.mem_top, iff_true]
  use ⟦ xs.take (f 0) ⟧, b
  apply mem_buchiFamily.mpr
  use xs.take (f 0), xs.drop (f 0) |>.toSegs (f · - f 0)
  #adaptation_note
  /-- A grind regression found moving to nightly-2026-03-31 (changes from lean#13166) -/
  split_ands
  · rfl
  · intro k
    specialize h_color {f k, f (k + 1)}
    have := @h_mono 0 k
    have := @h_mono k (k + 1)
    simp only [Language.mem_sub_one, toSegs_def]
    split_ands
    · have : b = color {f k, f (k + 1)} := by grind
      simp_all only [extract_drop, color]
      split_ifs with h
      · have : f k ≤ f (k + 1) := by lia
        have : f 0 + (f k - f 0) = f k := by grind
        have : f 0 + (f (k + 1) - f 0) = f (k + 1) := by lia
        simp_all
        rfl
      · simp at h
    · grind
  · grind [Nat.base_zero_strictMono h_mono]

-- This intermediate result is split out of the proof of `buchiCongruence_saturation` below
-- because that proof was too big and kept exceeding the default `maxHeartbeats`.
private lemma frequently_via_accept [Inhabited Symbol]
    {xl : List Symbol} {xls : ωSequence (List Symbol)} {ss : ωSequence State}
    (h_acc : ∃ᶠ (k : ℕ) in atTop, ss k ∈ na.accept)
    (h_exec : na.OmegaExecution ss (xl ++ω xls.flatten))
    (h_xls_p : ∀ (k : ℕ), 0 < (xls k).length) :
    ∃ᶠ (k : ℕ) in atTop, xls k ∈ na.pairViaLang na.accept
      (ss (xl.length + xls.cumLen k)) (ss (xl.length + xls.cumLen (k + 1))) := by
  have hm : StrictMono (xl.length + xls.cumLen ·) := by grind [StrictMono, cumLen_strictMono]
  apply Frequently.mono <| frequently_in_strictMono hm h_acc
  rintro n ⟨k, _, _⟩
  apply LTS.mem_pairViaLang.mpr
  use ss (xl.length + xls.cumLen n + k), by grind, (xls n).take k, (xls n).drop k
  have := extract_flatten h_xls_p n
  have exec {m n} (h : m ≤ n) :=
    LTS.Execution.to_mTr <| LTS.OmegaExecution.extract_execution h_exec h
  split_ands
  · have h : xl.length + xls.cumLen n ≤ xl.length + xls.cumLen n + k := by lia
    specialize exec h
    grind [extract_append_right_right]
  · have h : xl.length + xls.cumLen n + k ≤ xl.length + xls.cumLen (n + 1) := by lia
    specialize exec h
    grind [extract_append_right_right]
  · grind only [!List.take_append_drop]

/-- `na.buchiFamily` saturates the ω-language accepted by `na`. -/
theorem buchiFamily_saturation [Inhabited Symbol] :
    Saturates (fun i ↦ (na.buchiFamily i).toSet) (language na).toSet := by
  -- first we introduce two ωSequences of symbols with the form `x := xl ++ω xls.flatten` and
  -- `y := yl ++ω yls.flatten`, Buchi-congruent and such that `x` is accepted by `na` along the
  -- state sequence `ss`.
  simp_rw [Saturates, Set.inter_nonempty, Set.subset_def, ← ωLanguage.mem_def, forall_exists_index,
    and_imp, Prod.forall, mem_buchiFamily, mem_sub_one, forall_and, List.ne_nil_iff_length_pos]
  rintro _ _ _ ⟨xl, xls, h_xl_c, ⟨h_xls_c, h_xls_p⟩, rfl⟩ ⟨ss, ⟨h_init, h_exec⟩, h_acc⟩ _
    ⟨yl, yls, h_yl_c, ⟨h_yls_c, h_yls_p⟩, rfl⟩
  let ts := ωSequence.mk (fun k ↦ ss (xl.length + xls.cumLen k))
  -- the head segment `xl` takes `na` from the start state to `ts 0`...
  have h_xl_e : xl ∈ na.pairLang (ss 0) (ts 0) := by
    rw [LTS.mem_pairLang]
    convert! LTS.OmegaExecution.extract_mTr h_exec xl.length.zero_le using 1
    simp [extract_append_zero_right]
  -- ... and the segment `xls k` takes `na` from `ts k` to `ts (k + 1)`
  have h_xls_e (k : ℕ) : xls k ∈ na.pairLang (ts k) (ts (k + 1)) := by
    have : xl.length + xls.cumLen k < xl.length + xls.cumLen (k + 1) :=
      Nat.add_lt_add_left (cumLen_strictMono h_xls_p k.lt_succ_self) xl.length
    grind [LTS.OmegaExecution.extract_mTr h_exec this.le, LTS.mem_pairLang,
      extract_append_right_right, add_tsub_cancel_left]
  -- for each such segment we choose a similar state sequence `sls k` for `y`.
  obtain ⟨sl, h_yl_e, _⟩ := buchiCongruence_transfer h_xl_c h_yl_c h_xl_e
  choose sls h_yls_e h_yls_a using
    fun k ↦ buchiCongruence_transfer (h_xls_c k) (h_yls_c k) (h_xls_e k)
  obtain ⟨sls, rfl⟩ : ∃ sls' : ωSequence (List State), (sls' : ℕ → List State) = sls := ⟨⟨sls⟩, rfl⟩
  -- our witness for `y` will be the sequence gluing `sl` and `sls` along their common start and
  -- endpoints: `sl ++ω (ωSequence.map List.dropLast sls).flatten.tail`. Auxilliary results:
  -- all the lengths agree
  have h_sls_drop_l (k : ℕ) : (ωSequence.map List.dropLast sls k).length = (yls k).length := by
    simp [List.length_dropLast, (h_yls_e k).length]
  have h_sls_drop_p (k : ℕ) : 0 < (ωSequence.map List.dropLast sls k).length :=
    h_sls_drop_l k ▸ h_yls_p k
  have h_sls_cl : (ωSequence.map List.dropLast sls).cumLen = yls.cumLen := by
    ext k; induction k <;> grind
  have : Inhabited State := ⟨ss 0⟩
  -- the initial state of the tail part is correct
  have h_fst : (ωSequence.map List.dropLast sls).flatten 0 = ts 0 := by
    have := flatten_get_add _ (h_sls_drop_p 0) h_sls_drop_p
    simp_rw [cumLen_zero, add_zero, get_map, List.getElem_dropLast] at this
    rw [this, (h_yls_e 0).start]
  -- use our witness: the start state is `ss 0 ∈ na.start` by `h_init`, and we can join the
  -- head and tail executions (for `yl` and `yls`) using `OmegaExecution.prepend_execution`.
  refine ⟨sl ++ω (ωSequence.map List.dropLast sls).flatten.tail,
    ⟨by rwa [get_append_left _ _ _ h_yl_e.length_ss_pos, h_yl_e.start],
    (LTS.OmegaExecution.flatten_execution' h_yls_e h_yls_p).prepend_execution h_yl_e h_fst⟩, ?_⟩
  -- it remains to show the witness satisfies the acceptance condition
  rw [frequently_atTop]
  intro n
  -- use the auxilliary lemma `frequently_via_accept` to transfer extract a witness for the
  -- acceptance of `x`
  obtain ⟨m, _, s, h_acc, h_mem⟩ :=
    frequently_atTop.mp ((frequently_via_accept h_acc h_exec h_xls_p).mono h_yls_a) n
  obtain ⟨k, hklen, rfl⟩ := List.mem_iff_getElem.mp h_mem
  rw [← sl.dropLast_append_getLast h_yl_e.ss_ne_nil, append_append_ωSequence,
    singleton_append_ωSequence, h_yl_e.getLast, ← h_fst, cons_head_tail]
  -- up to some messing around with indices, we use the same witness for `y`
  refine ⟨sl.dropLast.length + yls.cumLen m + k,
    by lia [(cumLen_strictMono h_yls_p).add_le_nat m 0],
    mem_of_eq_of_mem ?_ h_acc⟩
  rw [add_assoc, get_append_right]
  obtain (hk | rfl) : k < (yls m).length ∨ k = (yls m).length := by
    rwa [(h_yls_e m).length, k.lt_succ_iff, k.le_iff_lt_or_eq] at hklen
  · simp [← (sls m).getElem_dropLast (h_sls_drop_l m ▸ hk), ← h_sls_cl,
      flatten_get_add _ (h_sls_drop_l m ▸ hk) h_sls_drop_p]
  · rw [(h_yls_e m).last', ← cumLen_succ, ← (h_yls_e (m + 1)).start, ← h_sls_cl]
    convert! (sls.map List.dropLast).flatten_get_add (h_sls_drop_p (m + 1)) h_sls_drop_p using 1
    simp

end Cslib.Automata.NA.Buchi
