/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov, Antoine du Fresne von Hohenesche,
  Sorrachai Yingchareonthawornchai
-/

module

public import Cslib.Foundations.Data.SplayTree.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Amortized Complexity of Splay Trees

This module formalizes the amortized time complexity of bottom-up splay trees
using the potential method introduced by Sleator and Tarjan.

We define the rank of a tree as the base-2 logarithm of its node count, and
the potential Φ as the sum of ranks over all subtrees. It culminates in
the classical O(m log n + n log n) total cost bound for a sequence of
splay operations.
-/

@[expose] public section

variable {α : Type}

namespace SplayTree

open Tree

/-! ### Cost and Search-Path Length -/
section CostAndSearchPath

/-- Cost of a bottom-up splay: one unit per rotation.
Caution: If the search fails, we do not rotate (as currently
defined in splay) the empty leaf and start to rotate from
its ancestor, so the cost is path.length - 1. -/
def splay.cost [LinearOrder α] (t : Tree α) (q : α) : ℕ :=
  match descend t q with
  | (.nil, []) => 0
  | (.nil, _ :: rest) => rest.length
  | (.node _ _ _, path) => path.length

/-- Subtrees have positive search path length. -/
lemma searchPathLen_node_pos [LinearOrder α] (l : Tree α) (k : α) (r : Tree α)
    (q : α) : 1 ≤ (l △[k] r).searchPathLen q := by
  unfold searchPathLen
  split_ifs <;> omega

/-- Relation between `searchPathLen` and the length of the path produced by
`descend`. When `descend` reaches a node, the search path is one link longer;
when it reaches `.nil`, the two are equal. -/
theorem searchPathLen_eq_descend_length [LinearOrder α] (t : Tree α) (q : α) :
    t.searchPathLen q =
      (descend t q).2.length +
        (match (descend t q).1 with | .nil => 0 | .node _ _ _ => 1) := by
  induction t with
  | nil => simp [searchPathLen, descend, descend.go]
  | node k l r ihl ihr =>
    by_cases hqk : q = k
    · subst hqk
      simp [searchPathLen, descend_node_eq]
    · by_cases hlt : q < k
      · rw [descend_node_lt hlt]
        unfold searchPathLen
        simp only [hlt, if_true, List.length_append, List.length_singleton]
        rw [ihl]; omega
      · have hgt : k < q := by grind only
        rw [descend_node_gt hgt]
        unfold searchPathLen
        simp only [hlt, hgt, if_false, if_true, List.length_append,
          List.length_singleton]
        rw [ihr]; omega

end CostAndSearchPath


/-! ### Amortized Complexity (Potential Method)
We follow Sleator–Tarjan's potential method. The rank of a tree is
`log_2(nodeCount)`, the potential `φ` is the sum of ranks over all
subtrees. Each splay step (zig, zig-zig, zig-zag) satisfies a
per-step potential inequality, and these telescope along the frame
path to give the O(log n) amortized bound.
-/
noncomputable section PotentialMethod

/-- Rank of a tree: `log_2(nodeCount)`, or 0 for the empty tree. -/
def rank (t : Tree α) : ℝ :=
  if t.nodeCount = 0 then 0 else Real.logb 2 t.nodeCount

/-- Potential of a tree: sum of ranks over all subtrees (including itself). -/
def φ : Tree α → ℝ
  | .nil => 0
  | s@(l △[_] r) => rank s + φ l + φ r

/-! #### The key logarithmic inequality (AM-GM for logs) -/

theorem log_sum_le {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hsum : a + b ≤ c) :
    Real.logb 2 a + Real.logb 2 b ≤ 2 * Real.logb 2 c - 2 := by
  have hc : 0 < c := by linarith
  have hab_le : a * b ≤ c ^ 2 / 4 := by nlinarith [sq_nonneg (a - b)]
  have hln2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  suffices h : Real.log a + Real.log b ≤
      2 * Real.log c - 2 * Real.log 2 by
    simp only [Real.logb]
    rw [show Real.log a / Real.log 2 + Real.log b / Real.log 2 =
      (Real.log a + Real.log b) / Real.log 2 from by ring]
    rw [show 2 * (Real.log c / Real.log 2) - 2 =
      (2 * Real.log c - 2 * Real.log 2) / Real.log 2 from by
        field_simp]
    exact div_le_div_of_nonneg_right h hln2.le
  calc Real.log a + Real.log b
      = Real.log (a * b) := by
        rw [Real.log_mul (by positivity) (by positivity)]
    _ ≤ Real.log (c ^ 2 / 4) :=
        Real.log_le_log (by positivity) hab_le
    _ = Real.log (c ^ 2) - Real.log 4 :=
        Real.log_div (by positivity) (by positivity)
    _ = 2 * Real.log c - 2 * Real.log 2 := by
        rw [Real.log_pow, show (4:ℝ) = 2^2 from by norm_num,
          Real.log_pow]; push_cast; ring

/-! #### Basic rank and potential lemmas -/

@[simp] lemma rank_empty : rank (.nil : Tree α) = 0 := by simp [rank]

lemma rank_nonneg (t : Tree α) : 0 ≤ rank t := by
  simp only [rank]; split_ifs with h
  · rfl
  · exact Real.logb_nonneg (by grind)
      (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h)

@[simp] lemma φ_empty : φ (.nil : Tree α) = 0 := rfl

@[simp] lemma φ_node (l : Tree α) (k : α) (r : Tree α) :
    φ (l △[k] r) = rank (l △[k] r) + φ l + φ r := rfl

lemma φ_nonneg : ∀ t : Tree α, 0 ≤ φ t
  | .nil => le_refl _
  | l △[k] r => by
      simp [φ]; linarith [rank_nonneg (l △[k] r), φ_nonneg l, φ_nonneg r]

lemma rank_le_of_nodeCount_le {s t : Tree α}
    (h : s.nodeCount ≤ t.nodeCount) : rank s ≤ rank t := by
  simp only [rank]
  split_ifs with hs ht ht
  · exact le_refl _
  · exact Real.logb_nonneg (by norm_num)
      (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr ht)
  · omega
  · apply Real.logb_le_logb_of_le (by norm_num)
      (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hs)
      (by simp_all only [Nat.cast_le])

lemma rank_eq_of_nodeCount_eq {s t : Tree α}
    (h : s.nodeCount = t.nodeCount) : rank s = rank t := by
  exact le_antisymm (rank_le_of_nodeCount_le (le_of_eq h))
    (rank_le_of_nodeCount_le (le_of_eq h.symm))

@[simp] lemma rank_splay [LinearOrder α] (t : Tree α) (q : α) :
    rank (splay t q) = rank t :=
  rank_eq_of_nodeCount_eq (nodeCount_splay t q)

/-! #### Mirror preserves rank and potential -/

lemma rank_mirror (t : Tree α) : rank t.mirror = rank t := by
  simp [rank]

lemma φ_mirror : ∀ t : Tree α, φ t.mirror = φ t
  | .nil => rfl
  | l △[k] r => by
    change rank (r.mirror △[k] l.mirror) + φ r.mirror + φ l.mirror =
      rank (l △[k] r) + φ l + φ r
    rw [φ_mirror l, φ_mirror r]
    linarith [rank_eq_of_nodeCount_eq
      (show (r.mirror △[k] l.mirror).nodeCount =
        (l △[k] r).nodeCount by simp [nodeCount]; omega)]

/-- Transfer a potential-step inequality from mirrored trees to the
originals. -/
private lemma φ_transfer_mirror
    {step s c step' s' : Tree α}
    (hstep : step.mirror = step')
    (hs : s.mirror = s')
    (h : φ step' - φ s' + 2 ≤
      3 * (rank step' - rank c.mirror)) :
    φ step - φ s + 2 ≤ 3 * (rank step - rank c) := by
  rw [← hstep, φ_mirror, rank_mirror] at h
  rw [← hs, φ_mirror] at h
  linarith [rank_mirror c]

/-! #### Short‐hands for `logb 2` arithmetic (used in zig‐zig / zig‐zag) -/

/-- Monotonicity of `logb 2`. -/
private lemma logb_mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Real.logb 2 a ≤ Real.logb 2 b :=
  Real.logb_le_logb_of_le (by norm_num) ha hab

/-- Non‐negativity of `logb 2 x` when `x ≥ 1`. -/
private lemma logb_nonneg {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ Real.logb 2 x :=
  Real.logb_nonneg (by norm_num) hx

/-- `logb 2 x ≥ 1` when `x ≥ 2`. -/
private lemma one_le_logb {x : ℝ} (hx : 2 ≤ x) :
    1 ≤ Real.logb 2 x := by
  rwa [Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) (by linarith),
    show (2 : ℝ) ^ (1 : ℝ) = 2 from by norm_num]

/-! #### Potential of subtrees versus the whole tree -/

theorem φ_subtree_le_left (l : Tree α) (k : α) (r : Tree α) :
    φ l ≤ φ (l △[k] r) := by
  simp [φ]; linarith [rank_nonneg (l △[k] r), φ_nonneg r]

theorem φ_subtree_le_right (l : Tree α) (k : α) (r : Tree α) :
    φ r ≤ φ (l △[k] r) := by
  simp [φ]; linarith [rank_nonneg (l △[k] r), φ_nonneg l]

theorem φ_le_attach (c : Tree α) (f : Frame α) :
  φ c ≤ φ (f.attach c) := by
  cases f with | mk d k s =>
  cases d <;> simp [Frame.attach, φ_node] <;>
  linarith [rank_nonneg (c △[k] s), rank_nonneg (s △[k] c),
  φ_nonneg c, φ_nonneg s]

theorem φ_le_reassemble (c : Tree α) (path : List (Frame α)) :
    φ c ≤ φ (reassemble c path) := by
  induction path generalizing c with
  | nil => simp
  | cons f rest ih => simp only [reassemble_cons]; exact le_trans (φ_le_attach c f) (ih _)

theorem φ_descend_subtree_le [LinearOrder α] (t : Tree α) (q : α) :
    φ (descend t q).1 ≤ φ t := by
  have h := descend_preserves_tree t q
  calc φ (descend t q).1
      ≤ φ (reassemble (descend t q).1 (descend t q).2) :=
        φ_le_reassemble _ _
    _ = φ t := by rw [h]

/-! #### Splay step potential bounds -/

theorem φ_zig (c : Tree α) (f : Frame α) :
    φ (f.dir.bringUp (f.attach c)) - φ (f.attach c) ≤
      rank (f.dir.bringUp (f.attach c)) - rank c := by
  rcases f with ⟨d, key, sib⟩
  rcases c with _ | ⟨k, l, r⟩ <;> cases d <;>
    all_goals simp only [Dir.bringUp, rotateLeft, rotateRight,
    Frame.attach, φ_node, φ_empty, add_zero, sub_self, rank_empty, sub_zero]
  -- empty: 0 ≤ rank t; node: rank(child) ≤ rank(parent)
  · exact rank_nonneg _
  · exact rank_nonneg _
  · linarith [rank_le_of_nodeCount_le (show
      (r △[key] sib).nodeCount ≤
      ((l △[k] r) △[key] sib).nodeCount
      by simp)]
  · linarith [rank_le_of_nodeCount_le (show
      (sib △[key] l).nodeCount ≤
      (sib △[key] (l △[k] r)).nodeCount
      by simp; omega)]

/-- Zig-zig, left–left direction only. -/
private theorem φ_zigzig_left (c : Tree α)
    (k1 : α) (n1 : Tree α) (k2 : α) (n2 : Tree α) :
    let s := (Frame.mk .L k2 n2).attach ((Frame.mk .L k1 n1).attach c)
    let step := rotateRight (rotateRight s)
    φ step - φ s + 2 ≤ 3 * (rank step - rank c) := by
  set nn1 := (n1.nodeCount : ℝ); set nn2 := (n2.nodeCount : ℝ)
  have h1 : (0 : ℝ) ≤ nn1 := by positivity
  have h2 : (0 : ℝ) ≤ nn2 := by positivity
  rcases c with _ | ⟨k, l, r⟩ <;>
    simp +decide only [Frame.attach, rotateRight,
      φ_node, φ_empty, rank, add_zero, sub_zero,
      nodeCount_node, nodeCount_empty,
      Nat.add_eq_zero_iff, false_and, and_self,
      ↓reduceIte, Nat.cast_add, Nat.cast_one]
  all_goals ring_nf
  · nlinarith [
      logb_mono (show (0 : ℝ) < 1 + nn1 + nn2 by linarith)
        (show 1 + nn1 + nn2 ≤ 2 + nn1 + nn2 by linarith),
      logb_nonneg (show (1 : ℝ) ≤ 1 + nn1 by linarith),
      one_le_logb (show (2 : ℝ) ≤ 2 + nn1 + nn2 by linarith)]
  · set a := (l.nodeCount : ℝ); set b := (r.nodeCount : ℝ)
    have ha : (0 : ℝ) ≤ a := by positivity
    have hb : (0 : ℝ) ≤ b := by positivity
    have hls := log_sum_le
        (show (0 : ℝ) < 1 + a + b by linarith)
        (show (0 : ℝ) < 1 + nn1 + nn2 by linarith)
        (show 1 + a + b + (1 + nn1 + nn2) ≤
          3 + a + b + nn1 + nn2 by linarith)
    nlinarith [
      logb_mono (show (0 : ℝ) < 2 + b + nn1 + nn2 by linarith)
        (show 2 + b + nn1 + nn2 ≤
          3 + a + b + nn1 + nn2 by linarith),
      logb_mono (show (0 : ℝ) < 1 + a + b by linarith)
        (show 1 + a + b ≤ 2 + a + b + nn1 by linarith)]

theorem φ_zigzig (c : Tree α) (f1 f2 : Frame α)
    (heq : f1.dir = f2.dir) :
    let s := f2.attach (f1.attach c)
    let step := f2.dir.bringUp (f2.dir.bringUp s)
    φ step - φ s + 2 ≤ 3 * (rank step - rank c) := by
  rcases f1 with ⟨d, k1, n1⟩; rcases f2 with ⟨_, k2, n2⟩; subst heq
  cases d
  · exact φ_zigzig_left c k1 n1 k2 n2
  · have h := φ_zigzig_left c.mirror k1 n1.mirror k2 n2.mirror
    simp only [Frame.attach, Dir.bringUp] at h ⊢
    exact φ_transfer_mirror (by simp [mirror_rotateLeft]) (by simp) h

/-- Zig-zag, left–right direction only. -/
private theorem φ_zigzag_left (c : Tree α)
    (k1 : α) (n1 : Tree α) (k2 : α) (n2 : Tree α) :
    let f1 : Frame α := ⟨.L, k1, n1⟩
    let f2 : Frame α := ⟨.R, k2, n2⟩
    let s := f2.attach (f1.attach c)
    let step := rotateLeft (applyChild .R rotateRight s)
    φ step - φ s + 2 ≤ 3 * (rank step - rank c) := by
  set nn1 := (n1.nodeCount : ℝ); set nn2 := (n2.nodeCount : ℝ)
  have h1 : (0 : ℝ) ≤ nn1 := by positivity
  have h2 : (0 : ℝ) ≤ nn2 := by positivity
  rcases c with _ | ⟨k, l, r⟩ <;>
    simp +decide only [Frame.attach, applyChild,
      rotateRight, rotateLeft,
      φ_node, φ_empty, rank, add_zero, sub_zero,
      nodeCount_node, nodeCount_empty,
      Nat.add_eq_zero_iff, false_and, and_self,
      ↓reduceIte, Nat.cast_add, Nat.cast_one]
  all_goals ring_nf
  · have hls := log_sum_le
        (show (0 : ℝ) < nn1 + 1 by linarith)
        (show (0 : ℝ) < nn2 + 1 by linarith)
        (show nn1 + 1 + (nn2 + 1) ≤ nn1 + nn2 + 2 by linarith)
    simp only [show nn1 + 1 = 1 + nn1 by ring,
      show nn2 + 1 = 1 + nn2 by ring,
      show nn1 + nn2 + 2 = 2 + nn2 + nn1 by ring] at hls
    linarith [
      logb_nonneg (show (1 : ℝ) ≤ 1 + nn1 by linarith),
      logb_nonneg (show (1 : ℝ) ≤ 1 + nn2 by linarith)]
  · set a := (l.nodeCount : ℝ); set b := (r.nodeCount : ℝ)
    have ha : (0 : ℝ) ≤ a := by positivity
    have hb : (0 : ℝ) ≤ b := by positivity
    have hls := log_sum_le
        (show (0 : ℝ) < 1 + nn2 + a by linarith)
        (show (0 : ℝ) < 1 + b + nn1 by linarith)
        (show 1 + nn2 + a + (1 + b + nn1) ≤
          3 + nn2 + a + b + nn1 by linarith)
    nlinarith [
      logb_mono (show (0 : ℝ) < 1 + a + b by linarith)
        (show 1 + a + b ≤ 2 + a + b + nn1 by linarith),
      logb_mono (show (0 : ℝ) < 1 + a + b by linarith)
        (show 1 + a + b ≤ 3 + nn2 + a + b + nn1 by linarith)]

theorem φ_zigzag (c : Tree α) (f1 f2 : Frame α)
    (hne : f1.dir ≠ f2.dir) :
    let s := f2.attach (f1.attach c)
    let step := f2.dir.bringUp (applyChild f2.dir f1.dir.bringUp s)
    φ step - φ s + 2 ≤ 3 * (rank step - rank c) := by
  rcases f1 with ⟨d1, k1, n1⟩; rcases f2 with ⟨d2, k2, n2⟩
  cases d1 <;> cases d2 <;> simp_all +decide only [ne_eq]
  · exact φ_zigzag_left c k1 n1 k2 n2
  · have h := φ_zigzag_left c.mirror k1 n1.mirror k2 n2.mirror
    simp only [Frame.attach, Dir.bringUp, applyChild] at h ⊢
    exact φ_transfer_mirror
      (by simp [mirror_rotateRight, mirror_rotateLeft]) (by simp) h

/-! #### Telescoping: potential change along the full splayUp -/

lemma φ_attach_congr {s s' : Tree α} (f : Frame α)
    (h : s.nodeCount = s'.nodeCount) :
    φ (f.attach s') - φ (f.attach s) = φ s' - φ s := by
  cases f with | mk d k sib =>
  cases d <;> simp only [Frame.attach, φ_node, add_sub_add_right_eq_sub] <;>
    (unfold rank; simp [h])

lemma φ_reassemble_congr {s s' : Tree α} (path : List (Frame α))
    (h : s.nodeCount = s'.nodeCount) :
    φ (reassemble s' path) - φ (reassemble s path) = φ s' - φ s := by
  induction path generalizing s s' with
  | nil => simp
  | cons f rest ih =>
    simp only [reassemble_cons]
    rw [ih (by simp [nodeCount_Frame_attach, h])]
    exact φ_attach_congr f h

/-- The total potential change of splayUp plus the path length is at
    most 3 × the rank increase + 1. -/
theorem φ_splayUp (c : Tree α) (path : List (Frame α)) :
    φ (splayUp c path) - φ (reassemble c path) + path.length ≤
      3 * (rank (splayUp c path) - rank c) + 1 := by
  induction c, path using splayUp_induction with
  | nil c => simp
  | single c f =>
    simp only [splayUp_singleton, reassemble_cons,
      reassemble_nil, List.length_singleton, Nat.cast_one]
    linarith [φ_zig c f,
      rank_le_of_nodeCount_le (α := α)
        (show c.nodeCount ≤
          (f.dir.bringUp (f.attach c)).nodeCount from by simp)]
  | step c f1 f2 rest ih =>
    rw [splayUp_cons_cons]; simp only [List.length_cons]
    split_ifs with hdir
    · set s := f2.attach (f1.attach c)
      set step_tree := f2.dir.bringUp (f2.dir.bringUp s)
      have hnn : step_tree.nodeCount = s.nodeCount := by
        simp [step_tree]
      simp only [reassemble_cons]; push_cast
      nlinarith [ih step_tree,
        φ_reassemble_congr rest hnn.symm, φ_zigzig c f1 f2 hdir]
    · set s := f2.attach (f1.attach c)
      set step_tree :=
        f2.dir.bringUp (applyChild f2.dir f1.dir.bringUp s)
      have hnn : step_tree.nodeCount = s.nodeCount := by
        simp [step_tree]
      simp only [reassemble_cons]; push_cast
      nlinarith [ih step_tree,
        φ_reassemble_congr rest hnn.symm, φ_zigzag c f1 f2 hdir]

/-! #### The main O(log n) amortized bound -/

private lemma rank_eq_logb {t : Tree α}
    (h : t.nodeCount ≠ 0) :
    rank t = Real.logb 2 t.nodeCount := by
  simp [rank, h]

private lemma nodeCount_pos_of_descend_nonempty_path
    [LinearOrder α] {t : Tree α} {q : α}
    {reached : Tree α} {path : List (Frame α)}
    (hdecomp : descend t q = (reached, path))
    (hpath : path ≠ []) : t.nodeCount ≠ 0 := by
  intro h0
  have hd := nodeCount_descend t q
  rw [hdecomp] at hd; simp at hd
  rcases path with _ | ⟨f, rest⟩
  · exact hpath rfl
  · simp [pathNodes, Frame.nodes] at hd; omega

theorem splay_amortized_bound [LinearOrder α]
    (t : Tree α) (q : α) :
    φ (splay t q) - φ t + splay.cost t q ≤
      3 * Real.logb 2 t.nodeCount + 1 := by
  rcases hdecomp : descend t q with ⟨reached, path⟩
  have hpres := descend_preserves_tree t q
  rw [hdecomp] at hpres; simp only at hpres
  have h_splay : splay t q = splayUp reached path ∨
      (∃ f rest, reached = .nil ∧
        path = f :: rest ∧
        splay t q = splayUp (f.attach .nil) rest) := by
    simp only [splay, hdecomp]
    rcases reached with _ | ⟨k, l, r⟩
    · rcases path with _ | ⟨f, rest⟩
      · left; rfl
      · right; exact ⟨f, rest, rfl, rfl, rfl⟩
    · left; rfl
  rcases reached with _ | ⟨k, l, r⟩
  · rcases path with _ | ⟨f, rest⟩
    · simp only [reassemble, List.foldl_nil] at hpres
      subst hpres
      simp [splay, splay.cost, hdecomp, φ]
    · have h_cost : splay.cost t q = rest.length := by simp [splay.cost, hdecomp]
      rw [h_cost]
      have h_eq : splay t q = splayUp (f.attach .nil) rest := by simp [splay, hdecomp]
      rw [h_eq]
      set base := f.attach (.nil : Tree α)
      have hpres' : reassemble base rest = t := by rw [← hpres]; simp [reassemble, base]
      have hφ := φ_splayUp base rest
      rw [hpres'] at hφ
      have hrank_eq : rank (splayUp base rest) = rank t := by
        have h := rank_splay t q; simp only [splay, hdecomp] at h; exact h
      have hnn : t.nodeCount ≠ 0 :=
        nodeCount_pos_of_descend_nonempty_path hdecomp (List.cons_ne_nil f rest)
      calc φ (splayUp base rest) - φ t + ↑rest.length
          ≤ 3 * (rank (splayUp base rest) - rank base) + 1 := by exact_mod_cast hφ
        _ ≤ 3 * rank (splayUp base rest) + 1 := by linarith [rank_nonneg base]
        _ = 3 * Real.logb 2 t.nodeCount + 1 := by rw [hrank_eq, rank_eq_logb hnn]
  · have h_cost : splay.cost t q = path.length := by simp [splay.cost, hdecomp]
    rw [h_cost]
    have h_eq : splay t q = splayUp (l △[k] r) path := by simp [splay, hdecomp]
    rw [h_eq]
    have hφ := φ_splayUp (l △[k] r) path
    rw [hpres] at hφ
    have hrank_eq : rank (splayUp (l △[k] r) path) = rank t := by
      have h := rank_splay t q; simp only [splay, hdecomp] at h; exact h
    have hnn : t.nodeCount ≠ 0 := by
      have hd := nodeCount_descend t q; rw [hdecomp] at hd; simp at hd; omega
    calc φ (splayUp (l △[k] r) path) - φ t + ↑path.length
        ≤ 3 * (rank (splayUp (l △[k] r) path) - rank (l △[k] r)) + 1 := by exact_mod_cast hφ
      _ ≤ 3 * rank (splayUp (l △[k] r) path) + 1 := by linarith [rank_nonneg (l △[k] r)]
      _ = 3 * Real.logb 2 t.nodeCount + 1 := by rw [hrank_eq, rank_eq_logb hnn]

end PotentialMethod


/-! ### Sequence Cost and The O(m log n) Amortized Bound -/
section SequenceCost

/-! #### Splay Sequence -/

/-- A clean sequence generator for a series of splays. -/
def splaySeq [LinearOrder α] {m : ℕ} (init : Tree α)
(X : Fin m → α) : Fin (m + 1) → Tree α :=
  fun i => Nat.recOn i.val init (fun j acc =>
    if h : j < m then splay acc (X ⟨j, h⟩) else acc)

/-- The total cost is defined as the sum of actual rotations
performed across the generated sequence. -/
def splay.sequenceCost [LinearOrder α] {m : ℕ} (init : Tree α) (X : Fin m → α) : ℕ :=
  ∑ i : Fin m, splay.cost (splaySeq init X i.castSucc) (X i)

/-- The tree at step `i+1` is exactly the result of splaying the target key
on the tree at step `i`. -/
lemma splaySeq_succ [LinearOrder α] {m : ℕ}
(init : Tree α) (X : Fin m → α) (i : Fin m) :
    splaySeq init X i.succ = splay (splaySeq init X i.castSucc) (X i) := by
  unfold splaySeq
  simp only [Fin.val_succ, Fin.val_castSucc, Fin.is_lt, ↓reduceDIte]

/-- Splaying preserves the number of nodes across the entire sequence. -/
lemma splaySeq_nodeCount [LinearOrder α] {m : ℕ}
(init : Tree α) (X : Fin m → α) (i : Fin (m + 1)) :
    (splaySeq init X i).nodeCount = init.nodeCount := by
  unfold splaySeq
  generalize i.val = j
  induction j with
  | zero => rfl
  | succ k ih =>
    simp_all only
    split
    next h => simp_all only [nodeCount_splay]
    next h => simp_all only [not_lt]

/-! #### Initial Potential Bound -/

private lemma nat_log_le (a b : ℕ) (hab : a ≤ b) :
    (a : ℝ) * Real.logb 2 a ≤ (a : ℝ) * Real.logb 2 b := by
  by_cases ha : a = 0
  · simp [ha]
  · have ha_pos : (0 : ℝ) < a := Nat.cast_pos.mpr (Nat.pos_of_ne_zero ha)
    have hab_real : (a : ℝ) ≤ (b : ℝ) := Nat.cast_le.mpr hab
    have h_log : Real.logb 2 a ≤ Real.logb 2 b :=
      Real.logb_le_logb_of_le (by norm_num) ha_pos hab_real
    have ha_nonneg : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    exact mul_le_mul_of_nonneg_left h_log ha_nonneg

/-- Bound the maximum possible potential of any initial tree: Φ ≤ n log₂ n. -/
lemma φ_le_n_log_n [LinearOrder α] (init : Tree α) :
    φ init ≤ init.nodeCount * Real.logb 2 init.nodeCount := by
  induction init with
  | nil => simp [φ]
  | node k l r ihl ihr =>
    set t := l △[k] r
    have hl_le : l.nodeCount ≤ t.nodeCount := by simp [t, nodeCount]; omega
    have hr_le : r.nodeCount ≤ t.nodeCount := by simp [t, nodeCount]
    have h_rank : rank t = Real.logb 2 t.nodeCount := by
      unfold rank
      have : t.nodeCount ≠ 0 := by simp [t, nodeCount]
      simp [this]
    calc φ t = rank t + φ l + φ r := rfl
      _ ≤ rank t + l.nodeCount * Real.logb 2 l.nodeCount +
                   r.nodeCount * Real.logb 2 r.nodeCount := by linarith
      _ ≤ Real.logb 2 t.nodeCount +
          l.nodeCount * Real.logb 2 t.nodeCount +
          r.nodeCount * Real.logb 2 t.nodeCount := by
        rw [h_rank]
        have h1 := nat_log_le _ _ hl_le
        have h2 := nat_log_le _ _ hr_le
        linarith
      _ = (1 + l.nodeCount + r.nodeCount : ℝ) * Real.logb 2 t.nodeCount := by ring
      _ = t.nodeCount * Real.logb 2 t.nodeCount := by simp [t, nodeCount]

/-! #### General Sequence Cost Theorem -/

theorem amortized_cost_bound {S : Type*} (m : ℕ)
    (s : Fin (m + 1) → S) (cost : Fin m → ℝ)
    (Φ : S → ℝ) (B : ℝ)
    (hamort : ∀ i : Fin m,
      Φ (s i.succ) - Φ (s i.castSucc) + cost i ≤ B) :
    ∑ i : Fin m, cost i ≤
      m * B + Φ (s 0) - Φ (s (Fin.last m)) := by
  have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    hamort i
  simp_all +decide only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
  Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
  ge_iff_le]
  linarith! [Fin.sum_univ_castSucc fun i => Φ (s i),
    Fin.sum_univ_succ fun i => Φ (s i)]

theorem amortized_cost_bound' {S : Type*} (m : ℕ)
    (s : Fin (m + 1) → S) (cost : Fin m → ℝ)
    (Φ : S → ℝ) (B : ℝ)
    (hamort : ∀ i : Fin m,
      Φ (s i.succ) - Φ (s i.castSucc) + cost i ≤ B)
    (hΦ_nonneg : ∀ x, 0 ≤ Φ x) :
    ∑ i : Fin m, cost i ≤ m * B + Φ (s 0) := by
  linarith [amortized_cost_bound m s cost Φ B hamort,
    hΦ_nonneg (s (Fin.last m))]

theorem splay_total_cost [LinearOrder α] (m : ℕ)
    (t : Fin (m + 1) → Tree α)
    (q : Fin m → α) (n : ℕ)
    (hseq : ∀ i : Fin m,
      t i.succ = splay (t i.castSucc) (q i))
    (hsize : ∀ i : Fin (m + 1),
      (t i).nodeCount ≤ n) :
    ∑ i : Fin m,
      (splay.cost (t i.castSucc) (q i) : ℝ) ≤
      m * (3 * Real.logb 2 n + 1) + φ (t 0) := by
  apply amortized_cost_bound' m t
    (fun i => (splay.cost (t i.castSucc) (q i) : ℝ))
    φ (3 * Real.logb 2 n + 1)
  · intro i
    rw [hseq i]
    have hb := splay_amortized_bound
      (t i.castSucc) (q i)
    by_cases h : (t (Fin.castSucc i)).nodeCount = 0
    · simp_all +decide [Real.logb]
      have : (0 : ℝ) ≤ Real.log n / Real.log 2 :=
        by positivity
      linarith
    · calc φ (splay (t i.castSucc) (q i)) -
              φ (t i.castSucc) +
              splay.cost (t i.castSucc) (q i)
          ≤ 3 * Real.logb 2
              (t i.castSucc).nodeCount + 1 := hb
        _ ≤ 3 * Real.logb 2 n + 1 := by
            gcongr <;> [norm_num; exact hsize _]
  · exact fun x => φ_nonneg x

/-! #### The Main Total Cost Bound Theorem -/

theorem nlogn_cost [LinearOrder α] (n m : ℕ) (X : Fin m → α)
    (init : Tree α) (h_size : init.nodeCount = n) :
    splay.sequenceCost init X ≤ m * (3 * Real.logb 2 n + 1) + n * Real.logb 2 n := by
  have h_amortized := splay_total_cost m (splaySeq init X) X n
    (splaySeq_succ init X)
    (fun i => by rw [splaySeq_nodeCount, h_size])
  have h_phi_bound : φ (splaySeq init X 0) ≤ n * Real.logb 2 n := by
    have : splaySeq init X 0 = init := rfl
    rw [this, ← h_size]
    exact φ_le_n_log_n init
  unfold splay.sequenceCost
  push_cast
  linarith

end SequenceCost

end SplayTree
