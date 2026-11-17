/-
Copyright (c) 2026 Sparsa Roychowdhury. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sparsa Roychowdhury
-/

module

public import Cslib.Computability.Automata.MPDA.Underapprox
public import Mathlib.Data.Set.Card

/-! # Hole-bounded sequences

Holes are the underapproximation introduced in [AkshayGastinKrishnaRoychowdhury2020]. A hole of
stack `i` is a factor of the form `(↓ᵢ ws)⁺`: pending pushes on stack `i`, each followed by a
well-nested sequence. Well-nested sequences do not distinguish stacks, so the sequences `ws` may
use any stack, while the pending pushes of a hole all use the same stack. A push that is closed by
a well-nested continuation, that is a push `↓` with matching pop `↑` such that `↓ ws ↑` is
well-nested, belongs to a well-nested sequence and never opens a hole.

A sequence is `K`-hole-bounded if at most `K` holes are open at each position.

## Main definitions

- `MPDA.WellMatched`: a push that is closed by a well-nested continuation.
- `MPDA.HolePush`: a push that is not closed by a well-nested continuation.
- `MPDA.SameHole`: two pending hole pushes that belong to the same open hole.
- `MPDA.openHoles`: the number of holes open at a position.
- `MPDA.HoleBounded`: at most `K` holes are open at each position.

## Main statements

- `MPDA.WellNested.net_eq_zero`, `MPDA.WellNested.net_take_nonneg`: well-nested sequences are
  balanced on every stack.
- `MPDA.WellNested.exists_wellMatched`: every push of a well-nested sequence is closed by a
  well-nested continuation.
- `MPDA.WellNested.holeBounded_zero`: well-nested sequences are `0`-hole-bounded.

## Implementation notes

We count open holes through their pending pushes. At position `x`, take the hole pushes that are
pending at `x`, in order. Two consecutive ones belong to the same hole exactly when they push on
the same stack and the factor between them is well-nested. Each open hole is then counted once,
through its first pending push.

## References

* [S. Akshay, P. Gastin, S. Krishna, S. Roychowdhury,
  *Revisiting Underapproximate Reachability for Multipushdown Systems*]
  [AkshayGastinKrishnaRoychowdhury2020]
-/

@[expose] public section

namespace Cslib.Automata.MPDA

variable {n : ℕ} {Γ α β : Type*}

/-! ## Net effect on a stack -/

@[simp]
theorem net_nil (i : Fin n) : net i ([] : List (α × Op n Γ)) = 0 := rfl

@[simp]
theorem net_cons (i : Fin n) (μ : α × Op n Γ) (w : List (α × Op n Γ)) :
    net i (μ :: w) = μ.2.net i + net i w := by
  simp [net]

@[simp]
theorem net_append (i : Fin n) (u w : List (α × Op n Γ)) :
    net i (u ++ w) = net i u + net i w := by
  simp [net]

theorem Op.net_push_nonneg (i j : Fin n) (γ : Γ) : 0 ≤ (Op.push j γ).net i := by
  simp only [Op.net]
  split_ifs <;> simp

theorem Op.net_pop (i j : Fin n) (γ γ' : Γ) : (Op.pop j γ).net i = -(Op.push j γ').net i := by
  simp only [Op.net]
  split_ifs <;> simp

/-- A well-nested sequence leaves the height of every stack unchanged. -/
theorem WellNested.net_eq_zero {w : List (α × Op n Γ)} (hw : WellNested w) (i : Fin n) :
    net i w = 0 := by
  induction hw with
  | nil => rfl
  | nop _ ih => simp [ih, Op.net]
  | @pushPop a b j γ u u' _ _ ih ih' =>
    rw [net_cons, net_append, net_cons, ih, ih', Op.net_pop i j γ γ]
    simp

/-- No prefix of a well-nested sequence pops below the initial height of any stack. -/
theorem WellNested.net_take_nonneg {w : List (α × Op n Γ)} (hw : WellNested w) (i : Fin n) :
    ∀ k, 0 ≤ net i (w.take k) := by
  induction hw with
  | nil => intro k; simp
  | nop _ ih =>
    intro k
    cases k with
    | zero => simp
    | succ k =>
      rw [List.take_succ_cons, net_cons]
      simpa [Op.net] using ih k
  | @pushPop a b j γ u u' hu _ ih ih' =>
    intro k
    cases k with
    | zero => simp
    | succ k =>
      rw [List.take_succ_cons, net_cons, List.take_append, net_append]
      have hδ := Op.net_push_nonneg i j γ
      rcases Nat.eq_zero_or_pos (k - u.length) with h | h
      · rw [h, List.take_zero, net_nil]
        have := ih k
        dsimp only
        omega
      · obtain ⟨k', hk'⟩ : ∃ k', k - u.length = k' + 1 := ⟨_, (Nat.succ_pred_eq_of_pos h).symm⟩
        rw [hk', List.take_succ_cons, net_cons, List.take_of_length_le (by omega),
          hu.net_eq_zero i, Op.net_pop i j γ γ]
        have := ih' k'
        dsimp only
        omega

/-! ## Shifting positions -/

theorem factor_cons_succ (x : β) (w : List β) (a b : ℕ) :
    factor (x :: w) (a + 1) (b + 1) = factor w a b := by
  simp [factor]

theorem factor_append_left (v w : List β) (a b : ℕ) :
    factor (v ++ w) (v.length + a) (v.length + b) = factor w a b := by
  unfold factor
  rw [List.drop_append, List.drop_of_length_le (by omega), List.nil_append,
    show v.length + a - v.length = a by omega, show v.length + b - (v.length + a) = b - a by omega]

theorem factor_append_right (w v : List β) {a b : ℕ} (hb : b ≤ w.length) :
    factor (w ++ v) a b = factor w a b := by
  unfold factor
  by_cases ha : a ≤ w.length
  · rw [List.drop_append_of_le_length ha, List.take_append_of_le_length (by simp; omega)]
  · rw [show b - a = 0 by omega, List.take_zero, List.take_zero]

theorem matches_cons_succ (x : α × Op n Γ) (w : List (α × Op n Γ)) (p m : ℕ) :
    Matches (x :: w) (p + 1) (m + 1) ↔ Matches w p m := by
  simp only [Matches, List.getElem?_cons_succ, Nat.add_lt_add_iff_right, factor_cons_succ]

theorem matches_append_left (v w : List (α × Op n Γ)) (p m : ℕ) :
    Matches (v ++ w) (v.length + p) (v.length + m) ↔ Matches w p m := by
  induction v with
  | nil => simp
  | cons x v ih =>
    rw [List.cons_append, List.length_cons, show v.length + 1 + p = v.length + p + 1 by omega,
      show v.length + 1 + m = v.length + m + 1 by omega, matches_cons_succ, ih]

theorem Matches.lt_length {w : List (α × Op n Γ)} {p m : ℕ} (h : Matches w p m) :
    m < w.length := by
  obtain ⟨_, _, _, ⟨b, γ, hm⟩, _⟩ := h
  exact (List.getElem?_eq_some_iff.mp hm).1

theorem Matches.append_right {w : List (α × Op n Γ)} {p m : ℕ} (h : Matches w p m)
    (v : List (α × Op n Γ)) : Matches (w ++ v) p m := by
  have hm := h.lt_length
  obtain ⟨hpm, i, ⟨a, γ, hp⟩, ⟨b, γ', hm'⟩, hk, hnet⟩ := h
  refine ⟨hpm, i, ⟨a, γ, ?_⟩, ⟨b, γ', ?_⟩, ?_, ?_⟩
  · rw [List.getElem?_append_left (by omega), hp]
  · rw [List.getElem?_append_left hm, hm']
  · rw [factor_append_right _ _ (by omega)]
    exact hk
  · rw [factor_append_right _ _ (by omega)]
    exact hnet

/-! ## Hole pushes and open holes -/

/-- Position `p` of `w` is a push on stack `i`. -/
def IsPushOn (w : List (α × Op n Γ)) (i : Fin n) (p : ℕ) : Prop :=
  ∃ a γ, w[p]? = some (a, .push i γ)

/-- The push at position `p` is closed by a well-nested continuation: it has a matching pop at
some position `m`, and the factor from `p` to `m` is well-nested. -/
def WellMatched (w : List (α × Op n Γ)) (p : ℕ) : Prop :=
  ∃ m, Matches w p m ∧ WellNested (factor w p (m + 1))

/-- A hole push is a push that is not closed by a well-nested continuation. Hole pushes are the
pending pushes that make up holes. -/
def HolePush (w : List (α × Op n Γ)) (p : ℕ) : Prop :=
  (∃ i, IsPushOn w i p) ∧ ¬WellMatched w p

/-- The push at position `p` is a hole push that is pending at position `x`. -/
def OpenHolePush (w : List (α × Op n Γ)) (x p : ℕ) : Prop :=
  HolePush w p ∧ PendingAt w p x

/-- The pending hole pushes at positions `p < q` belong to the same hole at position `x`: they push
on the same stack and the factor strictly between them is well-nested. -/
def SameHole (w : List (α × Op n Γ)) (x p q : ℕ) : Prop :=
  p < q ∧ OpenHolePush w x p ∧ OpenHolePush w x q ∧ (∃ i, IsPushOn w i p ∧ IsPushOn w i q) ∧
    WellNested (factor w (p + 1) q)

/-- The number of holes of `w` open at position `x`. Each open hole is counted through its first
pending hole push. -/
noncomputable def openHoles (w : List (α × Op n Γ)) (x : ℕ) : ℕ :=
  {q | OpenHolePush w x q ∧ ¬∃ p, SameHole w x p q}.ncard

/-- A sequence is `K`-hole-bounded if at most `K` holes are open at each of its positions. -/
def HoleBounded (K : ℕ) (w : List (α × Op n Γ)) : Prop :=
  ∀ x < w.length, openHoles w x ≤ K

theorem HoleBounded.mono {K K' : ℕ} {w : List (α × Op n Γ)} (h : HoleBounded K w)
    (hK : K ≤ K') : HoleBounded K' w :=
  fun x hx => (h x hx).trans hK

/-! ## Well-nested sequences have no holes -/

/-- Every push of a well-nested sequence is closed by a well-nested continuation. -/
theorem WellNested.exists_wellMatched {w : List (α × Op n Γ)} (hw : WellNested w) {p : ℕ}
    {i : Fin n} (hp : IsPushOn w i p) : WellMatched w p := by
  obtain ⟨a, γ, hp⟩ := hp
  induction hw generalizing p with
  | nil => simp at hp
  | nop _ ih =>
    cases p with
    | zero => simp at hp
    | succ p =>
      rw [List.getElem?_cons_succ] at hp
      obtain ⟨m, hm, hf⟩ := ih hp
      refine ⟨m + 1, (matches_cons_succ _ _ _ _).mpr hm, ?_⟩
      rw [factor_cons_succ]
      exact hf
  | @pushPop a' b j γ' u u' hu _ ih ih' =>
    have e : u ++ (b, Op.pop j γ') :: u' = (u ++ [(b, Op.pop j γ')]) ++ u' := by simp
    have el : (u ++ [(b, Op.pop j γ')]).length = u.length + 1 := by simp
    cases p with
    | zero =>
      have hf : factor ((a', Op.push j γ') :: (u ++ (b, Op.pop j γ') :: u')) 1 (u.length + 1)
          = u := by
        simp [factor]
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq, Op.push.injEq] at hp
      obtain ⟨rfl, rfl, rfl⟩ := hp
      refine ⟨u.length + 1, ⟨by omega, j, ⟨a', γ', rfl⟩, ⟨b, γ', by simp⟩, ?_, ?_⟩, ?_⟩
      · rw [hf]
        exact hu.net_take_nonneg j
      · rw [hf]
        exact hu.net_eq_zero j
      · have : factor ((a', Op.push j γ') :: (u ++ (b, Op.pop j γ') :: u')) 0 (u.length + 1 + 1)
            = (a', Op.push j γ') :: (u ++ [(b, Op.pop j γ')]) := by
          simp [factor, List.take_append]
        rw [this]
        exact .pushPop hu .nil
    | succ p =>
      rw [List.getElem?_cons_succ] at hp
      rcases Nat.lt_or_ge p u.length with h | h
      · rw [List.getElem?_append_left h] at hp
        obtain ⟨m, hm, hf⟩ := ih hp
        have hmu := hm.lt_length
        refine ⟨m + 1, (matches_cons_succ _ _ _ _).mpr (hm.append_right _), ?_⟩
        rw [factor_cons_succ, factor_append_right _ _ (by omega)]
        exact hf
      · rcases Nat.eq_or_lt_of_le h with h | h
        · subst h
          simp at hp
        · obtain ⟨q, rfl⟩ : ∃ q, p = u.length + 1 + q := ⟨p - (u.length + 1), by omega⟩
          have hp' : u'[q]? = some (a, .push i γ) := by
            rw [e, List.getElem?_append_right (by rw [el]; omega), el,
              show u.length + 1 + q - (u.length + 1) = q by omega] at hp
            exact hp
          obtain ⟨m, hm, hf⟩ := ih' hp'
          refine ⟨u.length + 1 + m + 1, ?_, ?_⟩
          · rw [matches_cons_succ, e]
            have := (matches_append_left (u ++ [(b, Op.pop j γ')]) u' q m).mpr hm
            rw [el] at this
            exact this
          · have := factor_append_left (u ++ [(b, Op.pop j γ')]) u' q (m + 1)
            rw [el] at this
            rw [factor_cons_succ, e, show u.length + 1 + m + 1 = u.length + 1 + (m + 1) by omega,
              this]
            exact hf

/-- A well-nested sequence has no hole pushes. -/
theorem WellNested.not_holePush {w : List (α × Op n Γ)} (hw : WellNested w) (p : ℕ) :
    ¬HolePush w p :=
  fun ⟨⟨_, hp⟩, hnot⟩ => hnot (hw.exists_wellMatched hp)

/-- Well-nested sequences are `0`-hole-bounded. -/
theorem WellNested.holeBounded_zero {w : List (α × Op n Γ)} (hw : WellNested w) :
    HoleBounded 0 w := by
  intro x _
  have : {q | OpenHolePush w x q ∧ ¬∃ p, SameHole w x p q} = ∅ := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    exact fun ⟨⟨hq, _⟩, _⟩ => hw.not_holePush q hq
  rw [openHoles, this, Set.ncard_empty]

end Cslib.Automata.MPDA
