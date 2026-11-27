/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.SymmetricCycles
public import Mathlib.Data.Nat.Pairing

/-!
# Finite networks for symmetric cycle tables

Vertices are natural numbers. At stage `n`, the first `n` vertices form a consistently
labelled complete graph. Each step supplies a witness for one composition request. Pairing the
endpoints with the request index bounds the witness vertex independently of the table.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.SymmetricCycles

variable {α : Type*} {T : Table α}

/-- A symmetric labelling of edges, consistent on the first `n` distinct vertices. -/
structure Network (T : Table α) (n : ℕ) where
  /-- Diversity labels on edges between distinct vertices. -/
  edge : ℕ → ℕ → α
  symm : ∀ i j, edge i j = edge j i
  triangle : ∀ i < n, ∀ j < n, ∀ k < n, i ≠ j → i ≠ k → j ≠ k →
    edge i k ::ₛ pair (edge i j) (edge j k) ∈ T

namespace Network

variable {n : ℕ}

/-- Use the identity atom exactly on the diagonal. -/
def atom (N : Network T n) (i j : ℕ) : Option α :=
  if i = j then none else some (N.edge i j)

theorem atom_symm (N : Network T n) (i j : ℕ) : N.atom i j = N.atom j i := by
  by_cases h : i = j
  · subst j; rfl
  · simp [atom, h, Ne.symm h, N.symm i j]

theorem cycle_atom (N : Network T n) {i j k : ℕ} (hi : i < n) (hj : j < n) (hk : k < n) :
    cycle T (N.atom i j) (N.atom j k) (N.atom i k) := by
  by_cases hij : i = j
  · subst j
    simp [atom, cycle]
  by_cases hik : i = k
  · subst k
    simp [atom, hij, Ne.symm hij, cycle, N.symm i j]
  by_cases hjk : j = k
  · subst k
    simp [atom, hij, cycle]
  simpa [atom, hij, hik, hjk, cycle] using N.triangle i hi j hj k hk hij hik hjk

private def initial (a : α) : Network T 2 where
  edge _ _ := a
  symm _ _ := rfl
  triangle := by intros; omega

/-- If the label on `(i, j)` belongs to the product of `R` and `S`, some vertex below `bound`
realizes the two factors. -/
def Meets (N : Network T n) (bound i j : ℕ) (R S : Set (Option α)) : Prop :=
  (∃ r ∈ R, ∃ s ∈ S, cycle T r s (N.atom i j)) →
    ∃ v < bound, N.atom i v ∈ R ∧ N.atom v j ∈ S

private theorem add_vertex (N : Network T n) (d : ℕ → α)
    (hd : ∀ i < n, ∀ j < n, i ≠ j → d i ::ₛ pair (d j) (N.edge i j) ∈ T) :
    ∃ M : Network T (n + 1), (∀ i < n, ∀ j < n, M.atom i j = N.atom i j) ∧
      ∀ i < n, M.atom i n = some (d i) := by
  let edge (i j : ℕ) := if i = n then d j else if j = n then d i else N.edge i j
  have hsym (i j) : edge i j = edge j i := by
    by_cases hi : i = n <;> by_cases hj : j = n <;> simp_all [edge, N.symm i j]
  have htri (i) (hi : i < n + 1) (j) (hj : j < n + 1) (k) (hk : k < n + 1)
      (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      edge i k ::ₛ pair (edge i j) (edge j k) ∈ T := by
    by_cases hin : i = n
    · subst i
      simpa [edge, hij.symm, hik.symm, N.symm j k] using hd k (by omega) j (by omega) hjk.symm
    by_cases hjn : j = n
    · subst j
      have h := hd i (by omega) k (by omega) hik
      simpa only [edge, ite_eq_right hin, ite_eq_right hjk.symm, ite_true, ite_eq_left rfl, pair,
        Sym.cons_swap (N.edge i k) (d i), Sym.cons_swap (N.edge i k) (d k)] using h
    by_cases hkn : k = n
    · subst k
      simpa only [edge, ite_eq_right hin, ite_eq_right hjn, ite_true, ite_eq_left rfl, pair,
        Sym.cons_swap (N.edge i j) (d j)]
        using hd i (by omega) j (by omega) hij
    simpa [edge, hin, hjn, hkn] using
      N.triangle i (by omega) j (by omega) k (by omega) hij hik hjk
  let M : Network T (n + 1) := ⟨edge, hsym, htri⟩
  exact ⟨M, fun i hi j hj => by simp [M, atom, edge, hi.ne, hj.ne],
    fun i hi => by simp [M, atom, edge, hi.ne]⟩

private theorem extend (N : Network T n) {k : ℕ} (hT : HasCommonWitnesses k T) (hn : n ≤ k + 1)
    (i j : Fin n) (R S : Set (Option α)) :
    ∃ M : Network T (n + 1), (∀ a < n, ∀ b < n, M.atom a b = N.atom a b) ∧
      M.Meets (n + 1) i j R S := by
  classical
  let A := N.atom i j
  -- When one factor is the identity, the corresponding endpoint already witnesses the product.
  by_cases fresh : ∃ a b : α, some a ∈ R ∧ some b ∈ S ∧ cycle T (some a) (some b) A
  · obtain ⟨a,b,ha,hb,hab⟩ := fresh
    let c (v : Fin n) := if v = i then a else b
    have hc : ∀ u ∈ ({i,j} : Finset (Fin n)), ∀ v ∈ ({i,j} : Finset (Fin n)), u ≠ v →
        c u ::ₛ pair (c v) (N.edge u v) ∈ T := by
      intro u hu v hv huv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> try contradiction
      · have hn : (u : ℕ) ≠ v := fun he => huv (Fin.ext he)
        simpa only [c, ite_true, ite_eq_left rfl,
          ite_eq_right huv.symm, A, atom, ite_eq_right hn, cycle, pair,
          Sym.cons_swap (N.edge u v) a, Sym.cons_swap (N.edge u v) b] using hab
      · have hn : (v : ℕ) ≠ u := fun he => huv.symm (Fin.ext he)
        simpa only [c, ite_true, ite_eq_left rfl,
          ite_eq_right huv, A, atom, ite_eq_right hn, cycle, N.symm v u, pair,
          Sym.cons_swap (N.edge u v) a, Sym.cons_swap (N.edge u v) b, Sym.cons_swap a b] using hab
    obtain ⟨d, hd, ht⟩ := hT.extend (by simpa using hn) (fun u v : Fin n => N.edge u v)
      (fun u v => N.symm u v) {i,j} c hc
    let d' (v : ℕ) := if h : v < n then d ⟨v,h⟩ else a
    obtain ⟨M, hold, hnew⟩ := N.add_vertex d' (fun u hu v hv huv => by
      simpa [d', hu, hv] using ht ⟨u,hu⟩ ⟨v,hv⟩ (fun h => huv (congrArg Fin.val h)))
    refine ⟨M, hold, fun _ => ⟨n, by omega, ?_, ?_⟩⟩
    · simpa [hnew i i.isLt, d', i.isLt, hd i (by simp), c] using ha
    · rw [M.atom_symm n j, hnew j j.isLt]
      by_cases hij : j = i
      · subst j
        have he : a = b := by simpa [A, atom, cycle] using hab
        simpa [d', i.isLt, hd i (by simp), c, he] using hb
      · simpa [d', j.isLt, hd j (by simp), c, hij] using hb
  · let c (_ : Fin n) := N.edge i j
    obtain ⟨d, _, ht⟩ := hT.extend (by simpa using hn) (fun u v : Fin n => N.edge u v)
      (fun u v => N.symm u v) ∅ c (by simp)
    let d' (v : ℕ) := if h : v < n then d ⟨v,h⟩ else N.edge i j
    obtain ⟨M, hold, _⟩ := N.add_vertex d' (fun u hu v hv huv => by
      simpa [d', hu, hv] using ht ⟨u,hu⟩ ⟨v,hv⟩ (fun h => huv (congrArg Fin.val h)))
    refine ⟨M, hold, ?_⟩
    rintro ⟨r, hr, s, hs, h⟩
    rw [hold i i.isLt j j.isLt] at h
    cases r with
    | none =>
      have he : s = N.atom i j := h
      exact ⟨i, by omega, by simpa [atom] using hr, by rwa [hold i i.isLt j j.isLt, ← he]⟩
    | some r =>
      cases s with
      | none =>
        have he : some r = N.atom i j := h
        exact ⟨j, by omega, by rwa [hold i i.isLt j j.isLt, ← he], by simpa [atom] using hs⟩
      | some s => exact False.elim (fresh ⟨r,s,hr,hs,h⟩)

private def left (t : ℕ) := t.unpair.1.unpair.1
private def right (t : ℕ) := t.unpair.1.unpair.2
private def request (t : ℕ) := t.unpair.2

private theorem left_le (t : ℕ) : left t ≤ t :=
  (Nat.unpair_left_le _).trans (Nat.unpair_left_le _)

private theorem right_le (t : ℕ) : right t ≤ t :=
  (Nat.unpair_right_le _).trans (Nat.unpair_left_le _)

private theorem build {k : ℕ} (hT : HasCommonWitnesses k T) (seed : α)
    (R S : ℕ → Set (Option α)) (l : ℕ) (hl : l ≤ k) :
    ∃ N : Network T (l + 2), N.atom 0 1 = some seed ∧
      ∀ t < l, N.Meets (t + 3) (left t) (right t) (R (request t)) (S (request t)) := by
  induction l with
  | zero => exact ⟨initial seed, rfl, by simp⟩
  | succ l ih =>
    obtain ⟨N, hseed, hmeet⟩ := ih (by omega)
    let i : Fin (l + 2) := ⟨left l, by have := left_le l; omega⟩
    let j : Fin (l + 2) := ⟨right l, by have := right_le l; omega⟩
    obtain ⟨M, hold, hnew⟩ := N.extend hT (by omega) i j (R (request l)) (S (request l))
    refine ⟨M, (hold 0 (by omega) 1 (by omega)).trans hseed, fun t ht => ?_⟩
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ ht) with hlt | rfl
    · have hi : left t < l + 2 := by have := left_le t; omega
      have hj : right t < l + 2 := by have := right_le t; omega
      intro h
      rw [hold _ hi _ hj] at h
      obtain ⟨v,hv,h₁,h₂⟩ := hmeet t hlt h
      exact ⟨v,hv, by rwa [hold _ hi v (by omega)], by rwa [hold v (by omega) _ hj]⟩
    · exact hnew

/-- The network of size `k + 2` meets every request scheduled before stage `k`.
The witness bound depends only on the endpoints and the request index. -/
theorem exists_meeting_requests {k : ℕ} (hT : HasCommonWitnesses k T) (seed : α)
    (R S : ℕ → Set (Option α)) :
    ∃ N : Network T (k + 2), N.atom 0 1 = some seed ∧ ∀ i j t,
      Nat.pair (Nat.pair i j) t < k →
      N.Meets (Nat.pair (Nat.pair i j) t + 3) i j (R t) (S t) := by
  obtain ⟨N, hs, ht⟩ := build hT seed R S k le_rfl
  exact ⟨N, hs, fun i j t h => by simpa [left, right, request] using ht _ h⟩

end Network
end Cslib.RelationAlgebra.SymmetricCycles
