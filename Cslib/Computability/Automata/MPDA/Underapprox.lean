/-
Copyright (c) 2026 Sparsa Roychowdhury. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sparsa Roychowdhury
-/

module

public import Cslib.Computability.Automata.MPDA.WellNested

/-! # Underapproximations of multistack pushdown automata

Reachability for multistack pushdown automata is undecidable, so verification focuses on
restricted classes of runs. This file defines the classes studied in
[AkshayGastinKrishnaRoychowdhury2020] on sequences of transition labels:

- `MPDA.ContextBounded`: at most `K` contexts, where a context uses at most one stack.
- `MPDA.RoundBounded`: at most `K` rounds, where a round is one context per stack, in order.
- `MPDA.PhaseBounded`: at most `K` phases, where a phase pops from at most one stack.
- `MPDA.ScopeBounded`: every push and its matching pop are at most `K` context switches apart.

Hole-bounded sequences are defined in `Cslib.Computability.Automata.MPDA.Holes`.

## Main statements

- `MPDA.Splits.of_isInfix`: a bounded splitting into factors with an infix-closed property
  restricts to any infix.
- `MPDA.RoundBounded.contextBounded`: `K` rounds give at most `K * n` contexts.
- `MPDA.ContextBounded.phaseBounded`: `K` contexts give at most `K` phases.
- `MPDA.ContextBounded.scopeBounded`: the first inclusion of Proposition 2(a) of
  [AkshayGastinKrishnaRoychowdhury2020].

## Implementation notes

Positions are `0`-indexed. Matching between a push and a pop is defined by counting the pushes and
pops of the relevant stack in between, so it does not depend on the stack symbols. On runs of an
MPDA the symbols of matching pushes and pops coincide.

## References

* [S. Akshay, P. Gastin, S. Krishna, S. Roychowdhury,
  *Revisiting Underapproximate Reachability for Multipushdown Systems*]
  [AkshayGastinKrishnaRoychowdhury2020]
-/

@[expose] public section

namespace Cslib.Automata.MPDA

variable {n : ℕ} {Γ α β : Type*}

/-! ## Bounded splittings -/

/-- `Splits P K w` holds when `w` is the concatenation of at most `K` factors satisfying `P`. -/
def Splits (P : List β → Prop) (K : ℕ) (w : List β) : Prop :=
  ∃ ws : List (List β), ws.length ≤ K ∧ ws.flatten = w ∧ ∀ v ∈ ws, P v

namespace Splits

variable {P Q : List β → Prop} {K K' : ℕ} {w : List β}

theorem nil (P : List β → Prop) (K : ℕ) : Splits P K [] := ⟨[], Nat.zero_le _, rfl, by simp⟩

theorem of_prop (h : P w) (hK : 1 ≤ K) : Splits P K w := ⟨[w], hK, by simp, by simpa using h⟩

theorem mono_bound (h : Splits P K w) (hK : K ≤ K') : Splits P K' w :=
  let ⟨ws, hlen, hw, hP⟩ := h
  ⟨ws, hlen.trans hK, hw, hP⟩

theorem mono (h : Splits P K w) (hPQ : ∀ v, P v → Q v) : Splits Q K w :=
  let ⟨ws, hlen, hw, hP⟩ := h
  ⟨ws, hlen, hw, fun v hv => hPQ v (hP v hv)⟩

/-- Splitting each factor of a splitting yields a splitting. -/
theorem flatten_of_forall {m : ℕ} :
    ∀ ws : List (List β), (∀ v ∈ ws, Splits P m v) → Splits P (ws.length * m) ws.flatten
  | [], _ => nil P _
  | v :: ws, h => by
    obtain ⟨us, hlen, rfl, hP⟩ := h v List.mem_cons_self
    obtain ⟨us', hlen', hw', hP'⟩ :=
      flatten_of_forall ws fun v hv => h v (List.mem_cons_of_mem _ hv)
    refine ⟨us ++ us', ?_, ?_, ?_⟩
    · rw [List.length_append, List.length_cons, Nat.succ_mul]
      omega
    · rw [List.flatten_append, hw', List.flatten_cons]
    · intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · exact hP u hu
      · exact hP' u hu

/-- A splitting into factors that themselves split boundedly gives a bounded splitting. -/
theorem trans {m : ℕ} (h : Splits (Splits P m) K w) : Splits P (K * m) w := by
  obtain ⟨ws, hlen, rfl, hP⟩ := h
  exact (flatten_of_forall ws hP).mono_bound (Nat.mul_le_mul_right m hlen)

private theorem prefix_aux (hP : ∀ u v, u <+: v → P v → P u) :
    ∀ (ws : List (List β)) (u : List β), (∀ v ∈ ws, P v) → u <+: ws.flatten →
      ∃ us : List (List β), us.length ≤ ws.length ∧ us.flatten = u ∧ ∀ v ∈ us, P v
  | [], u, _, hu => ⟨[], le_rfl, (List.prefix_nil.mp hu).symm, by simp⟩
  | v :: ws, u, hws, ⟨t, ht⟩ => by
    rw [List.flatten_cons] at ht
    rcases List.append_eq_append_iff.mp ht with ⟨a, rfl, -⟩ | ⟨c, rfl, hc⟩
    · exact ⟨[u], by simp, by simp,
        by simpa using hP u (u ++ a) (List.prefix_append u a) (hws _ List.mem_cons_self)⟩
    · obtain ⟨us, hlen, rfl, hus⟩ := prefix_aux hP ws c
        (fun v hv => hws v (List.mem_cons_of_mem _ hv)) ⟨t, hc.symm⟩
      refine ⟨v :: us, by simpa using hlen, by simp, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hws _ List.mem_cons_self
      · exact hus x hx

private theorem suffix_aux (hP : ∀ u v, u <:+ v → P v → P u) :
    ∀ (ws : List (List β)) (u : List β), (∀ v ∈ ws, P v) → u <:+ ws.flatten →
      ∃ us : List (List β), us.length ≤ ws.length ∧ us.flatten = u ∧ ∀ v ∈ us, P v
  | [], u, _, hu => ⟨[], le_rfl, (List.suffix_nil.mp hu).symm, by simp⟩
  | v :: ws, u, hws, ⟨t, ht⟩ => by
    rw [List.flatten_cons] at ht
    rcases List.append_eq_append_iff.mp ht with ⟨a, rfl, rfl⟩ | ⟨c, rfl, hc⟩
    · refine ⟨a :: ws, by simp, by simp, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hP x (t ++ x) (List.suffix_append t x) (hws _ List.mem_cons_self)
      · exact hws x (List.mem_cons_of_mem _ hx)
    · obtain ⟨us, hlen, rfl, hus⟩ := suffix_aux hP ws u
        (fun v hv => hws v (List.mem_cons_of_mem _ hv)) ⟨c, hc.symm⟩
      exact ⟨us, by simp only [List.length_cons]; omega, rfl, hus⟩

/-- If `P` is closed under taking infixes, so is having a splitting into at most `K` factors
satisfying `P`. -/
theorem of_isInfix (hP : ∀ u v, u <:+: v → P v → P u) (h : Splits P K w) {u : List β}
    (hu : u <:+: w) : Splits P K u := by
  obtain ⟨ws, hlen, rfl, hws⟩ := h
  obtain ⟨t, ht, hts⟩ := List.infix_iff_prefix_suffix.mp hu
  obtain ⟨vs, hvlen, rfl, hvs⟩ :=
    suffix_aux (fun u v h => hP u v h.isInfix) ws t hws hts
  obtain ⟨us, hulen, rfl, hus⟩ :=
    prefix_aux (fun u v h => hP u v h.isInfix) vs _ hvs ht
  exact ⟨us, (hulen.trans hvlen).trans hlen, rfl, hus⟩

end Splits

/-! ## Contexts, rounds and phases -/

/-- The stack touched by an operation, if any. -/
def Op.stack : Op n Γ → Option (Fin n)
  | .nop => none
  | .push i _ => some i
  | .pop i _ => some i

/-- The stack popped by an operation, if any. -/
def Op.popStack : Op n Γ → Option (Fin n)
  | .pop i _ => some i
  | _ => none

/-- Every operation of `w` touches stack `i` or no stack. -/
def IsContextOf (i : Fin n) (w : List (α × Op n Γ)) : Prop :=
  ∀ μ ∈ w, μ.2.stack = none ∨ μ.2.stack = some i

/-- A context is a sequence of transitions that uses at most one stack. -/
def IsContext (w : List (α × Op n Γ)) : Prop :=
  ∃ o : Option (Fin n), ∀ μ ∈ w, μ.2.stack = none ∨ μ.2.stack = o

/-- A phase is a sequence of transitions that pops from at most one stack. Pushes are
unrestricted. -/
def IsPhase (w : List (α × Op n Γ)) : Prop :=
  ∃ o : Option (Fin n), ∀ μ ∈ w, μ.2.popStack = none ∨ μ.2.popStack = o

/-- A round is a sequence of contexts for stacks `0, …, n - 1`, in this order. Each context may be
empty. -/
def IsRound (w : List (α × Op n Γ)) : Prop :=
  ∃ vs : Fin n → List (α × Op n Γ), (List.ofFn vs).flatten = w ∧ ∀ i, IsContextOf i (vs i)

/-- At most `K` contexts. -/
def ContextBounded (K : ℕ) (w : List (α × Op n Γ)) : Prop := Splits IsContext K w

/-- At most `K` rounds. -/
def RoundBounded (K : ℕ) (w : List (α × Op n Γ)) : Prop := Splits IsRound K w

/-- At most `K` phases. -/
def PhaseBounded (K : ℕ) (w : List (α × Op n Γ)) : Prop := Splits IsPhase K w

theorem IsContextOf.isContext {i : Fin n} {w : List (α × Op n Γ)} (h : IsContextOf i w) :
    IsContext w :=
  ⟨some i, h⟩

theorem IsContext.isPhase {w : List (α × Op n Γ)} (h : IsContext w) : IsPhase w := by
  obtain ⟨o, ho⟩ := h
  refine ⟨o, fun μ hμ => ?_⟩
  obtain ⟨a, op⟩ := μ
  rcases ho _ hμ with h | h <;> cases op <;> simp_all [Op.stack, Op.popStack]

theorem IsContext.of_isInfix {u w : List (α × Op n Γ)} (hu : u <:+: w) (h : IsContext w) :
    IsContext u :=
  let ⟨o, ho⟩ := h
  ⟨o, fun μ hμ => ho μ (hu.subset hμ)⟩

theorem IsRound.contextBounded {w : List (α × Op n Γ)} (h : IsRound w) : ContextBounded n w := by
  obtain ⟨vs, rfl, hvs⟩ := h
  refine ⟨List.ofFn vs, by simp, rfl, ?_⟩
  intro v hv
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
  exact (hvs i).isContext

/-- `K` rounds give at most `K * n` contexts. -/
theorem RoundBounded.contextBounded {K : ℕ} {w : List (α × Op n Γ)} (h : RoundBounded K w) :
    ContextBounded (K * n) w :=
  (h.mono fun _ hv => hv.contextBounded).trans

/-- `K` contexts give at most `K` phases. -/
theorem ContextBounded.phaseBounded {K : ℕ} {w : List (α × Op n Γ)} (h : ContextBounded K w) :
    PhaseBounded K w :=
  Splits.mono h fun _ hv => hv.isPhase

theorem ContextBounded.of_isInfix {K : ℕ} {u w : List (α × Op n Γ)} (h : ContextBounded K w)
    (hu : u <:+: w) : ContextBounded K u :=
  Splits.of_isInfix (fun _ _ huv hv => hv.of_isInfix huv) h hu

/-! ## Matching pushes and pops -/

/-- The effect of an operation on the height of stack `i`. -/
def Op.net (i : Fin n) : Op n Γ → ℤ
  | .nop => 0
  | .push j _ => if j = i then 1 else 0
  | .pop j _ => if j = i then -1 else 0

/-- The net change of the height of stack `i` along a sequence of transitions. -/
def net (i : Fin n) (w : List (α × Op n Γ)) : ℤ := (w.map fun μ => μ.2.net i).sum

/-- The factor of `w` between positions `a` (included) and `b` (excluded). -/
def factor (w : List β) (a b : ℕ) : List β := (w.drop a).take (b - a)

theorem factor_infix (w : List β) (a b : ℕ) : factor w a b <:+: w :=
  (List.take_prefix _ _).isInfix.trans (List.drop_suffix _ _).isInfix

/-- The push at position `p` of `w` is matched by the pop at position `m`: they act on the same
stack `i`, and the factor strictly between them never pops below its initial height of stack `i`
and returns to it. -/
def Matches (w : List (α × Op n Γ)) (p m : ℕ) : Prop :=
  p < m ∧ ∃ i : Fin n, (∃ a γ, w[p]? = some (a, .push i γ)) ∧ (∃ b γ, w[m]? = some (b, .pop i γ)) ∧
    (∀ k, 0 ≤ net i ((factor w (p + 1) m).take k)) ∧ net i (factor w (p + 1) m) = 0

/-- The push at position `p` of `w` is pending at position `x`: it occurs at or before `x`, and it
has not been popped by position `x`. -/
def PendingAt (w : List (α × Op n Γ)) (p x : ℕ) : Prop :=
  p ≤ x ∧ x < w.length ∧ ∃ i : Fin n, (∃ a γ, w[p]? = some (a, .push i γ)) ∧
    ∀ k, 0 ≤ net i ((factor w (p + 1) (x + 1)).take k)

/-! ## Scope-bounded sequences -/

/-- A sequence is `K`-scope-bounded if every push and its matching pop are separated by at most `K`
context switches, that is, the factor from the push to the pop splits into at most `K + 1`
contexts. -/
def ScopeBounded (K : ℕ) (w : List (α × Op n Γ)) : Prop :=
  ∀ p m, Matches w p m → ContextBounded (K + 1) (factor w p (m + 1))

/-- Proposition 2(a) of [AkshayGastinKrishnaRoychowdhury2020], first inclusion: a sequence with at
most `K` contexts is `K`-scope-bounded. -/
theorem ContextBounded.scopeBounded {K : ℕ} {w : List (α × Op n Γ)} (h : ContextBounded K w) :
    ScopeBounded K w :=
  fun p m _ => (h.of_isInfix (factor_infix w p (m + 1))).mono_bound (Nat.le_succ K)

/-- A sequence with at most `K` rounds is `K * n`-scope-bounded. -/
theorem RoundBounded.scopeBounded {K : ℕ} {w : List (α × Op n Γ)} (h : RoundBounded K w) :
    ScopeBounded (K * n) w :=
  h.contextBounded.scopeBounded

end Cslib.Automata.MPDA
