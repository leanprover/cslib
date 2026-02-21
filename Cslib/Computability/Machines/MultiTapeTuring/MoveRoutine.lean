/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Basic

namespace Turing

namespace Routines

variable [Inhabited α] [Fintype α]

/-- A 1-tape Turing machine that moves its head in a given direction
once and then halts. -/
public def move (dir : Dir) : MultiTapeTM 1 α where
  Λ := PUnit
  q₀ := 0
  M _ syms := (fun i => ⟨syms i, some dir⟩, none)

@[simp]
public lemma move_eval (tape : BiTape α) (dir : Turing.Dir) :
  (move dir).eval (fun _ => tape) = .some (fun _ => tape.move dir) := by
  rw [MultiTapeTM.eval_iff_exists_steps_iter_eq_some]
  use 1
  rfl

/-- A 1-tape Turing machine that moves its head in a given direction until a condition
on the read symbol is met. -/
public def move_until (dir : Turing.Dir) (cond : (Option α) → Bool) : MultiTapeTM 1 α where
  Λ := PUnit
  q₀ := PUnit.unit
  M q syms := match cond (syms 0) with
    | false  => (fun _ => ⟨syms 0, some dir⟩, some q)
    | true => (fun _ => ⟨syms 0, none⟩, none)

lemma move_until_step_cond_false
  {tape : BiTape α}
  {stop_condition : Option α → Bool}
  (h_neg_stop : ¬ stop_condition tape.head) :
  (move_until .right stop_condition).step
    ⟨some (move_until .right stop_condition).q₀, (fun _ => tape)⟩ =
    some ⟨some (move_until .right stop_condition).q₀, (fun _ => tape.move .right)⟩ := by
  simp [move_until, h_neg_stop, BiTape.optionMove, MultiTapeTM.step]

lemma move_until_step_cond_true
  {tape : BiTape α}
  {stop_condition : Option α → Bool}
  (h_neg_stop : stop_condition tape.head) :
  (move_until .right stop_condition).step
    ⟨some (move_until .right stop_condition).q₀, (fun _ => tape)⟩ =
    some ⟨none, (fun _ => tape)⟩ := by
  simp [move_until, h_neg_stop, BiTape.optionMove, MultiTapeTM.step]

public theorem move_until.right_semantics
  (tape : BiTape α)
  (stop_condition : Option α → Bool)
  (h_stop : ∃ n : ℕ, stop_condition (tape.nth n)) :
  (move_until .right stop_condition).eval (fun _ => tape) =
    .some (fun _ => tape.move_int (Nat.find h_stop)) := by
  rw [MultiTapeTM.eval_iff_exists_steps_iter_eq_some]
  let n := Nat.find h_stop
  use n.succ
  have h_not_stop_of_lt : ∀ k < n, ¬ stop_condition (tape.move_int k).head := by
    intro k hk
    simp [Nat.find_min h_stop hk]
  have h_iter : ∀ k < n, (Option.bind · (move_until .right stop_condition).step)^[k]
      (some ⟨some (move_until .right stop_condition).q₀, fun _ => tape⟩) =
      some ⟨some (move_until .right stop_condition).q₀, fun _ => tape.move_int k⟩ := by
    intro k hk
    induction k with
    | zero =>
      simp [BiTape.move_int]
    | succ k ih =>
      have hk' : k < n := Nat.lt_of_succ_lt hk
      rw [Function.iterate_succ_apply', ih hk']
      simp only [Option.bind_some, move_until_step_cond_false (h_not_stop_of_lt k hk')]
      simp [BiTape.move, ← BiTape.move_int_one_eq_move_right, BiTape.move_int_move_int]
  have h_n_eq : n = Nat.find h_stop := by grind
  by_cases h_n_zero : n = 0
  · have h_stop_cond : stop_condition (tape.head) := by simp_all [n]
    let h_step := move_until_step_cond_true h_stop_cond
    simp [h_step, ← h_n_eq, h_n_zero]
  · obtain ⟨n', h_n'_eq_n_succ⟩ := Nat.exists_eq_add_one_of_ne_zero h_n_zero
    rw [h_n'_eq_n_succ, Function.iterate_succ_apply', Function.iterate_succ_apply']
    have h_n'_lt_n : n' < n := by omega
    simp only [MultiTapeTM.initCfgTapes, MultiTapeTM.haltCfgTapes]
    rw [h_iter n' h_n'_lt_n]
    simp only [Option.bind_some, move_until_step_cond_false (h_not_stop_of_lt n' h_n'_lt_n)]
    simp only [BiTape.move, ← BiTape.move_int_one_eq_move_right, BiTape.move_int_move_int]
    rw [show (n' : ℤ) + 1 = n by omega]
    have h_n_stop : stop_condition ((tape.move_int n).head) := by
      simpa [n] using Nat.find_spec h_stop
    simpa using move_until_step_cond_true h_n_stop

end Routines

end Turing
