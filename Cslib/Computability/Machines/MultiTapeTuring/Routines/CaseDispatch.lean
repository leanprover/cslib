/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.StructuralMachines
public import Cslib.Computability.Machines.MultiTapeTuring.TapeView
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.Navigation

namespace Turing
namespace Routines

-- ═══════════════════════════════════════════════════════════════════════════
-- Case dispatch
-- ═══════════════════════════════════════════════════════════════════════════

/-- TODO document -/
public def ite_enc {k : ℕ} (v : List Char) (i : Fin k) (then_branch else_branch : MultiTapeTM k Char) :
  MultiTapeTM k Char := match v with
    | [] => then_branch
    | c :: cs => if_eq c i
        (right i;ₜ ite_enc cs i (left i;ₜ then_branch) (left i;ₜ else_branch))
        else_branch

@[simp]
public lemma ite_enc.eval {k : ℕ} {v : List Char} {i : Fin k}
    {then_branch else_branch : MultiTapeTM k Char}
    {tapes : Fin k → BiTape Char} :
    (ite_enc v i then_branch else_branch).eval tapes =
      if ∀ n, (h : n < v.length) → (BiTape.move_right^[n] (tapes i)).head = some v[n] then
        then_branch.eval tapes
      else
        else_branch.eval tapes := by
  induction v generalizing tapes then_branch else_branch with
  | nil => simp [ite_enc]
  | cons c cs ih =>
    simp only [ite_enc, if_eq.eval]
    by_cases h : (tapes i).head = some c
    · simp only [h, ↓reduceIte, MultiTapeTM.seq_eval, right.eval, Part.bind_some, Part.bind_eq_bind]
      rw [ih]
      simp only [MultiTapeTM.seq_eval, left.eval, Part.bind_some, Part.bind_eq_bind,
        Function.update_self, Function.update_idem,
        BiTape.move_right_move_left, Function.update_eq_self]
      congr 1
      ext
      constructor <;> intro h' n hn
      · match n with
        | 0 => simpa using h
        | n + 1 => simpa [Function.iterate_succ] using h' n (by simp_all)
      · simpa [Function.iterate_succ] using h' (n + 1) (by simp_all)
    · simp only [h, ↓reduceIte]
      have : ¬∀ n, (hn : n < (c :: cs).length) →
          (BiTape.move_right^[n] (tapes i)).head = some (c :: cs)[n] := by
        intro h'; exact h (by simpa using h' 0 (by simp))
      exact (if_neg this).symm

/-- Runs `then_branch` if `(views i).current = v`, otherwise `else_branch`. -/
public def ite {k : ℕ} (v : Data) (i : Fin k) (then_branch else_branch : MultiTapeTM k Char) :
  MultiTapeTM k Char := ite_enc v.enc i then_branch else_branch

@[simp]
public lemma ite.eval_struct {k : ℕ} {v : Data} {i : Fin k}
    {then_branch else_branch : MultiTapeTM k Char}
    {views : Fin k → TapeView} :
    (ite v i then_branch else_branch).eval_struct views =
      if (views i).current = v then
        then_branch.eval_struct views
      else
        else_branch.eval_struct views := by -- TODO clean up (ai)
  -- simp only [ite, MultiTapeTM.eval_struct, ite_enc.eval, Function.comp_apply,
  --   TapeView.ite_enc_condition_iff]
  -- split <;> rfl
  sorry

/-- Dispatch on the numeric value of an encoding.
    Reads the number `n` and runs `branches[n]`.
    The head stays at the start of the encoding. -/
public def case_num {k : ℕ} (i : Fin k)
    (branches : List (MultiTapeTM k Char)) : MultiTapeTM k Char := sorry

/-- `case_num i branches` dispatches on the numeric value at the current position
    of tape `i`. If `currentNum` is `some n` and `n < branches.length`, runs
    `branches[n]`. Otherwise (tape empty, not a num, or out of range), does nothing. -/
@[simp]
public lemma case_num_eval_struct {k : ℕ} {i : Fin k}
    {branches : List (MultiTapeTM k Char)}
    {views : Fin k → TapeView} :
    (case_num i branches).eval_struct views =
      match StrEnc.fromData (views i).current with
      | some (n : ℕ) => if h : n < branches.length then branches[n].eval_struct views else some views
      | _ => some views := by sorry

/-- Dispatch on the numeric value of the first element of a list.
    Pops the first element from the list on tape `i`. If it is `Data.num n`
    and `n < branches.length`, runs `branches[n]` on the updated views
    (with the element removed). If the pop fails, the element is not a number,
    or the index is out of range, leaves the tape unmodified. -/
public def case_popList_num {k : ℕ} (i : Fin k)
    (branches : List (MultiTapeTM k Char)) : MultiTapeTM k Char := sorry

@[simp]
public lemma case_popList_num_eval_struct {k : ℕ} {i : Fin k}
    {branches : List (MultiTapeTM k Char)}
    {views : Fin k → TapeView} :
    (case_popList_num i branches).eval_struct views = match views i with
      | ⟨Data.list (n :: ds), [], .leftEnd, _⟩ => match StrEnc.fromData n with
        | some (n : ℕ) => if h_n : n < branches.length then
            branches[n].eval_struct (Function.update views i (.ofList ds))
          else
            .some views
        | _ => .some views
      | _ => .some views := by sorry

/-- Runs `then_branch` if tape `i` points at a list whose head is `v`, otherwise
runs `else_branch`. -/
public def ite_list_head {k : ℕ} {α : Type} [StrEnc α] (i : Fin k)
    (v : α) (then_branch else_branch : MultiTapeTM k Char) : MultiTapeTM k Char := sorry

@[simp]
public lemma ite_list_head_eval_struct {k : ℕ} {α : Type} [StrEnc α] {i : Fin k}
    (v : α)
    (then_branch else_branch : MultiTapeTM k Char) :
    ∀ (ls : List Data) (views : Fin k → TapeView),
    (views i = TapeView.ofList ls) →
    (ite_list_head i v then_branch else_branch).eval_struct views =
      if ls.head? = some (StrEnc.toData v) then
        then_branch.eval_struct views
      else
        else_branch.eval_struct views := by sorry

end Routines
end Turing
