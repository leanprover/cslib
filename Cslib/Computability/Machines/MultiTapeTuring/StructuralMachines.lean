/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Basic
public import Cslib.Computability.Machines.MultiTapeTuring.Encoding
public import Cslib.Computability.Machines.MultiTapeTuring.SequentialCombinator

namespace Turing

namespace Routines


public instance : Fintype Char := by sorry

public def right (i : Fin k) : MultiTapeTM k Char := sorry

@[simp]
public lemma right_eval {i : Fin k} {tapes : Fin k → BiTape Char} :
    (right i).eval tapes = .some
      (Function.update tapes i (tapes i).move_right) := by sorry

public def left (i : Fin k) : MultiTapeTM k Char := sorry

@[simp]
public lemma left_eval {i : Fin k} {tapes : Fin k → BiTape Char} :
    (left i).eval tapes = .some
      (Function.update tapes i (tapes i).move_left) := by sorry

public def write (c : Char) (i : Fin k) : MultiTapeTM k Char := sorry

@[simp]
public lemma write_eval {c : Char} {i : Fin k} {tapes : Fin k → BiTape Char} :
    (write c i).eval tapes = .some
      (Function.update tapes i ((tapes i).write (.some c))) := by sorry

public def noop : MultiTapeTM k Char := sorry

@[simp]
public lemma noop_eval {tapes : Fin k → BiTape Char} :
    (noop (k := k)).eval tapes = .some tapes := by sorry

public def while_eq (c : Char) (i : Fin k)  (tm : MultiTapeTM k Char) :
  MultiTapeTM k Char := sorry

@[simp]
public lemma while_eq_eval {i : Fin k} {c : Char}
  {tm : MultiTapeTM k Char}
  {tapes : Fin k → BiTape Char}
  (h_halts : ∀ tapes, tm.HaltsOn tapes) :
    (while_eq c i tm).eval tapes =
    ⟨∃ n, ((tm.eval_tot h_halts)^[n] tapes i).head ≠ .some c,
      fun h_loopEnds => (tm.eval_tot h_halts)^[Nat.find h_loopEnds] tapes⟩ := by
    sorry

public def while_neq (c : Char) (i : Fin k) (tm : MultiTapeTM k Char) :
  MultiTapeTM k Char := sorry

@[simp]
public lemma while_neq_eval {i : Fin k} {c : Char}
  {tm : MultiTapeTM k Char}
  {tapes : Fin k → BiTape Char}
  (h_halts : ∀ tapes, tm.HaltsOn tapes) :
    (while_eq c i tm).eval tapes =
    ⟨∃ n, ((tm.eval_tot h_halts)^[n] tapes i).head = .some c,
      fun h_loopEnds => (tm.eval_tot h_halts)^[Nat.find h_loopEnds] tapes⟩ := by
    sorry

-- TODO We are only
-- dealing with a _max_ depth and not an exact depth,
-- We have to check that there is an opening parenthesis!

--- Skip to the right across a StrEnc-encoded value.
def skipRight_numeric {k : ℕ} (depth : ℕ) (i : Fin k) :
    MultiTapeTM k Char :=
  match depth with
  | 0     => while_neq ')' i (right i) ;ₜ right i
  | d + 1 => while_eq '(' i (right i ;ₜ skipRight_numeric d i) ;ₜ right i

--- Skip to the right across a StrEnc-encoded value.
public def skipRight {k : ℕ} (α : Type*) [StrEnc α] (i : Fin k) :
    MultiTapeTM k Char := skipRight_numeric (StrEnc.maxDepth α) i

@[simp]
public lemma skipRight_eval {k : ℕ} {α : Type*} [StrEnc α] {i : Fin k}
  {tapes : Fin k → BiTape Char}
  {x : α}
  {l r : List Char}
  (h_hasValue : tapes i = BiTape.mk₂ l ((StrEnc.enc x) ++ r)) :
  (skipRight α i).eval tapes = .some (Function.update tapes i
      (BiTape.mk₂ ((StrEnc.enc x).reverse ++ l) r)) := by sorry

/--
Write a list of characters to tape `i` by repeatedly moving left and writing,
effectively prepending the characters to the tape content.
For `[c₁, c₂, …, cₙ]` this unfolds to:
`left ; write cₙ ; … ; left ; write c₂ ; left ; write c₁`
-/
public def putChars : List Char → Fin k → MultiTapeTM k Char
  | [], _ => noop
  | c :: rest, i => putChars rest i ;ₜ left i ;ₜ write c i

/--
A Turing machine that prepends the encoding of a value `x : α` to tape `i`.
For an inductive type with constructor `c` and arguments `a₁, …, aₙ` of types `T₁, …, Tₙ`,
this is equivalent to:
`left ; write ')' ; put Tₙ aₙ ; … ; put T₁ a₁ ; put ℕ c ; write '('`
-/
public def put {k : ℕ} (α : Type*) [StrEnc α] (x : α) (i : Fin k) :
    MultiTapeTM k Char :=
  putChars (StrEnc.enc x) i

@[simp]
public lemma put_eval {k : ℕ} {α : Type*} [StrEnc α] {x : α} {i : Fin k}
  {tapes : Fin k → BiTape Char}
  {l r : List Char}
  (h_tape : tapes i = BiTape.mk₁ r) :
  (put α x i).eval tapes = .some (Function.update tapes i
      (BiTape.mk₁ ((StrEnc.enc x) ++ r))) := by sorry

--- Skip to the left across a StrEnc-encoded value (inverse of `skipRight`).
def skipLeft_numeric {k : ℕ} (depth : ℕ) (i : Fin k) :
    MultiTapeTM k Char := sorry

--- Skip to the left across a StrEnc-encoded value (inverse of `skipRight`).
public def skipLeft {k : ℕ} (α : Type*) [StrEnc α] (i : Fin k) :
    MultiTapeTM k Char := skipLeft_numeric (StrEnc.maxDepth α) i

@[simp]
public lemma skipLeft_eval {k : ℕ} {α : Type*} [StrEnc α] {i : Fin k}
  {tapes : Fin k → BiTape Char}
  {x : α}
  {l r : List Char}
  (h_hasValue : tapes i = BiTape.mk₂ ((StrEnc.enc x).reverse ++ l) r) :
  (skipLeft α i).eval tapes = .some (Function.update tapes i
      (BiTape.mk₂ l ((StrEnc.enc x) ++ r))) := by sorry

--- Skip past a given number of constructor fields using their known depths.
def skipFields {k : ℕ} (α : Type*) [StrEnc α] (ctorIdx : ℕ) :
    ℕ → Fin k → MultiTapeTM k Char
  | 0, _ => noop
  | n + 1, i => skipFields α ctorIdx n i ;ₜ
      skipRight_numeric (StrEnc.fieldDepth α ctorIdx n) i

--- Skip past fields to the left (inverse of `skipFields`).
def skipFieldsLeft {k : ℕ} (α : Type*) [StrEnc α] (ctorIdx : ℕ) :
    ℕ → Fin k → MultiTapeTM k Char
  | 0, _ => noop
  | n + 1, i => skipLeft_numeric (StrEnc.fieldDepth α ctorIdx n) i ;ₜ
      skipFieldsLeft α ctorIdx n i

/--
Move the head to the `argIdx`-th argument of a constructor of type `α`.
`toArg α ctorIdx argIdx i = right i ;ₜ skipRight ℕ i ;ₜ skipRight T₁ i ;ₜ … ;ₜ skipRight T(argIdx-1) i`
-/
public def toArg {k : ℕ} (α : Type*) [StrEnc α] (ctorIdx argIdx : ℕ)
    (i : Fin k) : MultiTapeTM k Char :=
  right i ;ₜ skipRight ℕ i ;ₜ skipFields α ctorIdx argIdx i

/--
Move the head back from the `argIdx`-th argument to the start of the encoding
(inverse of `toArg`).
-/
public def outOfArg {k : ℕ} (α : Type*) [StrEnc α] (ctorIdx argIdx : ℕ)
    (i : Fin k) : MultiTapeTM k Char :=
  skipFieldsLeft α ctorIdx argIdx i ;ₜ skipLeft ℕ i ;ₜ left i

/-- Erase the StrEnc-encoded value at the head of tape `i`. -/
public def erase {k : ℕ} (α : Type*) [StrEnc α] (i : Fin k) :
    MultiTapeTM k Char := sorry

@[simp]
public lemma erase_eval {k : ℕ} {α : Type*} [StrEnc α] {i : Fin k}
  {tapes : Fin k → BiTape Char}
  {x : α}
  {l r : List Char}
  (h_tape : tapes i = BiTape.mk₂ l ((StrEnc.enc x) ++ r)) :
  (erase α i).eval tapes = .some (Function.update tapes i
      (BiTape.mk₂ l r)) := by sorry

/--
Prepend an item to a StrEnc-encoded list on tape `i`.
`pushList α x i = right i ;ₜ put α x i ;ₜ left i ;ₜ write '(' i`
-/
public def pushList {k : ℕ} (α : Type*) [StrEnc α] (x : α) (i : Fin k) :
    MultiTapeTM k Char :=
  right i ;ₜ put α x i ;ₜ left i ;ₜ write '(' i

@[simp]
public lemma pushList_eval {k : ℕ} {α : Type*} [StrEnc α] {x : α}
  {xs : List α} {i : Fin k}
  {tapes : Fin k → BiTape Char}
  {r : List Char}
  (h_tape : tapes i = BiTape.mk₁ (StrEnc.enc xs ++ r)) :
  (pushList α x i).eval tapes = .some (Function.update tapes i
      (BiTape.mk₁ (StrEnc.enc (x :: xs) ++ r))) := by sorry

/-- Remove the first item from a StrEnc-encoded list on tape `i`.
    Running `pop` on an empty list does not modify the tape. -/
public def popEnc {k : ℕ} (α : Type*) [StrEnc α] (i : Fin k) :
    MultiTapeTM k Char := sorry

@[simp]
public lemma popEnc_eval_cons {k : ℕ} {α : Type*} [StrEnc α]
  {x : α} {xs : List α} {i : Fin k}
  {tapes : Fin k → BiTape Char}
  {r : List Char}
  (h_tape : tapes i = BiTape.mk₁ (StrEnc.enc (x :: xs) ++ r)) :
  (popEnc α i).eval tapes = .some (Function.update tapes i
      (BiTape.mk₁ (StrEnc.enc xs ++ r))) := by sorry

@[simp]
public lemma popEnc_eval_nil {k : ℕ} {α : Type*} [StrEnc α] {i : Fin k}
  {tapes : Fin k → BiTape Char}
  {r : List Char}
  (h_tape : tapes i = BiTape.mk₁ (StrEnc.enc ([] : List α) ++ r)) :
  (popEnc α i).eval tapes = .some tapes := by sorry

/--
Dispatch on the constructor of a StrEnc-encoded value on tape `i`.
Reads the constructor index, positions the head at the first argument,
runs the corresponding branch, then repositions the head at the start of the encoding.
-/
public def case {k : ℕ} (α : Type*) [StrEnc α] (i : Fin k)
    (branches : List (MultiTapeTM k Char)) : MultiTapeTM k Char := sorry

/--
Copy a StrEnc-encoded value of type `α` from tape `i` to tape `j`
(prepending the encoding to tape `j`).
-/
public def copyEnc {k : ℕ} (α : Type*) [StrEnc α] (i j : Fin k) :
    MultiTapeTM k Char := sorry

@[simp]
public lemma copyEnc_eval {k : ℕ} {α : Type*} [StrEnc α]
  {i j : Fin k} (h_ne : i ≠ j)
  {tapes : Fin k → BiTape Char}
  {x : α}
  {lᵢ rᵢ : List Char}
  {rⱼ : List Char}
  (h_tapei : tapes i = BiTape.mk₂ lᵢ ((StrEnc.enc x) ++ rᵢ))
  (h_tapej : tapes j = BiTape.mk₁ rⱼ) :
  (copyEnc α i j).eval tapes = .some
    (Function.update (Function.update tapes i (BiTape.mk₂ lᵢ ((StrEnc.enc x) ++ rᵢ)))
      j (BiTape.mk₁ ((StrEnc.enc x) ++ rⱼ))) := by sorry

/--
Compare StrEnc-encoded values of type `α` on tapes `i` and `j`.
Runs `tm_eq` if values are equal, `tm_neq` if not. Tapes `i` and `j` are
restored to their original positions after comparison.
-/
public def eqEnc {k : ℕ} (α : Type*) [StrEnc α] (i j : Fin k)
    (tm_eq tm_neq : MultiTapeTM k Char) : MultiTapeTM k Char := sorry

/-- Compare values on tapes `i` and `j` and put the boolean result on tape `result`. -/
public def isEq {k : ℕ} (α : Type*) [StrEnc α] (i j : Fin k) (result : Fin k) :
    MultiTapeTM k Char :=
  eqEnc α i j (put Bool true result) (put Bool false result)

@[simp]
public lemma isEq_eval {k : ℕ} {α : Type*} [StrEnc α] [DecidableEq α]
  {i j result : Fin k}
  {tapes : Fin k → BiTape Char}
  {x y : α}
  {lᵢ rᵢ lⱼ rⱼ : List Char}
  {rₖ : List Char}
  (h_tapei : tapes i = BiTape.mk₂ lᵢ ((StrEnc.enc x) ++ rᵢ))
  (h_tapej : tapes j = BiTape.mk₂ lⱼ ((StrEnc.enc y) ++ rⱼ))
  (h_tapek : tapes result = BiTape.mk₁ rₖ) :
  (isEq α i j result).eval tapes = .some
    (Function.update tapes result
      (BiTape.mk₁ ((StrEnc.enc (decide (x = y))) ++ rₖ))) := by sorry

/--
Execute a Turing machine `tm` on every item in the StrEnc-encoded list on tape `i`,
assuming the state of tape `i` is reset by `tm`.
`run_list α i tm = right i ;ₜ while_neq ')' i (tm ;ₜ skipRight α i) ;ₜ while_neq '(' i (skipLeft α i)`
-/
public def run_list {k : ℕ} (α : Type*) [StrEnc α] (i : Fin k)
    (tm : MultiTapeTM k Char) : MultiTapeTM k Char :=
  right i ;ₜ while_neq ')' i (tm ;ₜ skipRight α i) ;ₜ
    while_neq '(' i (skipLeft α i)

/-- Combine two Bool values using logical OR.
    `combineOr j = case Bool j [erase Bool j, erase Bool j ;ₜ erase Bool j ;ₜ put Bool true j]` -/
public def combineOr {k : ℕ} (j : Fin k) : MultiTapeTM k Char :=
  case Bool j [erase Bool j, erase Bool j ;ₜ erase Bool j ;ₜ put Bool true j]

/-- Negate a Bool value on tape `j`.
    `negateBool j = case Bool j [erase Bool j ;ₜ put Bool true j, erase Bool j ;ₜ put Bool false j]` -/
public def negateBool {k : ℕ} (j : Fin k) : MultiTapeTM k Char :=
  case Bool j [erase Bool j ;ₜ put Bool true j, erase Bool j ;ₜ put Bool false j]

/--
Run `tm` on every item of the list on tape `i`, assuming `tm` outputs a boolean
value to tape `j`, and compute the logical OR of the results across the list.
`any_list α i tm j = put Bool false j ;ₜ run_list α i (tm ;ₜ combineOr j)`
-/
public def any_list {k : ℕ} (α : Type*) [StrEnc α] (i : Fin k)
    (tm : MultiTapeTM k Char) (j : Fin k) : MultiTapeTM k Char :=
  put Bool false j ;ₜ run_list α i (tm ;ₜ combineOr j)

/--
Run `tm` on every item of the list on tape `i`, assuming `tm` outputs a boolean
value to tape `j`, and compute the logical AND of the results across the list.
`all_list α i tm j = any_list α i (tm ;ₜ negateBool j) j ;ₜ negateBool j`
-/
public def all_list {k : ℕ} (α : Type*) [StrEnc α] (i : Fin k)
    (tm : MultiTapeTM k Char) (j : Fin k) : MultiTapeTM k Char :=
  any_list α i (tm ;ₜ negateBool j) j ;ₜ negateBool j

/--
Check if the value on tape `i` is contained in the list on tape `j`
and store the boolean result on tape `result`.
`contains α i j result = any_list α j (isEq α i j result) result`
-/
public def contains {k : ℕ} (α : Type*) [StrEnc α]
    (i j result : Fin k) : MultiTapeTM k Char :=
  any_list α j (isEq α i j result) result

end Routines

end Turing
