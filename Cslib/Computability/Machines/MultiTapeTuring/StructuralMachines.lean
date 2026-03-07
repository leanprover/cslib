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
  {r : List Char}
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

/-- The tape `i` state after `toArg`. -/
public noncomputable def toArg_result {k : ℕ} (α : Type*) [StrEnc α]
    (ctorIdx argIdx : ℕ) (i : Fin k)
    (tapes : Fin k → BiTape Char) : BiTape Char := sorry

@[simp]
public lemma toArg_eval {k : ℕ} {α : Type*} [StrEnc α]
    {ctorIdx argIdx : ℕ} {i : Fin k} {tapes : Fin k → BiTape Char} :
    (toArg α ctorIdx argIdx i).eval tapes = .some
      (Function.update tapes i (toArg_result α ctorIdx argIdx i tapes)) := by sorry

/--
Move the head back from the `argIdx`-th argument to the start of the encoding
(inverse of `toArg`).
-/
public def outOfArg {k : ℕ} (α : Type*) [StrEnc α] (ctorIdx argIdx : ℕ)
    (i : Fin k) : MultiTapeTM k Char :=
  skipFieldsLeft α ctorIdx argIdx i ;ₜ skipLeft ℕ i ;ₜ left i

/-- The tape `i` state after `outOfArg`. -/
public noncomputable def outOfArg_result {k : ℕ} (α : Type*) [StrEnc α]
    (ctorIdx argIdx : ℕ) (i : Fin k)
    (tapes : Fin k → BiTape Char) : BiTape Char := sorry

@[simp]
public lemma outOfArg_eval {k : ℕ} {α : Type*} [StrEnc α]
    {ctorIdx argIdx : ℕ} {i : Fin k} {tapes : Fin k → BiTape Char} :
    (outOfArg α ctorIdx argIdx i).eval tapes = .some
      (Function.update tapes i (outOfArg_result α ctorIdx argIdx i tapes)) := by sorry

/-- Erase the StrEnc-encoded value at the head of tape `i`. -/
public def erase {k : ℕ} (α : Type*) [StrEnc α] (i : Fin k) :
    MultiTapeTM k Char := sorry

/-- The tape `i` state after `erase`. -/
public noncomputable def erase_result {k : ℕ} (α : Type*) [StrEnc α]
    (i : Fin k) (tapes : Fin k → BiTape Char) : BiTape Char := sorry

@[simp]
public lemma erase_eval {k : ℕ} {α : Type*} [StrEnc α] {i : Fin k}
  {tapes : Fin k → BiTape Char} :
  (erase α i).eval tapes = .some (Function.update tapes i
      (erase_result α i tapes)) := by sorry

@[simp]
public lemma erase_result_spec {k : ℕ} {α : Type*} [StrEnc α] {i : Fin k}
  {tapes : Fin k → BiTape Char}
  {x : α}
  {r : List Char}
  (h_tape : tapes i = BiTape.mk₁ ((StrEnc.enc x) ++ r)) :
  erase_result α i tapes = BiTape.mk₁ r := by sorry

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
Requires `StrEnc.fieldDepths.size > 0` (i.e., the type is inductive).
-/
public def case {k : ℕ} (α : Type*) [StrEnc α] (i : Fin k)
    (branches : List (MultiTapeTM k Char)) : MultiTapeTM k Char := sorry

/-- Generic `case` eval: dispatches to `branches[ctorIndex x]`. -/
@[simp]
public lemma case_eval {α : Type*} [StrEnc α] {i : Fin k}
    {branches : List (MultiTapeTM k Char)}
    {tapes : Fin k → BiTape Char}
    {x : α}
    {r : List Char}
    (h_tape : tapes i = BiTape.mk₁ (StrEnc.enc x ++ r))
    (h_idx : StrEnc.ctorIndex x < branches.length) :
    (case α i branches).eval tapes =
      branches[StrEnc.ctorIndex x].eval tapes := by sorry

/-- `case` on a `false` value dispatches to the first branch. -/
@[simp]
public lemma case_Bool_false_eval {i : Fin k}
    {tm₀ : MultiTapeTM k Char} {tms : List (MultiTapeTM k Char)}
    {tapes : Fin k → BiTape Char}
    {r : List Char}
    (h_tape : tapes i = BiTape.mk₁ (StrEnc.enc false ++ r)) :
    (case Bool i (tm₀ :: tms)).eval tapes = tm₀.eval tapes := by
  have h_idx : StrEnc.ctorIndex false < (tm₀ :: tms).length :=
    Nat.zero_lt_succ _
  rw [case_eval (x := false) h_tape h_idx]
  rfl

/-- `case` on a `true` value dispatches to the second branch. -/
@[simp]
public lemma case_Bool_true_eval {i : Fin k}
    {tm₀ tm₁ : MultiTapeTM k Char}
    {tms : List (MultiTapeTM k Char)}
    {tapes : Fin k → BiTape Char}
    {r : List Char}
    (h_tape : tapes i = BiTape.mk₁ (StrEnc.enc true ++ r)) :
    (case Bool i (tm₀ :: tm₁ :: tms)).eval tapes =
      tm₁.eval tapes := by
  have h_idx : StrEnc.ctorIndex true < (tm₀ :: tm₁ :: tms).length := by
    simp [show StrEnc.ctorIndex true = 1 from rfl]
  rw [case_eval (x := true) h_tape h_idx]
  rfl

/--
Copy a StrEnc-encoded value of type `α` from tape `i` to tape `j`
(prepending the encoding to tape `j`).
-/
public def copyEnc {k : ℕ} (α : Type*) [StrEnc α] (i j : Fin k) :
    MultiTapeTM k Char := sorry

/-- The full tape state after `copyEnc`. -/
public noncomputable def copyEnc_result {k : ℕ} (α : Type*) [StrEnc α]
    (i j : Fin k) (tapes : Fin k → BiTape Char) : Fin k → BiTape Char := sorry

@[simp]
public lemma copyEnc_eval {k : ℕ} {α : Type*} [StrEnc α]
  {i j : Fin k} {tapes : Fin k → BiTape Char} :
  (copyEnc α i j).eval tapes = .some (copyEnc_result α i j tapes) := by sorry

@[simp]
public lemma copyEnc_result_spec {k : ℕ} {α : Type*} [StrEnc α]
  {i j : Fin k} (h_ne : i ≠ j)
  {tapes : Fin k → BiTape Char}
  {x : α}
  {lᵢ rᵢ : List Char}
  {rⱼ : List Char}
  (h_tapei : tapes i = BiTape.mk₂ lᵢ ((StrEnc.enc x) ++ rᵢ))
  (h_tapej : tapes j = BiTape.mk₁ rⱼ) :
  copyEnc_result α i j tapes =
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

@[simp]
public lemma Function.update_update {α : Type*} {β : Type*}
    [DecidableEq α] {f : α → β} {a : α} {b c : β} :
    Function.update (Function.update f a b) a c =
      Function.update f a c := by
  ext x; simp [Function.update]; split <;> rfl

@[simp]
public lemma part_some_bind_eq {α : Type u}
    {a : α} {f : α → Part α} :
    Part.some a >>= f = f a := by
  change (Part.some a).bind f = f a
  exact Part.bind_some a f

/-- Combine two Bool values using logical OR.
    `combineOr j = case Bool j [erase Bool j, erase Bool j ;ₜ erase Bool j ;ₜ put Bool true j]` -/
public def combineOr {k : ℕ} (j : Fin k) : MultiTapeTM k Char :=
  case Bool j [erase Bool j, erase Bool j ;ₜ erase Bool j ;ₜ put Bool true j]

@[simp]
public lemma combineOr_eval {j : Fin k} {b₁ b₂ : Bool}
    {tapes : Fin k → BiTape Char}
    {r : List Char}
    (h_tape : tapes j = BiTape.mk₁ (StrEnc.enc b₁ ++ StrEnc.enc b₂ ++ r)) :
    (combineOr j).eval tapes = .some (Function.update tapes j
      (BiTape.mk₁ (StrEnc.enc (b₁ || b₂) ++ r))) := by
  unfold combineOr
  have h_assoc : tapes j = BiTape.mk₁ (StrEnc.enc b₁ ++ (StrEnc.enc b₂ ++ r)) := by
    simp only [List.append_assoc] at h_tape; exact h_tape
  cases b₁ with
  | false =>
    simp only [Bool.false_or, case_Bool_false_eval h_assoc,
      erase_eval, erase_result_spec (x := false) h_assoc]
  | true =>
    simp only [Bool.true_or, case_Bool_true_eval h_assoc,
      MultiTapeTM.seq_eval,
      erase_eval, erase_result_spec (x := true) h_assoc, part_some_bind_eq,
      erase_result_spec (x := b₂) (Function.update_self j _ tapes),
      Function.update_update,
      put_eval (x := true) (Function.update_self j _ tapes)]

/-- Negate a Bool value on tape `j`. -/
public def negateBool {k : ℕ} (j : Fin k) : MultiTapeTM k Char :=
  case Bool j
    [erase Bool j ;ₜ put Bool true j,
     erase Bool j ;ₜ put Bool false j]

@[simp]
public lemma negateBool_eval {j : Fin k} {b : Bool}
    {tapes : Fin k → BiTape Char}
    {r : List Char}
    (h_tape : tapes j = BiTape.mk₁ (StrEnc.enc b ++ r)) :
    (negateBool j).eval tapes = .some (Function.update tapes j
      (BiTape.mk₁ (StrEnc.enc (!b) ++ r))) := by
  unfold negateBool
  cases b with
  | false =>
    simp only [Bool.not_false, case_Bool_false_eval h_tape,
      MultiTapeTM.seq_eval,
      erase_eval, erase_result_spec (x := false) h_tape, part_some_bind_eq,
      put_eval (x := true) (Function.update_self j _ tapes),
      Function.update_update]
  | true =>
    simp only [Bool.not_true, case_Bool_true_eval h_tape,
      MultiTapeTM.seq_eval,
      erase_eval, erase_result_spec (x := true) h_tape, part_some_bind_eq,
      put_eval (x := false) (Function.update_self j _ tapes),
      Function.update_update]

/--
Execute a Turing machine `tm` on every item in the StrEnc-encoded list on tape `i`,
assuming the state of tape `i` is reset by `tm`.
-/
public def run_list {k : ℕ} (α : Type*) [StrEnc α] (i : Fin k)
    (tm : MultiTapeTM k Char) : MultiTapeTM k Char :=
  right i ;ₜ while_neq ')' i (tm ;ₜ skipRight α i) ;ₜ
    while_neq '(' i (skipLeft α i)

/--
After `run_list α i (tm ;ₜ combineOr j)` processes a list `xs` on tape `i`,
with an initial boolean accumulator `b₀` on tape `j`, the result on tape `j` is
`enc(xs.any f || b₀)`, where `f` is the boolean function computed by `tm`.
Tape `i` is restored to its original state.
-/
@[simp]
public lemma run_list_combineOr_eval {α : Type*} [StrEnc α] {i j : Fin k}
    (h_ne : i ≠ j)
    {tm : MultiTapeTM k Char}
    {xs : List α} {f : α → Bool} {b₀ : Bool}
    {tapes : Fin k → BiTape Char}
    {r_i r_j : List Char}
    (h_tape_i : tapes i = BiTape.mk₁ (StrEnc.enc xs ++ r_i))
    (h_tape_j : tapes j = BiTape.mk₁ (StrEnc.enc b₀ ++ r_j))
    (h_halts : ∀ tapes,
      (tm ;ₜ combineOr j ;ₜ skipRight α i).HaltsOn tapes)
    (h_tm : ∀ (x : α) (t : Fin k → BiTape Char)
      (l r : List Char) (b : Bool) (r' : List Char),
      t i = BiTape.mk₂ l (StrEnc.enc x ++ r) →
      t j = BiTape.mk₁ (StrEnc.enc b ++ r') →
      ∃ t', tm.eval t = .some t' ∧ t' i = t i ∧
        t' j = BiTape.mk₁ (StrEnc.enc (f x) ++ StrEnc.enc b ++ r')) :
    (run_list α i (tm ;ₜ combineOr j)).eval tapes = .some (Function.update tapes j
      (BiTape.mk₁ (StrEnc.enc (xs.any f || b₀) ++ r_j))) := by sorry


/--
Run `tm` on every item of the list on tape `i`, assuming `tm` outputs a boolean
value to tape `j`, and compute the logical OR of the results across the list.
`any_list α i tm j = put Bool false j ;ₜ run_list α i (tm ;ₜ combineOr j)`
-/
public def any_list {k : ℕ} (α : Type*) [StrEnc α] (i : Fin k)
    (tm : MultiTapeTM k Char) (j : Fin k) : MultiTapeTM k Char :=
  put Bool false j ;ₜ run_list α i (tm ;ₜ combineOr j)

/--
The result on tape `j` after running `any_list α i tm j` on `tapes`.
Use simp lemmas like `any_list_result_spec` to reduce this for specific inputs.
-/
public noncomputable def any_list_result {k : ℕ} (α : Type*) [StrEnc α]
    (i : Fin k) (tm : MultiTapeTM k Char) (j : Fin k)
    (tapes : Fin k → BiTape Char) : BiTape Char := sorry

/--
Unconditional simp lemma: `any_list` always produces an update to tape `j`.
The actual content of tape `j` is described by `any_list_result`, which has its
own simp rules for specific inputs.
-/
@[simp]
public lemma any_list_eval {α : Type*} [StrEnc α] {i j : Fin k}
    {tm : MultiTapeTM k Char}
    {tapes : Fin k → BiTape Char} :
    (any_list α i tm j).eval tapes = .some (Function.update tapes j
      (any_list_result α i tm j tapes)) := by sorry

/--
Reduce `any_list_result` when the list on tape `i` and the function computed by
`tm` are known.
-/
@[simp]
public lemma any_list_result_spec {α : Type*} [StrEnc α] {i j : Fin k}
    (h_ne : i ≠ j)
    {tm : MultiTapeTM k Char}
    {xs : List α} {f : α → Bool}
    {tapes : Fin k → BiTape Char}
    {r_i r_j : List Char}
    (h_tape_i : tapes i = BiTape.mk₁ (StrEnc.enc xs ++ r_i))
    (h_tape_j : tapes j = BiTape.mk₁ r_j)
    (h_halts : ∀ tapes, (tm ;ₜ combineOr j ;ₜ skipRight α i).HaltsOn tapes)
    (h_tm : ∀ (x : α) (t : Fin k → BiTape Char) (l r : List Char) (b : Bool) (r' : List Char),
      t i = BiTape.mk₂ l (StrEnc.enc x ++ r) →
      t j = BiTape.mk₁ (StrEnc.enc b ++ r') →
      ∃ t', tm.eval t = .some t' ∧ t' i = t i ∧
        t' j = BiTape.mk₁ (StrEnc.enc (f x) ++ StrEnc.enc b ++ r')) :
    any_list_result α i tm j tapes =
      BiTape.mk₁ (StrEnc.enc (xs.any f) ++ r_j) := by sorry

/--
Run `tm` on every item of the list on tape `i`, assuming `tm` outputs a boolean
value to tape `j`, and compute the logical AND of the results across the list.
`all_list α i tm j = any_list α i (tm ;ₜ negateBool j) j ;ₜ negateBool j`
-/
public def all_list {k : ℕ} (α : Type*) [StrEnc α] (i : Fin k)
    (tm : MultiTapeTM k Char) (j : Fin k) : MultiTapeTM k Char :=
  any_list α i (tm ;ₜ negateBool j) j ;ₜ negateBool j

/--
The result on tape `j` after running `all_list α i tm j` on `tapes`.
Use simp lemmas like `all_list_result_spec` to reduce this for specific inputs.
-/
public noncomputable def all_list_result {k : ℕ} (α : Type*) [StrEnc α]
    (i : Fin k) (tm : MultiTapeTM k Char) (j : Fin k)
    (tapes : Fin k → BiTape Char) : BiTape Char := sorry

/--
Unconditional simp lemma: `all_list` always produces an update to tape `j`.
-/
@[simp]
public lemma all_list_eval {α : Type*} [StrEnc α] {i j : Fin k}
    {tm : MultiTapeTM k Char}
    {tapes : Fin k → BiTape Char} :
    (all_list α i tm j).eval tapes = .some (Function.update tapes j
      (all_list_result α i tm j tapes)) := by sorry

/--
Reduce `all_list_result` when the list on tape `i` and the function computed by
`tm` are known.
-/
@[simp]
public lemma all_list_result_spec {α : Type*} [StrEnc α] {i j : Fin k}
    (h_ne : i ≠ j)
    {tm : MultiTapeTM k Char}
    {xs : List α} {f : α → Bool}
    {tapes : Fin k → BiTape Char}
    {r_i r_j : List Char}
    (h_tape_i : tapes i = BiTape.mk₁ (StrEnc.enc xs ++ r_i))
    (h_tape_j : tapes j = BiTape.mk₁ r_j)
    (h_halts : ∀ tapes,
      (tm ;ₜ negateBool j ;ₜ combineOr j ;ₜ skipRight α i).HaltsOn tapes)
    (h_tm : ∀ (x : α) (t : Fin k → BiTape Char) (l r : List Char) (b : Bool) (r' : List Char),
      t i = BiTape.mk₂ l (StrEnc.enc x ++ r) →
      t j = BiTape.mk₁ (StrEnc.enc b ++ r') →
      ∃ t', (tm ;ₜ negateBool j).eval t = .some t' ∧ t' i = t i ∧
        t' j = BiTape.mk₁ (StrEnc.enc (!(f x)) ++ StrEnc.enc b ++ r')) :
    all_list_result α i tm j tapes =
      BiTape.mk₁ (StrEnc.enc (xs.all f) ++ r_j) := by sorry

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
