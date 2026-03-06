import Encoding
import Mathlib.Data.List.Basic

/-!
# Turing Machines over Character Tapes

We define an abstract model of single-tape Turing machines over character alphabets,
give elementary operations as `sorry`-defined constants with stated semantics, and
build derived *skip* machines for navigating encoded values.

## Tape model

A `Tape` is a pair `⟨left, right⟩` where
- `left` is the portion to the *left* of the head, stored in **reverse** order
  (`left.head?` is the cell immediately left of the head), and
- `right` is the portion at and to the *right* of the head
  (`right.head?` is the current cell, if any).

## Machine model

A `TM` is an opaque type representing a partial Turing machine.  Use `TM.eval` to
execute it.  `none` means the machine diverges or encounters an invalid configuration.
Sequential composition `m₁ ;; m₂` is `Option`-monadic bind on `TM.eval`.

## Skip machines

For each encodable type `α` with `[StrEnc α]` giving its maximum parenthesis nesting
depth `StrEnc.depth`, the machine `skip α = skipRight StrEnc.depth` moves the head
from the opening `(` of an encoded value to the first character after the closing `)`
 no runtime counter needed, since the depth is a compile-time constant.
-/

/-! ## Tape -/

/-- A Turing machine tape.
    `left` is stored reversed so that `left.head?` is the cell immediately left of the head.
    `right.head?` is the current cell (if any). -/
structure Tape where
  left  : List Char
  right : List Char
  deriving Repr, DecidableEq

/-! ## TM: opaque Turing machine type -/

/-- An opaque Turing machine.  The internal implementation is hidden; use `TM.eval` to run it. -/
structure TM where
  private mk ::
  private runFn : Tape → Option Tape

namespace TM

/-- Execute a TM on a tape.  Returns `none` if the machine diverges or gets stuck. -/
def eval (tm : TM) (t : Tape) : Option Tape := tm.runFn t

@[simp] lemma eval_mk (f : Tape → Option Tape) (t : Tape) : (TM.mk f).eval t = f t := rfl

/-- Two TMs are equal iff they agree on all inputs. -/
@[ext] theorem ext {m₁ m₂ : TM} (h : ∀ t, m₁.eval t = m₂.eval t) : m₁ = m₂ := by
  cases m₁; cases m₂; simp only [eval] at h; exact congrArg TM.mk (funext h)

/-! ## Composition -/

/-- Sequential composition: run `m₁` then feed its output to `m₂`. -/
def seq (m₁ m₂ : TM) : TM := TM.mk (fun t => m₁.eval t >>= m₂.eval)

infixl:55 " ;; " => seq

@[simp] lemma seq_eval (m₁ m₂ : TM) (t : Tape) : (m₁ ;; m₂).eval t = m₁.eval t >>= m₂.eval := rfl

/-- The identity machine. -/
def idMach : TM := TM.mk (fun t => some t)

@[simp] lemma idMach_eval (t : Tape) : idMach.eval t = some t := rfl

@[simp] lemma seq_idMach_right (m : TM) : (m ;; idMach) = m := by
  ext t; simp [seq_eval]; cases m.eval t <;> rfl

@[simp] lemma seq_idMach_left (m : TM) : (idMach ;; m) = m := by
  ext t; simp [seq_eval]

@[simp] lemma seq_assoc (m₁ m₂ m₃ : TM) : ((m₁ ;; m₂) ;; m₃) = (m₁ ;; (m₂ ;; m₃)) := by
  ext t; simp [seq_eval]; cases m₁.eval t <;> simp

/-! ## Elementary machines (definitions deferred — semantics stated as lemmas) -/

/-- Move the head one cell to the right. -/
def right : TM := sorry

/-- Move the head one cell to the left. -/
def left : TM := sorry

/-- While the cell at the head equals `c`, execute `tm`. -/
def while_eq (c : Char) (tm : TM) : TM := sorry

/-- While the cell at the head differs from `c`, execute `tm`. -/
def while_neq (c : Char) (tm : TM) : TM := sorry

/-! ### Semantics of elementary machines (sorry-proved) -/

@[simp]
lemma right_spec (l : List Char) (c : Char) (r : List Char) :
    right.eval ⟨l, c :: r⟩ = some ⟨c :: l, r⟩ := sorry

@[simp]
lemma left_spec (l : List Char) (c : Char) (r : List Char) :
    left.eval ⟨c :: l, r⟩ = some ⟨l, c :: r⟩ := sorry

/-- `while_eq` terminates immediately when the head cell differs from `c`. -/
lemma while_eq_done {c : Char} {tm : TM} {l : List Char} {c' : Char} {r : List Char}
    (h : c' ≠ c) :
    (while_eq c tm).eval ⟨l, c' :: r⟩ = some ⟨l, c' :: r⟩ := sorry

/-- `while_eq` runs one step of `tm` when the head cell equals `c`, then loops. -/
lemma while_eq_step {c : Char} {tm : TM} {l : List Char} {r : List Char} {t' : Tape}
    (hstep : tm.eval ⟨l, c :: r⟩ = some t') :
    (while_eq c tm).eval ⟨l, c :: r⟩ = (while_eq c tm).eval t' := sorry

/-- `while_neq` terminates immediately when the head cell equals `c`. -/
@[simp]
lemma while_neq_done {c : Char} {tm : TM} {l : List Char} {r : List Char} :
    (while_neq c tm).eval ⟨l, c :: r⟩ = some ⟨l, c :: r⟩ := sorry

/-- `while_neq` runs one step of `tm` when the head cell differs from `c`, then loops. -/
lemma while_neq_step {c : Char} {tm : TM} {l : List Char} {c' : Char} {r : List Char}
    {t' : Tape} (h : c' ≠ c) (hstep : tm.eval ⟨l, c' :: r⟩ = some t') :
    (while_neq c tm).eval ⟨l, c' :: r⟩ = (while_neq c tm).eval t' := sorry

/-! ## Parenthesis nesting depth -/

/-- Maximum parenthesis nesting depth of a string.
    State: (current depth, maximum depth seen so far). -/
def parenDepth (s : String) : ℕ :=
  (s.toList.foldl
    (fun st c =>
      if c = '(' then (st.1 + 1, max st.2 (st.1 + 1))
      else if c = ')' then (st.1 - 1, st.2)
      else st)
    (0, 0)).2

section DepthExamples
#eval parenDepth "()"           -- 1  (= enc 0 : ℕ)
#eval parenDepth "(11)"         -- 1  (= enc 3 : ℕ)
#eval parenDepth "(()(1))"      -- 2  (= enc (Literal.pos 1))
#eval parenDepth "((1)(1))"     -- 2  (= enc (Literal.neg 1))
#eval parenDepth "(((1)(1)))"   -- 3
end DepthExamples

/-- A string is a *well-formed encoding*: nonempty, starts with `(`, ends with `)`. -/
def WellFormed (s : String) : Prop :=
  s.toList ≠ [] ∧ s.toList.head? = some '(' ∧ s.toList.getLast? = some ')'

/-! ## `EncDepth` typeclass -/

/-- `EncDepth α` asserts that:
    (1) every encoded value of type `α` has parenthesis nesting depth ≤ `StrEnc.depth α`, and
    (2) every encoded value is well-formed (starts with `(`, ends with `)`).

    The depth bound is carried in `StrEnc.depth`.  These two properties together guarantee
    that `skipRight (StrEnc.depth α)` correctly skips over any encoded `α` value. -/
class EncDepth (α : Type*) [StrEnc α] where
  depth_bound : ∀ x : α, parenDepth (StrEnc.enc x) ≤ StrEnc.depth (α := α)
  well_formed : ∀ x : α, WellFormed (StrEnc.enc x)

/-! ### Standard `EncDepth` instances -/

/-- Natural numbers: `encNat n = "(" ++ dyadicEnc n ++ ")"`, `StrEnc.depth = 1`.
    The dyadic digits `1` and `2` contain no parentheses, so depth = 1. -/
instance : EncDepth ℕ where
  depth_bound := sorry
  well_formed := sorry

/-- Lists: `enc l = "(" ++ enc x₁ ++ … ++ ")"`.
    Each `enc xᵢ` has depth ≤ `StrEnc.depth α`; the outer `()` adds one level,
    giving  `StrEnc.depth α + 1 = StrEnc.depth (List α)`. -/
instance [StrEnc α] [EncDepth α] : EncDepth (List α) where
  depth_bound := sorry
  well_formed := sorry

/-! ## Skip machines -/

/-- `skipRight d` moves the head from the `(` of a well-formed encoding of depth ≤ `d`
    to the first character after the closing `)`.

    ```
    skipRight 0     = right                                   -- not used in practice
    skipRight (d+1) = right ;; while_neq ')' (skipRight d) ;; right
    ```

    Correctness: inside any depth-`(d+1)` encoding, the content consists of
    depth-`d` sub-encodings; `while_neq ')' (skipRight d)` iterates `skipRight d`
    on each sub-encoding until the closing `)` is reached. -/
def skipRight : ℕ → TM
  | 0     => right
  | d + 1 => right ;; while_neq ')' (skipRight d) ;; right

/-- The canonical skip machine for type `α`: moves past one encoded `α` value.
    Uses `StrEnc.depth` as the parenthesis nesting depth bound. -/
def skip (α : Type*) [StrEnc α] [EncDepth α] : TM :=
  skipRight (StrEnc.depth (α := α))

/-! ### Unfolding lemmas -/

lemma skipRight_zero : skipRight 0 = right := rfl

lemma skipRight_succ (d : ℕ) :
    skipRight (d + 1) = (right ;; while_neq ')' (skipRight d) ;; right) := rfl

lemma skip_Nat_eq : skip ℕ = (right ;; while_neq ')' right ;; right) := rfl

lemma skip_List_eq (α : Type*) [StrEnc α] [EncDepth α] :
    skip (List α) = (right ;; while_neq ')' (skip α) ;; right) := rfl

/-! ## Key correctness theorem -/

/-- `skipRight d` correctly skips any well-formed string of depth ≤ `d`.
    Starting with the head on the opening `(`, it ends with the head on
    the first character after the closing `)`. -/
theorem skipRight_spec {d : ℕ} {s : String}
    (hwf  : WellFormed s)
    (hdep : parenDepth s ≤ d)
    (l r  : List Char) :
    (skipRight d).eval ⟨l, s.toList ++ r⟩ = some ⟨s.toList.reverse ++ l, r⟩ := sorry
/-
  Proof sketch (by strong induction on d):
  * Base case (d = 0): parenDepth s ≤ 0 contradicts WellFormed (which forces '(' at head,
    giving parenDepth ≥ 1).  Vacuously true.
  * Inductive step (d → d+1):
    Since s is well-formed, write s = "(" ++ inner ++ ")" where inner is a concatenation
    of well-formed sub-strings each of depth ≤ d.
    - `right` moves past '(', leaving head on inner ++ [')'] ++ r.
    - `while_neq ')'` iterates: each time head is on '(' (start of a sub-encoding of depth ≤ d),
      `skipRight d` (IH) advances past the entire sub-encoding.  This repeats until head is ')'.
    - The final `right` moves past ')'.
    - The accumulated `left` portion equals s.toList.reverse ++ l.
-/

/-- `skip α` correctly skips any encoded value of type `α`. -/
theorem skip_spec {α : Type*} [StrEnc α] [EncDepth α] (x : α) (l r : List Char) :
    (skip α).eval ⟨l, (StrEnc.enc x).toList ++ r⟩ =
      some ⟨(StrEnc.enc x).toList.reverse ++ l, r⟩ :=
  skipRight_spec (EncDepth.well_formed x) (EncDepth.depth_bound x) l r

/-! ## Navigation: `toArg` -/

/-- `toArg α ctorIdx fieldIdx` positions the head at the `fieldIdx`-th argument (0-indexed)
    of the encoding of a value of type `α` whose constructor has index `ctorIdx`.
    The head must start on the opening `(` of the encoded value.

    The skip machines for each field are derived automatically from `StrEnc.fieldDepths`:
    ```
    toArg α ctorIdx fieldIdx :=
      right ;;           -- move past the opening '('
      skip ℕ ;;          -- skip the constructor index
      skipRight d₀ ;;    -- skip field 0  (if fieldIdx > 0)
      skipRight d₁ ;;    -- skip field 1  (if fieldIdx > 1)
      …
      skipRight dᵢ₋₁    -- skip field i-1
    ```
    where `dⱼ = (StrEnc.fieldDepths (α := α))[ctorIdx][j]`.

    Semantics (informal):
    ```
    (toArg α ctorIdx fieldIdx).eval ⟨w₁, enc(c a₀ … aₙ) ++ w₂⟩ =
      some ⟨enc(aᵢ₋₁).rev ++ … ++ enc(a₀).rev ++ enc(idx).rev ++ ['('] ++ w₁,
            enc(aᵢ) ++ enc(aᵢ₊₁) ++ … ++ [')'] ++ w₂⟩
    ``` -/
def toArg (α : Type*) [StrEnc α] (ctorIdx fieldIdx : ℕ) : TM :=
  let depths := ((StrEnc.fieldDepths (α := α)).get? ctorIdx |>.getD #[]).toList
  let skipFields := depths.map skipRight
  right ;; skip ℕ ;; (skipFields.take fieldIdx).foldl seq idMach

/-- `toArg_spec`: `toArg` correctly positions the head on argument `fieldIdx`.
    After execution the left tape holds (reversed): the first `fieldIdx` field encodings,
    the constructor-index encoding, and the opening `(`;
    the right tape starts with the `fieldIdx`-th field encoding then the rest and `)`. -/
theorem toArg_spec
    {α : Type*} [StrEnc α] [EncDepth α]
    (ctorIdx fieldIdx : ℕ)
    (l r : List Char)
    (fieldEncodings : List String)
    (hfd  : ∀ j < fieldIdx,
              (StrEnc.fieldDepths (α := α)).get? ctorIdx |>.getD #[] |>.get? j |>.getD 0 =
              parenDepth (fieldEncodings.get? j |>.getD ""))
    (hlen : fieldIdx ≤ fieldEncodings.length) :
    let input  := Tape.mk l
      (("(" ++ encNat ctorIdx ++ String.join fieldEncodings ++ ")").toList ++ r)
    let left'  := (String.join (fieldEncodings.take fieldIdx)).toList.reverse ++
                  (encNat ctorIdx).toList.reverse ++ ['('] ++ l
    let right' := (String.join (fieldEncodings.drop fieldIdx)).toList ++ [')'] ++ r
    (toArg α ctorIdx fieldIdx).eval input = some (Tape.mk left' right') := sorry

/-! ## `EncDepth` instances for SAT types -/

/-- A `Literal` encoding has depth 2.
    `enc (pos n) = "(" ++ encNat 0 ++ encNat n ++ ")"` contains two depth-1 sub-encodings,
    so depth = 1 + 1 = 2. -/
instance : EncDepth Literal where
  depth_bound := sorry
  well_formed := sorry

-- `Clause = List Literal`: depth 2 + 1 = 3
instance : EncDepth (List Literal) where
  depth_bound := sorry
  well_formed := sorry

-- `Formula = List Clause = List (List Literal)`: depth 3 + 1 = 4
instance : EncDepth (List (List Literal)) where
  depth_bound := sorry
  well_formed := sorry

-- `Assignment = List ℕ`: depth 1 + 1 = 2
instance instEncDepthAssignment : EncDepth (List ℕ) where
  depth_bound := sorry
  well_formed := sorry

/-- `SATInput.mk` packs a `Formula` and an `Assignment` into one constructor.
    `enc (SATInput.mk φ σ) = "(" ++ encNat 0 ++ enc φ ++ enc σ ++ ")"`.
    depth = 1 + max(depth(Formula), depth(Assignment)) = 1 + max(4, 2) = 5. -/
instance : EncDepth SATInput where
  depth_bound := sorry
  well_formed := sorry

/-! ### Sanity checks -/

section DepthChecks
#eval parenDepth (StrEnc.enc (Literal.neg 1))                              -- 2 ✓
#eval parenDepth (StrEnc.enc ([Literal.neg 1] : Clause))                   -- 3 ✓
#eval parenDepth (StrEnc.enc ([[Literal.neg 1]] : Formula))                -- 4 ✓
#eval parenDepth (StrEnc.enc (SATInput.mk [[Literal.neg 1]] [0]))          -- 5 ✓
#eval StrEnc.depth (α := ℕ)                                                -- 1 ✓
#eval StrEnc.depth (α := Literal)                                          -- should be 2
#eval StrEnc.depth (α := Clause)                                           -- should be 3
#eval StrEnc.depth (α := Formula)                                          -- should be 4
#eval StrEnc.depth (α := SATInput)                                         -- should be 5
end DepthChecks

end TM
