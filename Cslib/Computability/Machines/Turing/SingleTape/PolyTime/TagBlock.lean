/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
import Cslib.Computability.Machines.Turing.SingleTape.PolyTime.Basic
import Cslib.Computability.Machines.Turing.SingleTape.PolyTime.TapeHelpers

/-!
# The `tagBlock` machine and decoding of encoded pairs

Since `Bitstring` carries the identity encoding, `decode` for pairs of bitstrings sends `l` to
`some (x, w)` exactly when `l` begins with a well-formed self-delimiting block. At the level of
encodings this is the function `tagBlock`, which prepends `true` (the `some` tag) to well-formed
inputs and erases ill-formed ones — a validating parser, computable in linear time by a single
left-to-right scan followed by a shift-right-by-one (accept) or a leftward erase (reject).

## Main results

* `PolyTimeComputable_tagBlock`: `tagBlock` is computable in linear time by `tagBlockComputer`.
* `IsComputableInPolyTime_decode`: decoding a bitstring as a pair of bitstrings is
  polynomial-time computable.
-/

open Computability Turing

namespace ComplexityTheory

section TagBlockMachine

open Cslib.Turing Cslib.Turing.SingleTapeTM Cslib.Turing.StackTape

/-- Does the bitstring begin with a well-formed self-delimiting block? -/
def hasBlock : List Bool → Bool
  | [] => false
  | false :: _ => true
  | true :: _ :: rest => hasBlock rest
  | [true] => false

/-- Tag a bitstring with a leading `true` if it begins with a well-formed self-delimiting block,
and return the empty bitstring otherwise. On pair encodings this computes `encode ∘ decode`. -/
def tagBlock (l : List Bool) : List Bool :=
  bif hasBlock l then true :: l else []

private lemma hasBlock_eq_isSome_undelimit : ∀ (n : ℕ) (l : List Bool), l.length = n →
    hasBlock l = (BitstringEncoding.undelimit l).isSome := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro l hlen
    match l with
    | [] => rfl
    | false :: rest => rfl
    | true :: [] => rfl
    | true :: b :: rest =>
      have hrec := ih rest.length (by simp only [List.length_cons] at hlen; omega) rest rfl
      simp only [hasBlock, BitstringEncoding.undelimit, hrec]
      cases BitstringEncoding.undelimit rest <;> rfl

private lemma undelimit_eq_some : ∀ (n : ℕ) (l : List Bool), l.length = n →
    ∀ x w, BitstringEncoding.undelimit l = some (x, w) →
      l = BitstringEncoding.delimit x ++ w := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro l hlen x w h
    match l with
    | [] => simp [BitstringEncoding.undelimit] at h
    | false :: rest =>
      simp only [BitstringEncoding.undelimit, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    | true :: [] => simp [BitstringEncoding.undelimit] at h
    | true :: b :: rest =>
      simp only [BitstringEncoding.undelimit, Option.map_eq_some_iff] at h
      obtain ⟨⟨p₁, p₂⟩, hp, heq⟩ := h
      have hrec := ih rest.length (by simp only [List.length_cons] at hlen; omega) rest rfl
        p₁ p₂ hp
      obtain ⟨rfl, rfl⟩ : b :: p₁ = x ∧ p₂ = w := by simpa [Prod.ext_iff] using heq
      simp only [hrec, BitstringEncoding.delimit, List.cons_append]

/-- States of the `tagBlock` machine. -/
inductive TBState
  /-- Parsing: expecting a pair marker `true` or the block terminator `false`. -/
  | pTF
  /-- Parsing: expecting the payload bit after a marker. -/
  | pB
  /-- Terminator seen (input valid): scan to the end of the input. -/
  | pOk
  /-- Accept phase: reading the rightmost unshifted cell. -/
  | shRead
  /-- Accept phase: writing the carried bit one cell to the right. -/
  | shWrite (b : Bool)
  /-- Accept phase: stepping back over the moving blank gap. -/
  | shBack
  /-- Accept phase: writing the leading `true` tag and halting. -/
  | shTag
  /-- Reject phase: erasing the input leftward. -/
  | erL
  deriving DecidableEq, Fintype

/-- The validating parser: scan the input checking that it begins with a well-formed
self-delimiting block; if so, shift the input one cell to the right (right to left, carrying one
bit at a time) and write a leading `true`; otherwise erase the input. Computes `tagBlock` in
linear time. -/
def tagBlockComputer : SingleTapeTM Bool where
  State := TBState
  q₀ := .pTF
  tr q sym :=
    match q, sym with
    -- parse phase
    | .pTF, some true => (⟨some true, some .right⟩, some .pB)
    | .pTF, some false => (⟨some false, some .right⟩, some .pOk)
    | .pTF, none => (⟨none, some .left⟩, some .erL)          -- no terminator: reject
    | .pB, some b => (⟨some b, some .right⟩, some .pTF)
    | .pB, none => (⟨none, some .left⟩, some .erL)           -- lone marker: reject
    | .pOk, some b => (⟨some b, some .right⟩, some .pOk)
    | .pOk, none => (⟨none, some .left⟩, some .shRead)       -- accept: shift and tag
    -- accept phase: shift the input right one cell, working right to left
    | .shRead, some b => (⟨none, some .right⟩, some (.shWrite b))
    | .shRead, none => (⟨none, some .right⟩, some .shTag)    -- everything shifted
    | .shWrite b, _ => (⟨some b, some .left⟩, some .shBack)
    | .shBack, _ => (⟨none, some .left⟩, some .shRead)
    | .shTag, _ => (⟨some true, none⟩, none)
    -- reject phase
    | .erL, some _ => (⟨none, some .left⟩, some .erL)
    | .erL, none => (⟨none, none⟩, none)

/-! #### Parse phase -/

private lemma tb_pTF_true (done rest : List Bool) :
    tagBlockComputer.TransitionRelation ⟨some .pTF, splitTape done (true :: rest)⟩
      ⟨some .pB, splitTape (done ++ [true]) rest⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, tagBlockComputer, splitTape_head_cons,
    splitTape_scan]

private lemma tb_pTF_false (done rest : List Bool) :
    tagBlockComputer.TransitionRelation ⟨some .pTF, splitTape done (false :: rest)⟩
      ⟨some .pOk, splitTape (done ++ [false]) rest⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, tagBlockComputer, splitTape_head_cons,
    splitTape_scan]

private lemma tb_pB_step (done : List Bool) (b : Bool) (rest : List Bool) :
    tagBlockComputer.TransitionRelation ⟨some .pB, splitTape done (b :: rest)⟩
      ⟨some .pTF, splitTape (done ++ [b]) rest⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, tagBlockComputer, splitTape_head_cons,
    splitTape_scan]

private lemma tb_pOk_step (done : List Bool) (b : Bool) (rest : List Bool) :
    tagBlockComputer.TransitionRelation ⟨some .pOk, splitTape done (b :: rest)⟩
      ⟨some .pOk, splitTape (done ++ [b]) rest⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, tagBlockComputer, splitTape_head_cons,
    splitTape_scan]

open Relation in
private lemma tb_pOk_scan : ∀ (rest done : List Bool),
    RelatesWithinSteps tagBlockComputer.TransitionRelation
      ⟨some .pOk, splitTape done rest⟩ ⟨some .pOk, splitTape (done ++ rest) []⟩ rest.length := by
  intro rest
  induction rest with
  | nil =>
    intro done
    rw [List.append_nil]
    simp only [List.length_nil]
    exact RelatesWithinSteps.refl _
  | cons b r ih =>
    intro done
    have h1 := RelatesWithinSteps.single (tb_pOk_step done b r)
    have h2 := ih (done ++ [b])
    rw [show done ++ [b] ++ r = done ++ b :: r by simp] at h2
    exact (h1.trans h2).of_le (by simp only [List.length_cons]; omega)

open Relation in
/-- The scan on inputs beginning with a well-formed block ends at the right end in `pOk`. -/
private lemma tb_scan_accept : ∀ (n : ℕ) (rest done : List Bool), rest.length = n →
    hasBlock rest = true →
    RelatesWithinSteps tagBlockComputer.TransitionRelation
      ⟨some .pTF, splitTape done rest⟩ ⟨some .pOk, splitTape (done ++ rest) []⟩ rest.length := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro rest done hlen hblock
    match rest with
    | [] => simp [hasBlock] at hblock
    | false :: r =>
      have h1 := RelatesWithinSteps.single (tb_pTF_false done r)
      have h2 := tb_pOk_scan r (done ++ [false])
      rw [show done ++ [false] ++ r = done ++ false :: r by simp] at h2
      exact (h1.trans h2).of_le (by simp only [List.length_cons]; omega)
    | true :: [] => simp [hasBlock] at hblock
    | true :: b :: r =>
      have h1 := RelatesWithinSteps.single (tb_pTF_true done (b :: r))
      have h2 := RelatesWithinSteps.single (tb_pB_step (done ++ [true]) b r)
      have h3 := ih r.length (by simp only [List.length_cons] at hlen; omega) r
        (done ++ [true] ++ [b]) rfl (by simpa [hasBlock] using hblock)
      rw [show done ++ [true] ++ [b] ++ r = done ++ true :: b :: r by simp] at h3
      refine (h1.trans (h2.trans h3)).of_le ?_
      simp only [List.length_cons]
      omega

/-! #### Accept phase: shift right by one and tag -/

/-- Tape during the accept-phase shift: `done ++ [c]` is still unshifted (head on `c`), and
`shifted` has been moved one cell to the right, separated by a single blank. -/
private def shiftTape (done : List Bool) (c : Bool) (shifted : List Bool) : BiTape Bool :=
  ⟨some c, StackTape.mapSome done.reverse, StackTape.cons none (StackTape.mapSome shifted)⟩

private lemma tb_pOk_exit (l' : List Bool) (c : Bool) :
    tagBlockComputer.TransitionRelation ⟨some .pOk, splitTape (l' ++ [c]) []⟩
      ⟨some .shRead, shiftTape l' c []⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, tagBlockComputer, splitTape, shiftTape,
    List.head?_nil, List.tail_nil, mapSome_nil, BiTape.write, BiTape.optionMove, BiTape.move,
    BiTape.moveLeft, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, mapSome_head, mapSome_tail, List.head?_cons, List.tail_cons,
    cons_none_empty]

private lemma tb_shift_read (L : StackTape Bool) (c : Bool) (shifted : List Bool) :
    tagBlockComputer.TransitionRelation
      ⟨some .shRead, ⟨some c, L, StackTape.cons none (StackTape.mapSome shifted)⟩⟩
      ⟨some (.shWrite c), ⟨none, StackTape.cons none L, StackTape.mapSome shifted⟩⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, tagBlockComputer, BiTape.write,
    BiTape.optionMove, BiTape.move, BiTape.moveRight, StackTape.head_cons, StackTape.tail_cons]

private lemma tb_shift_write (L : StackTape Bool) (c : Bool) (shifted : List Bool) :
    tagBlockComputer.TransitionRelation
      ⟨some (.shWrite c), ⟨none, StackTape.cons none L, StackTape.mapSome shifted⟩⟩
      ⟨some .shBack, ⟨none, L, StackTape.mapSome (c :: shifted)⟩⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, tagBlockComputer, BiTape.write,
    BiTape.optionMove, BiTape.move, BiTape.moveLeft, StackTape.head_cons, StackTape.tail_cons,
    cons_some_mapSome]

private lemma tb_shift_back (D : List Bool) (c' : Bool) (rest : List Bool) :
    tagBlockComputer.TransitionRelation
      ⟨some .shBack, ⟨none, StackTape.mapSome (D ++ [c']).reverse, StackTape.mapSome rest⟩⟩
      ⟨some .shRead, shiftTape D c' rest⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, tagBlockComputer, shiftTape,
    List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, BiTape.write, BiTape.optionMove, BiTape.move, BiTape.moveLeft,
    mapSome_head, mapSome_tail, List.head?_cons, List.tail_cons]

private lemma tb_shift_back_nil (rest : List Bool) :
    tagBlockComputer.TransitionRelation
      ⟨some .shBack, ⟨none, ∅, StackTape.mapSome rest⟩⟩
      ⟨some .shRead, ⟨none, ∅, StackTape.cons none (StackTape.mapSome rest)⟩⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, tagBlockComputer, BiTape.write,
    BiTape.optionMove, BiTape.move, BiTape.moveLeft, empty_head, empty_tail]

private lemma tb_shift_read_nil (rest : List Bool) :
    tagBlockComputer.TransitionRelation
      ⟨some .shRead, ⟨none, ∅, StackTape.cons none (StackTape.mapSome rest)⟩⟩
      ⟨some .shTag, ⟨none, ∅, StackTape.mapSome rest⟩⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, tagBlockComputer, BiTape.write,
    BiTape.optionMove, BiTape.move, BiTape.moveRight, StackTape.head_cons, StackTape.tail_cons,
    cons_none_empty]

private lemma tb_shift_tag (rest : List Bool) :
    tagBlockComputer.TransitionRelation ⟨some .shTag, ⟨none, ∅, StackTape.mapSome rest⟩⟩
      ⟨none, BiTape.mk₁ (true :: rest)⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, tagBlockComputer, BiTape.mk₁, BiTape.write,
    BiTape.optionMove]

open Relation in
/-- The full shift-and-tag: from the rightmost cell, halt on `true :: input`. -/
private lemma tb_shift : ∀ (done : List Bool) (c : Bool) (shifted : List Bool),
    RelatesWithinSteps tagBlockComputer.TransitionRelation
      ⟨some .shRead, shiftTape done c shifted⟩
      ⟨none, BiTape.mk₁ (true :: (done ++ c :: shifted))⟩ (3 * done.length + 5) := by
  intro done
  induction done using List.reverseRecOn with
  | nil =>
    intro c shifted
    simp only [shiftTape, List.reverse_nil, mapSome_nil, List.nil_append, List.length_nil,
      Nat.mul_zero, Nat.zero_add]
    have h1 := RelatesWithinSteps.single (tb_shift_read ∅ c shifted)
    have h2 := RelatesWithinSteps.single (tb_shift_write ∅ c shifted)
    have h3 := RelatesWithinSteps.single (tb_shift_back_nil (c :: shifted))
    have h4 := RelatesWithinSteps.single (tb_shift_read_nil (c :: shifted))
    have h5 := RelatesWithinSteps.single (tb_shift_tag (c :: shifted))
    exact (h1.trans (h2.trans (h3.trans (h4.trans h5)))).of_le (by omega)
  | append_singleton D d ih =>
    intro c shifted
    have h1 := RelatesWithinSteps.single
      (tb_shift_read (StackTape.mapSome (D ++ [d]).reverse) c shifted)
    have h2 := RelatesWithinSteps.single
      (tb_shift_write (StackTape.mapSome (D ++ [d]).reverse) c shifted)
    have h3 := RelatesWithinSteps.single (tb_shift_back D d (c :: shifted))
    have h4 := ih d (c :: shifted)
    rw [show D ++ d :: c :: shifted = (D ++ [d]) ++ c :: shifted by simp] at h4
    have hchain := h1.trans (h2.trans (h3.trans h4))
    refine hchain.of_le ?_
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

/-! #### Reject phase: erase the input -/

private lemma tb_pTF_reject (D : List Bool) (c : Bool) :
    tagBlockComputer.TransitionRelation ⟨some .pTF, splitTape (D ++ [c]) []⟩
      ⟨some .erL, splitTape D [c]⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, tagBlockComputer, splitTape, List.head?_nil,
    List.tail_nil, List.head?_cons, List.tail_cons, mapSome_nil, BiTape.write, BiTape.optionMove,
    BiTape.move, BiTape.moveLeft, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append, mapSome_head, mapSome_tail, cons_none_empty]

private lemma tb_pB_reject (D : List Bool) (c : Bool) :
    tagBlockComputer.TransitionRelation ⟨some .pB, splitTape (D ++ [c]) []⟩
      ⟨some .erL, splitTape D [c]⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, tagBlockComputer, splitTape, List.head?_nil,
    List.tail_nil, List.head?_cons, List.tail_cons, mapSome_nil, BiTape.write, BiTape.optionMove,
    BiTape.move, BiTape.moveLeft, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append, mapSome_head, mapSome_tail, cons_none_empty]

private lemma tb_pTF_reject_nil :
    tagBlockComputer.TransitionRelation ⟨some .pTF, splitTape [] []⟩
      ⟨some .erL, BiTape.mk₁ []⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, tagBlockComputer, splitTape, List.head?_nil,
    List.tail_nil, List.reverse_nil, mapSome_nil, BiTape.write, BiTape.optionMove, BiTape.move,
    BiTape.moveLeft, empty_head, empty_tail, cons_none_empty, BiTape.mk₁, BiTape.empty_eq_nil,
    BiTape.nil]

private lemma tb_erL_step (D : List Bool) (c' c : Bool) :
    tagBlockComputer.TransitionRelation ⟨some .erL, splitTape (D ++ [c']) [c]⟩
      ⟨some .erL, splitTape D [c']⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, tagBlockComputer, splitTape, List.head?_cons,
    List.tail_cons, mapSome_nil, BiTape.write, BiTape.optionMove, BiTape.move, BiTape.moveLeft,
    List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, mapSome_head, mapSome_tail, cons_none_empty]

private lemma tb_erL_last (c : Bool) :
    tagBlockComputer.TransitionRelation ⟨some .erL, splitTape [] [c]⟩
      ⟨some .erL, BiTape.mk₁ []⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, tagBlockComputer, splitTape, List.head?_cons,
    List.tail_cons, mapSome_nil, List.reverse_nil, BiTape.write, BiTape.optionMove, BiTape.move,
    BiTape.moveLeft, empty_head, empty_tail, cons_none_empty, BiTape.mk₁, BiTape.empty_eq_nil,
    BiTape.nil]

private lemma tb_erL_halt :
    tagBlockComputer.TransitionRelation ⟨some .erL, BiTape.mk₁ []⟩ ⟨none, BiTape.mk₁ []⟩ := by
  simp only [TransitionRelation, SingleTapeTM.step, tagBlockComputer, BiTape.mk₁, BiTape.write,
    BiTape.optionMove, BiTape.empty_eq_nil, BiTape.nil]

open Relation in
private lemma tb_erase : ∀ (D : List Bool) (c : Bool),
    RelatesWithinSteps tagBlockComputer.TransitionRelation
      ⟨some .erL, splitTape D [c]⟩ ⟨none, BiTape.mk₁ []⟩ (D.length + 2) := by
  intro D
  induction D using List.reverseRecOn with
  | nil =>
    intro c
    exact ((RelatesWithinSteps.single (tb_erL_last c)).trans
      (RelatesWithinSteps.single tb_erL_halt)).of_le (by simp)
  | append_singleton D' c' ih =>
    intro c
    have hchain := (RelatesWithinSteps.single (tb_erL_step D' c' c)).trans (ih c')
    refine hchain.of_le ?_
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

open Relation in
/-- The scan on inputs not beginning with a well-formed block ends by erasing everything. -/
private lemma tb_scan_reject : ∀ (n : ℕ) (rest done : List Bool), rest.length = n →
    hasBlock rest = false →
    RelatesWithinSteps tagBlockComputer.TransitionRelation
      ⟨some .pTF, splitTape done rest⟩ ⟨none, BiTape.mk₁ []⟩
      (2 * rest.length + done.length + 4) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro rest done hlen hblock
    match rest with
    | [] =>
      rcases List.eq_nil_or_concat done with rfl | ⟨D, c, rfl⟩
      · exact ((RelatesWithinSteps.single tb_pTF_reject_nil).trans
          (RelatesWithinSteps.single tb_erL_halt)).of_le (by simp)
      · rw [List.concat_eq_append]
        have hchain := (RelatesWithinSteps.single (tb_pTF_reject D c)).trans (tb_erase D c)
        refine hchain.of_le ?_
        simp only [List.length_nil, List.length_append, List.length_cons]
        omega
    | false :: r => simp [hasBlock] at hblock
    | true :: [] =>
      have h1 := RelatesWithinSteps.single (tb_pTF_true done [])
      have h2 := RelatesWithinSteps.single (tb_pB_reject done true)
      have h3 := tb_erase done true
      refine (h1.trans (h2.trans h3)).of_le ?_
      simp only [List.length_cons, List.length_nil]
      omega
    | true :: b :: r =>
      have h1 := RelatesWithinSteps.single (tb_pTF_true done (b :: r))
      have h2 := RelatesWithinSteps.single (tb_pB_step (done ++ [true]) b r)
      have h3 := ih r.length (by simp only [List.length_cons] at hlen; omega) r
        (done ++ [true] ++ [b]) rfl (by simpa [hasBlock] using hblock)
      refine (h1.trans (h2.trans h3)).of_le ?_
      simp only [List.length_cons, List.length_append, List.length_nil]
      omega

open Relation Polynomial in
/-- `tagBlock` is computable in linear time by `tagBlockComputer`. -/
theorem PolyTimeComputable_tagBlock :
    Nonempty (Cslib.Turing.SingleTapeTM.PolyTimeComputable tagBlock) :=
  ⟨{ tm := tagBlockComputer
     timeBound := fun n => 4 * n + 4
     poly := C 4 * X + C 4
     bounds := fun n => by simp only [eval_add, eval_mul, eval_C, eval_X]; omega
     outputsFunInTime := fun a => by
       simp only [OutputsWithinTime, initCfg, haltCfg]
       cases hb : hasBlock a with
       | false =>
         have h := tb_scan_reject a.length a [] rfl hb
         rw [splitTape_nil_left] at h
         rw [show tagBlock a = [] by simp [tagBlock, hb]]
         refine h.of_le ?_
         simp only [List.length_nil]
         omega
       | true =>
         have hne : a ≠ [] := by rintro rfl; simp [hasBlock] at hb
         obtain ⟨l', c, rfl⟩ := (List.eq_nil_or_concat a).resolve_left hne
         rw [List.concat_eq_append] at hb ⊢
         have h1 := tb_scan_accept (l' ++ [c]).length (l' ++ [c]) [] rfl hb
         rw [splitTape_nil_left, List.nil_append] at h1
         have h2 := RelatesWithinSteps.single (tb_pOk_exit l' c)
         have h3 := tb_shift l' c []
         rw [show tagBlock (l' ++ [c]) = true :: (l' ++ [c]) by simp [tagBlock, hb]]
         refine (h1.trans (h2.trans h3)).of_le ?_
         simp only [List.length_append, List.length_cons, List.length_nil]
         omega } ⟩

private lemma encode_option_none :
    BitstringEncoding.encode (none : Option (Bitstring × Bitstring)) = ([] : List Bool) := rfl

private lemma encode_option_some (x w : List Bool) :
    BitstringEncoding.encode (some (Bitstring.ofList x, Bitstring.ofList w))
      = true :: (BitstringEncoding.delimit x ++ w) := rfl

/-- The `tagBlock` function computes `encode ∘ decode` for pairs of bitstrings, at the level of
raw `List Bool` inputs. -/
private lemma tagBlock_eq_encode_decodePair (l : List Bool) :
    tagBlock l
      = BitstringEncoding.encode
          (BitstringEncoding.decodePair (α := Bitstring) (β := Bitstring) l) := by
  cases h : BitstringEncoding.undelimit l with
  | none =>
    have hd : BitstringEncoding.decodePair (α := Bitstring) (β := Bitstring) l = none := by
      simp [BitstringEncoding.decodePair, h]
    have hb : hasBlock l = false := by
      rw [hasBlock_eq_isSome_undelimit l.length l rfl, h]; rfl
    rw [hd, encode_option_none]
    simp [tagBlock, hb]
  | some p =>
    obtain ⟨x, w⟩ := p
    have hd : BitstringEncoding.decodePair (α := Bitstring) (β := Bitstring) l
        = some (Bitstring.ofList x, Bitstring.ofList w) := by
      simp [BitstringEncoding.decodePair, h, BitstringEncoding.decode_bitstring]
    have hb : hasBlock l = true := by
      rw [hasBlock_eq_isSome_undelimit l.length l rfl, h]; rfl
    have hl : l = BitstringEncoding.delimit x ++ w :=
      undelimit_eq_some l.length l rfl x w h
    rw [hd, encode_option_some, ← hl]
    simp [tagBlock, hb]

end TagBlockMachine

/-- Decoding a bitstring as a pair of bitstrings is polynomial-time computable: the machine
validates that the input begins with a well-formed self-delimiting block, tagging it with a
leading `true` (the `some` tag) if so and erasing it otherwise. -/
lemma IsComputableInPolyTime_decode :
    IsComputableInPolyTime (α := Bitstring)
      (BitstringEncoding.decode (α := Bitstring × Bitstring)) := by
  obtain ⟨m⟩ := PolyTimeComputable_tagBlock
  refine ⟨tagBlock, ⟨m⟩, fun l =>
    (tagBlock_eq_encode_decodePair (BitstringEncoding.encode l)).trans ?_⟩
  -- `decodePair (encode l)` and `decode l` agree definitionally: `encode` on a `Bitstring` is
  -- the identity and `decode` on pairs is `decodePair`.
  rfl


end ComplexityTheory
