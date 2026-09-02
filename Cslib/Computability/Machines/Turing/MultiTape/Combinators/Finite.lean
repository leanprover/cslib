/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Mathlib.Data.List.Infix
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

/-!
# Complexity of Functions over Finite Types

Every function `f : α → β` between finite types is computable in constant time and zero space:
the machine reads the encoded input while remembering the prefix it has seen so far (there are
only finitely many such prefixes), then decodes the input and emits the encoded output one symbol
per step.

Since `α` and `β` are finite, the lengthes of the encoded input and output are bounded by a
constant, which is why the time bound is a constant.

## Main Results

* `encodedComputableInTimeAndSpace_of_finite`: Every function between finite types is computable
    in constant time and zero space, relative to any encoding.
* `encodedComputableInTimeAndSpace_finiteFunTime`: The same as above with an explicit time bound.

-/

namespace Turing.MultiTapeTM

section FiniteFun

/-! ## The machine computing a function between finite types -/

variable {α β : Type*} [Finite α] {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {f : α → β}

/-- The prefixes of the encodings of the elements of `α`, together with the empty list.

The empty list has to be added explicitly for the case where `α` is empty: `finiteFunTM` uses
the elements of this set as its states while reading the input, so the set has to contain the
starting state `[]` even if there is no input to read. -/
noncomputable def encPrefixes (encIn : α ↪ List Bool) : Finset (List Bool) :=
  haveI := Fintype.ofFinite α
  insert [] (Finset.univ.biUnion fun a : α => (encIn a).inits.toFinset)

/-- The suffixes of the encoded values of `f`, together with the empty list.

The empty list has to be added explicitly for the case where `α` is empty: `finiteFunTM` uses
the elements of this set as its states while writing the output, so the set has to contain the
final state `[]` even if there is no output to write. -/
noncomputable def outSuffixes (encOut : β ↪ List Bool) (f : α → β) : Finset (List Bool) :=
  haveI := Fintype.ofFinite α
  insert [] (Finset.univ.biUnion fun a : α => (encOut (f a)).tails.toFinset)

lemma nil_mem_encPrefixes : [] ∈ encPrefixes encIn := by
  simp [encPrefixes]

lemma mem_encPrefixes {p : List Bool} {a : α} (h : p <+: encIn a) :
    p ∈ encPrefixes encIn := by
  classical
  simp only [encPrefixes, Finset.mem_insert, Finset.mem_biUnion, List.mem_toFinset, List.mem_inits]
  exact Or.inr ⟨a, by simp, h⟩

lemma nil_mem_outSuffixes : [] ∈ outSuffixes encOut f := by
  simp [outSuffixes]

lemma mem_outSuffixes {w : List Bool} {a : α} (h : w <:+ encOut (f a)) :
    w ∈ outSuffixes encOut f := by
  classical
  simp only [outSuffixes, Finset.mem_insert, Finset.mem_biUnion, List.mem_toFinset, List.mem_tails]
  exact Or.inr ⟨a, by simp, h⟩

lemma tail_mem_outSuffixes {w : List Bool} (h : w ∈ outSuffixes encOut f) :
    w.tail ∈ outSuffixes encOut f := by
  classical
  simp only [outSuffixes, Finset.mem_insert, Finset.mem_biUnion, List.mem_toFinset,
    List.mem_tails] at h ⊢
  rcases h with rfl | ⟨a, -, ha⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨a, by simp, (List.tail_suffix w).trans ha⟩

/-- The states of the machine `finiteFunTM`: either the prefix of the input read so far, or the
part of the output that still has to be emitted. -/
abbrev FiniteFunState (encIn : α ↪ List Bool) (encOut : β ↪ List Bool) (f : α → β) : Type :=
  {p : List Bool // p ∈ encPrefixes encIn} ⊕ {w : List Bool // w ∈ outSuffixes encOut f}

open Classical in
/-- The output that has to be emitted after having read the full input `p`. -/
noncomputable def decodeOutput (encIn : α ↪ List Bool) (encOut : β ↪ List Bool) (f : α → β)
    (p : List Bool) : List Bool :=
  if h : ∃ a : α, encIn a = p then encOut (f h.choose) else []

omit [Finite α] in
@[simp]
lemma decodeOutput_enc (a : α) : decodeOutput encIn encOut f (encIn a) = encOut (f a) := by
  have hex : ∃ a' : α, encIn a' = encIn a := ⟨a, rfl⟩
  rw [decodeOutput, dite_eq_left_of_eq_true (eq_true hex), encIn.injective hex.choose_spec]

lemma decodeOutput_mem_outSuffixes (p : List Bool) :
    decodeOutput encIn encOut f p ∈ outSuffixes encOut f := by
  rw [decodeOutput]
  split
  · exact mem_outSuffixes (List.suffix_refl _)
  · exact nil_mem_outSuffixes

open Classical in
/-- The machine computing a function between finite types. It has no work tapes.

While reading the input it remembers the prefix read so far. Upon reaching the blank behind the
input it switches to the state that holds the encoded output, which it then emits one symbol per
step before halting. -/
noncomputable def finiteFunTM (encIn : α ↪ List Bool) (encOut : β ↪ List Bool) (f : α → β) :
    MultiTapeTM 0 Bool (FiniteFunState encIn encOut f) where
  q₀ := Sum.inl ⟨[], nil_mem_encPrefixes⟩
  tr q input _ :=
    match q with
    | Sum.inl p =>
      match input with
      | some b =>
        if h : p.val ++ [b] ∈ encPrefixes encIn then
          ⟨.pos, Fin.elim0, none, some (Sum.inl ⟨p.val ++ [b], h⟩)⟩
        else
          ⟨0, Fin.elim0, none, none⟩
      | none =>
        ⟨0, Fin.elim0, none,
          some (Sum.inr ⟨decodeOutput encIn encOut f p.val,
            decodeOutput_mem_outSuffixes p.val⟩)⟩
    | Sum.inr w =>
      ⟨0, Fin.elim0, w.val.head?,
        if w.val = [] then none
        else some (Sum.inr ⟨w.val.tail, tail_mem_outSuffixes w.property⟩)⟩

/-- The configuration reached after `j` steps of reading the input. -/
lemma runFrom_read (a : α) {j : ℕ} (hj : j ≤ (encIn a).length) :
    (finiteFunTM encIn encOut f).runFrom ((finiteFunTM encIn encOut f).initCfg (encIn a)) j =
      { state := some (Sum.inl ⟨(encIn a).take j,
          mem_encPrefixes ((encIn a).take_prefix j)⟩),
        inputPos := ⟨1 + j, by omega⟩,
        workTapes := fun _ _ => none,
        workTapePos := fun _ => 0,
        output := [] } := by
  induction j with
  | zero =>
    simp only [runFrom_zero, initCfg, List.take_zero]
    ext <;> simp [finiteFunTM]
  | succ j ih =>
    have hmem : (encIn a).take j ++ [(encIn a)[j]] ∈ encPrefixes encIn := by
      grind [mem_encPrefixes, List.take_concat_get']
    have hmove : moveInputPos (⟨1 + j, by omega⟩ : Fin ((encIn a).length + 2)) SignType.pos
        = ⟨1 + (j + 1), by omega⟩ := by
      grind [moveInputPos_pos_of_ne_right]
    have hstart : 1 + j ≠ 0 := by omega
    have hend : 1 + j ≠ (encIn a).length + 1 := by omega
    have hprev : 1 + j - 1 = j := by omega
    rw [runFrom_succ_eq_step', ih (by omega)]
    simp only [step, finiteFunTM, Cfg.inputSymbol, Fin.ext_iff, Fin.val_zero, hstart, hend, hprev,
      reduceDIte, hmem]
    exact Cfg.ext_zero_tapes (by grind [List.take_concat_get']) hmove (by simp)

/-- The configuration reached after having read the whole input and emitted the first `i` symbols
of the output. -/
lemma runFrom_write (a : α) {i : ℕ} (hi : i ≤ (encOut (f a)).length) :
    (finiteFunTM encIn encOut f).runFrom ((finiteFunTM encIn encOut f).initCfg (encIn a))
        ((encIn a).length + 1 + i) =
      { state := some (Sum.inr ⟨(encOut (f a)).drop i,
          mem_outSuffixes ((encOut (f a)).drop_suffix i)⟩),
        inputPos := ⟨1 + (encIn a).length, by omega⟩,
        workTapes := fun _ _ => none,
        workTapePos := fun _ => 0,
        output := (encOut (f a)).take i } := by
  induction i with
  | zero =>
    have hend : 1 + (encIn a).length = (encIn a).length + 1 := by omega
    rw [runFrom_succ_eq_step', runFrom_read a le_rfl]
    simp only [step, finiteFunTM, Cfg.inputSymbol, Fin.ext_iff, Fin.val_zero, List.take_length,
      List.take_zero, List.drop_zero, hend, ↓reduceDIte, dite_eq_ite, ite_self, decodeOutput_enc]
    exact Cfg.ext_zero_tapes rfl (by simp) (by simp)
  | succ i ih =>
    have hilt : i < (encOut (f a)).length := by omega
    have htake := List.take_concat_get' (encOut (f a)) i hilt
    have hnotdone : ¬ ((encOut (f a)).length ≤ i) := by omega
    rw [← Nat.add_assoc, runFrom_succ_eq_step', ih (by omega)]
    simp only [step, finiteFunTM, List.head?_drop, List.getElem?_eq_getElem hilt,
      List.drop_eq_nil_iff, hnotdone, reduceIte, List.tail_drop, moveInputPos_zero,
      Option.toList_some]
    exact Cfg.ext_zero_tapes rfl rfl htake

/-- The machine `finiteFunTM` computes `f` in `(encIn a).length + (encOut (f a)).length + 2` steps
and no space. -/
lemma computesInTimeAndSpace_finiteFunTM (a : α) :
    ComputesInTimeAndSpace (finiteFunTM encIn encOut f) (encIn a) (encOut (f a))
      ((encIn a).length + (encOut (f a)).length + 2) 0 := by
  have h := runFrom_write (encIn := encIn) a (le_refl (encOut (f a)).length)
  have hsplit : (encIn a).length + (encOut (f a)).length + 2
      = ((encIn a).length + 1 + (encOut (f a)).length) + 1 := by omega
  rw [ComputesInTimeAndSpace, hsplit, runFrom_succ_eq_step', h]
  refine ⟨?_, ?_, ?_⟩
  · simp [step, finiteFunTM]
  · simp [step, finiteFunTM]
  · exact spaceUsed_zero_tapes_eq_zero _ _ rfl

/-- A constant time bound for the machine `finiteFunTM`, valid for all inputs since `α` is
finite. -/
public noncomputable def finiteFunTime
    (encIn : α ↪ List Bool) (encOut : β ↪ List Bool) (f : α → β) : ℕ :=
  haveI := Fintype.ofFinite α
  2 + Finset.univ.sup fun a : α => (encIn a).length + (encOut (f a)).length

lemma time_le_finiteFunTime (a : α) :
    (encIn a).length + (encOut (f a)).length + 2 ≤ finiteFunTime encIn encOut f := by
  rw [finiteFunTime]
  have h : (encIn a).length + (encOut (f a)).length ≤
      (@Finset.univ α (Fintype.ofFinite α)).sup
        fun a : α => (encIn a).length + (encOut (f a)).length :=
    Finset.le_sup (f := fun a : α => (encIn a).length + (encOut (f a)).length)
      (@Finset.mem_univ α (Fintype.ofFinite α) a)
  omega

lemma computesEncodedFunInTimeAndSpace_finiteFunTM :
    ComputesEncodedFunInTimeAndSpace (finiteFunTM encIn encOut f) encIn encOut f
      (fun _ => finiteFunTime encIn encOut f) (fun _ => 0) := fun a =>
  ⟨_, time_le_finiteFunTime a, 0, le_rfl,
    computesInTimeAndSpace_finiteFunTM a⟩

end FiniteFun

/-- Every function between finite types is computable in time `finiteFunTime` and zero space. -/
public theorem encodedComputableInTimeAndSpace_finiteFunTime {α β : Type*} [Finite α]
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    (f : α → β) :
    EncodedComputableInTimeAndSpace f encIn encOut
      (fun _ => finiteFunTime encIn encOut f) (fun _ => 0) :=
  ⟨0, FiniteFunState encIn encOut f, inferInstance,
    finiteFunTM encIn encOut f, computesEncodedFunInTimeAndSpace_finiteFunTM⟩

/-- Every function between finite types is computable in constant time and zero space. -/
public theorem encodedComputableInTimeAndSpace_of_finite {α β : Type*} [Finite α]
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    (f : α → β) :
    ∃ c, EncodedComputableInTimeAndSpace f encIn encOut (fun _ => c) (fun _ => 0) :=
  ⟨_, encodedComputableInTimeAndSpace_finiteFunTime f⟩

end Turing.MultiTapeTM
