/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Mathlib.Data.List.Infix
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

/-!
# Complexity of Almost Constant Functions

A function `f : α → β` that is constant except for a finite number of arguments is computable in
constant time and zero space: the machine reads the encoded input while remembering the prefix it
has seen so far. After a finite number of steps it either reaches the end of the input or a point
where the prefix cannot be extended to the encoding of one of the finitely many exceptions. In both
cases, it emits the corresponding output one symbol at a time.

This result also holds for functions whose domain is already finite.

## Main Results

* `encodedComputableInTimeAndSpace_of_finite`: Every function on a finite type is computable in
    constant time and zero space, relative to any encoding.
* `encodedComputableInTimeAndSpace_of_exists_finite_ne`: Every function that is constant except
    for a finite number of arguments is computable in constant time and zero space, relative to any
    encoding.
* `encodedComputableInTimeAndSpace_of_const`: Every constant function is computable in constant
    time and zero space, relative to any encoding.
* `encodedComputableInTimeAndSpace_almostConstTime` and
    `encodedComputableInTimeAndSpace_finiteFunTime`: The same with explicit time bounds.

-/

namespace Turing.MultiTapeTM

section AlmostConstFun

/-! ## The machine computing a function that is constant outside a finite set

The machine `almostConstTM encIn encOut f S out` computes `f`, provided that the encoded output
of `f` is the fixed Boolean string `out` outside of the finite set `S`. -/

variable {α β : Type*} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {f : α → β}
  {S : Finset α} {out : List Bool}

/-- The prefixes of the encodings of the elements of a finite set `S`, together with the empty list.

The empty list has to be added explicitly for the case where `S` is empty: `almostConstTM` uses
the elements of this set as its states while reading the input, so the set has to contain the
starting state `[]` even if there is nothing to distinguish. -/
def encPrefixes (encIn : α ↪ List Bool) (S : Finset α) : Finset (List Bool) :=
  insert [] (S.biUnion fun a => (encIn a).inits.toFinset)

lemma mem_encPrefixes {p : List Bool} {a : α} (ha : a ∈ S) (h : p <+: encIn a) :
    p ∈ encPrefixes encIn S := by
  simp only [encPrefixes, Finset.mem_insert, Finset.mem_biUnion, List.mem_toFinset, List.mem_inits]
  exact Or.inr ⟨a, ha, h⟩

/-- The set of prefixes is closed under taking prefixes. -/
lemma prefix_mem_encPrefixes {p q : List Bool} (h : p ∈ encPrefixes encIn S) (hq : q <+: p) :
    q ∈ encPrefixes encIn S := by
  simp only [encPrefixes, Finset.mem_insert, Finset.mem_biUnion, List.mem_toFinset,
    List.mem_inits] at h ⊢
  rcases h with rfl | ⟨a, ha, hp⟩
  · exact Or.inl (List.prefix_nil.mp hq)
  · exact Or.inr ⟨a, ha, hq.trans hp⟩

/-- The suffixes of the default output and of the encoded values of `f` on `S`. -/
def outSuffixes (encOut : β ↪ List Bool) (f : α → β) (S : Finset α) (out : List Bool) :
    Finset (List Bool) :=
  out.tails.toFinset ∪ S.biUnion fun a => (encOut (f a)).tails.toFinset

lemma suffix_out_mem_outSuffixes {w : List Bool} (h : w <:+ out) :
    w ∈ outSuffixes encOut f S out := by
  simp only [outSuffixes, Finset.mem_union, List.mem_toFinset, List.mem_tails]
  exact Or.inl h

lemma mem_outSuffixes {w : List Bool} {a : α} (ha : a ∈ S) (h : w <:+ encOut (f a)) :
    w ∈ outSuffixes encOut f S out := by
  simp only [outSuffixes, Finset.mem_union, Finset.mem_biUnion, List.mem_toFinset, List.mem_tails]
  exact Or.inr ⟨a, ha, h⟩

/-- The set of suffixes is closed under taking suffixes. -/
lemma suffix_mem_outSuffixes {v w : List Bool} (h : w ∈ outSuffixes encOut f S out) (hv : v <:+ w) :
    v ∈ outSuffixes encOut f S out := by
  simp only [outSuffixes, Finset.mem_union, Finset.mem_biUnion, List.mem_toFinset,
    List.mem_tails] at h ⊢
  rcases h with h | ⟨a, ha, h⟩
  · exact Or.inl (hv.trans h)
  · exact Or.inr ⟨a, ha, hv.trans h⟩

lemma tail_mem_outSuffixes {w : List Bool} (h : w ∈ outSuffixes encOut f S out) :
    w.tail ∈ outSuffixes encOut f S out :=
  suffix_mem_outSuffixes h (List.tail_suffix w)

/-- If the encoded output is the default output outside of `S`, then every encoded output occurs
among the suffixes. -/
lemma encOut_mem_outSuffixes (h : ∀ a ∉ S, encOut (f a) = out) (a : α) :
    encOut (f a) ∈ outSuffixes encOut f S out := by
  by_cases ha : a ∈ S
  · exact mem_outSuffixes ha (List.suffix_refl _)
  · rw [h a ha]
    exact suffix_out_mem_outSuffixes (List.suffix_refl _)

/-- The states of the machine `almostConstTM`: either the prefix of the input read so far, or the
part of the output that still has to be emitted. -/
abbrev AlmostConstState (encIn : α ↪ List Bool) (encOut : β ↪ List Bool) (f : α → β)
    (S : Finset α) (out : List Bool) : Type :=
  {p : List Bool // p ∈ encPrefixes encIn S} ⊕ {w : List Bool // w ∈ outSuffixes encOut f S out}

open Classical in
/-- The function `f`, transported along the encodings of its domain and codomain: it maps the
encoding of an element of `S` to the encoding of its value under `f`, and every other list to the
default output. -/
noncomputable def encodedFun (encIn : α ↪ List Bool) (encOut : β ↪ List Bool) (f : α → β)
    (S : Finset α) (out : List Bool) (p : List Bool) : List Bool :=
  if h : ∃ a ∈ S, encIn a = p then encOut (f h.choose) else out

@[simp]
lemma encodedFun_enc {a : α} (ha : a ∈ S) :
    encodedFun encIn encOut f S out (encIn a) = encOut (f a) := by
  have hex : ∃ a' ∈ S, encIn a' = encIn a := ⟨a, ha, rfl⟩
  rw [encodedFun, dite_eq_left_of_eq_true (eq_true hex), encIn.injective hex.choose_spec.2]

@[simp]
lemma encodedFun_enc_of_notMem {a : α} (ha : a ∉ S) :
    encodedFun encIn encOut f S out (encIn a) = out := by
  have hex : ¬ ∃ a' ∈ S, encIn a' = encIn a := by
    rintro ⟨a', ha', h⟩
    exact ha (encIn.injective h ▸ ha')
  rw [encodedFun, dite_eq_right_of_eq_false (eq_false hex)]

lemma encodedFun_mem_outSuffixes (p : List Bool) :
    encodedFun encIn encOut f S out p ∈ outSuffixes encOut f S out := by
  rw [encodedFun]
  split
  · next h => exact mem_outSuffixes h.choose_spec.1 (List.suffix_refl _)
  · exact suffix_out_mem_outSuffixes (List.suffix_refl _)

open Classical in
/-- The machine computing a function that is constant outside of `S`. It has no work tapes.

While reading the input it remembers the prefix read so far. Once this prefix cannot be extended
to the encoding of an element of `S` anymore, or the blank behind the input is reached, it
switches to the state that holds the encoded output, which it then emits one symbol per step
before halting. -/
noncomputable def almostConstTM (encIn : α ↪ List Bool) (encOut : β ↪ List Bool) (f : α → β)
    (S : Finset α) (out : List Bool) :
    MultiTapeTM 0 Bool (AlmostConstState encIn encOut f S out) where
  q₀ := Sum.inl ⟨[], by simp [encPrefixes]⟩
  tr q input _ :=
    match q with
    | Sum.inl p =>
      match input with
      | some b =>
        if h : p.val ++ [b] ∈ encPrefixes encIn S then
          ⟨.pos, Fin.elim0, none, some (Sum.inl ⟨p.val ++ [b], h⟩)⟩
        else
          ⟨0, Fin.elim0, none,
            some (Sum.inr ⟨out, suffix_out_mem_outSuffixes (List.suffix_refl out)⟩)⟩
      | none =>
        ⟨0, Fin.elim0, none,
          some (Sum.inr ⟨encodedFun encIn encOut f S out p.val,
            encodedFun_mem_outSuffixes p.val⟩)⟩
    | Sum.inr w =>
      ⟨0, Fin.elim0, w.val.head?,
        if w.val = [] then none
        else some (Sum.inr ⟨w.val.tail, tail_mem_outSuffixes w.property⟩)⟩

/-- The configuration reached after `j` steps of reading the input. -/
lemma runFrom_read (a : α) {j : ℕ} (hj : j ≤ (encIn a).length)
    (hmem : (encIn a).take j ∈ encPrefixes encIn S) :
    (almostConstTM encIn encOut f S out).runFrom
        ((almostConstTM encIn encOut f S out).initCfg (encIn a)) j =
      { state := some (Sum.inl ⟨(encIn a).take j, hmem⟩),
        inputPos := ⟨1 + j, by omega⟩,
        workTapes := fun _ _ => none,
        workTapePos := fun _ => 0,
        output := [] } := by
  induction j with
  | zero =>
    simp only [runFrom_zero, initCfg, List.take_zero]
    ext <;> simp [almostConstTM]
  | succ j ih =>
    have hprefix : (encIn a).take j <+: (encIn a).take (j + 1) := by
      simp
    have hmem' : (encIn a).take j ∈ encPrefixes encIn S := prefix_mem_encPrefixes hmem hprefix
    have hcat : (encIn a).take j ++ [(encIn a)[j]] ∈ encPrefixes encIn S := by
      grind [List.take_concat_get']
    have hmove : moveInputPos (⟨1 + j, by omega⟩ : Fin ((encIn a).length + 2)) SignType.pos
        = ⟨1 + (j + 1), by omega⟩ := by
      grind [moveInputPos_pos_of_ne_right]
    have hstart : 1 + j ≠ 0 := by omega
    have hend : 1 + j ≠ (encIn a).length + 1 := by omega
    have hprev : 1 + j - 1 = j := by omega
    rw [runFrom_succ_eq_step', ih (by omega) hmem']
    simp only [step, almostConstTM, Cfg.inputSymbol, Fin.ext_iff, Fin.val_zero, hstart, hend,
      hprev, reduceDIte, hcat]
    exact Cfg.ext_zero_tapes (by grind [List.take_concat_get']) hmove (by simp)

/-- The configuration reached after having emitted the first `i` symbols of `w`, starting from a
configuration that is about to emit `w`. -/
lemma runFrom_write {input : List Bool} (pos : Fin (input.length + 2)) (o : List Bool)
    {w : List Bool} (hw : w ∈ outSuffixes encOut f S out) {i : ℕ} (hi : i ≤ w.length) :
    (almostConstTM encIn encOut f S out).runFrom
        { state := some (Sum.inr ⟨w, hw⟩), inputPos := pos, workTapes := fun _ _ => none,
          workTapePos := fun _ => 0, output := o } i =
      { state := some (Sum.inr ⟨w.drop i, suffix_mem_outSuffixes hw (w.drop_suffix i)⟩),
        inputPos := pos,
        workTapes := fun _ _ => none,
        workTapePos := fun _ => 0,
        output := o ++ w.take i } := by
  induction i with
  | zero => simp [runFrom_zero]
  | succ i ih =>
    have hilt : i < w.length := by omega
    have htake := List.take_concat_get' w i hilt
    have hnotdone : ¬ (w.length ≤ i) := by omega
    rw [runFrom_succ_eq_step', ih (by omega)]
    simp only [step, almostConstTM, List.head?_drop, List.getElem?_eq_getElem hilt,
      List.drop_eq_nil_iff, hnotdone, reduceIte, List.tail_drop, moveInputPos_zero,
      Option.toList_some]
    exact Cfg.ext_zero_tapes rfl rfl (by grind)

/-- Starting from a configuration that is about to emit `w`, the machine halts after `w.length + 1`
steps, having emitted `w`. -/
lemma runFrom_write_halted {input : List Bool} (pos : Fin (input.length + 2)) (o : List Bool)
    {w : List Bool} (hw : w ∈ outSuffixes encOut f S out) :
    (almostConstTM encIn encOut f S out).runFrom
        { state := some (Sum.inr ⟨w, hw⟩), inputPos := pos, workTapes := fun _ _ => none,
          workTapePos := fun _ => 0, output := o } (w.length + 1) =
      { state := none,
        inputPos := pos,
        workTapes := fun _ _ => none,
        workTapePos := fun _ => 0,
        output := o ++ w } := by
  rw [runFrom_succ_eq_step', runFrom_write pos o hw le_rfl]
  simp only [step, almostConstTM, List.drop_length, reduceIte, List.head?_nil, moveInputPos_zero,
    Option.toList_none, List.append_nil, List.take_length]
  exact Cfg.ext_zero_tapes rfl rfl (by simp)

/-- A constant time bound for the machine `almostConstTM`. -/
public def almostConstTime (encIn : α ↪ List Bool) (encOut : β ↪ List Bool) (f : α → β)
    (S : Finset α) (out : List Bool) : ℕ :=
  2 + out.length + S.sup fun a => (encIn a).length + (encOut (f a)).length

lemma length_le_sup_of_mem_encPrefixes {p : List Bool} (h : p ∈ encPrefixes encIn S) :
    p.length ≤ S.sup fun a => (encIn a).length + (encOut (f a)).length := by
  simp only [encPrefixes, Finset.mem_insert, Finset.mem_biUnion, List.mem_toFinset,
    List.mem_inits] at h
  rcases h with rfl | ⟨a, ha, hp⟩
  · simp
  · have hsup : (encIn a).length + (encOut (f a)).length ≤
        S.sup fun a => (encIn a).length + (encOut (f a)).length :=
      Finset.le_sup (f := fun a => (encIn a).length + (encOut (f a)).length) ha
    have := hp.length_le
    omega

/-- The machine reaches the state in which it starts emitting the encoded output after a number
of steps that is bounded independently of the input. -/
lemma reaches_write (h : ∀ a ∉ S, encOut (f a) = out) (a : α) :
    ∃ (j : ℕ) (hj : j ≤ (encIn a).length),
      j + (encOut (f a)).length ≤
        out.length + S.sup (fun a => (encIn a).length + (encOut (f a)).length) ∧
      (almostConstTM encIn encOut f S out).runFrom
          ((almostConstTM encIn encOut f S out).initCfg (encIn a)) (j + 1) =
        { state := some (Sum.inr ⟨encOut (f a), encOut_mem_outSuffixes h a⟩),
          inputPos := ⟨1 + j, by omega⟩,
          workTapes := fun _ _ => none,
          workTapePos := fun _ => 0,
          output := [] } := by
  classical
  set j := Nat.findGreatest (fun j => (encIn a).take j ∈ encPrefixes encIn S) (encIn a).length
    with hjdef
  have hmem : (encIn a).take j ∈ encPrefixes encIn S :=
    Nat.findGreatest_spec (P := fun j => (encIn a).take j ∈ encPrefixes encIn S)
      (Nat.zero_le _) (by simp [encPrefixes])
  have hjle : j ≤ (encIn a).length := Nat.findGreatest_le _
  have hjsup : j ≤ S.sup fun a => (encIn a).length + (encOut (f a)).length := by
    have hlen := length_le_sup_of_mem_encPrefixes (encOut := encOut) (f := f) hmem
    rw [List.length_take] at hlen
    omega
  use j, hjle
  constructor
  · by_cases ha : a ∈ S
    · grind [Finset.le_sup (f := fun a => (encIn a).length + (encOut (f a)).length) ha]
    · grind [h a ha]
  rw [runFrom_succ_eq_step', runFrom_read a hjle hmem]
  rcases eq_or_lt_of_le hjle with heq | hlt
  · -- the whole input has been read, so the machine decodes it
    have hend : 1 + j = (encIn a).length + 1 := by omega
    have hdec : encodedFun encIn encOut f S out ((encIn a).take j) = encOut (f a) := by
      rw [heq, List.take_length]
      by_cases ha : a ∈ S
      · exact encodedFun_enc ha
      · rw [encodedFun_enc_of_notMem ha, h a ha]
    simp only [step, almostConstTM, Cfg.inputSymbol, Fin.ext_iff, Fin.val_zero, hend,
      reduceDIte, dite_eq_ite, ite_self, hdec]
    exact Cfg.ext_zero_tapes rfl (by simp) (by simp)
  · -- the prefix read so far cannot be extended, so the machine emits the default output
    have hend : 1 + j ≠ (encIn a).length + 1 := by omega
    have hprev : 1 + j - 1 = j := by omega
    have hnotmem : (encIn a).take (j + 1) ∉ encPrefixes encIn S :=
      Nat.findGreatest_is_greatest (hjdef ▸ Nat.lt_succ_self j) (by omega)
    have hcat : (encIn a).take j ++ [(encIn a)[j]] ∉ encPrefixes encIn S := by
      grind [List.take_concat_get']
    have ha : a ∉ S := fun ha => hnotmem (mem_encPrefixes ha ((encIn a).take_prefix _))
    have hstart : 1 + j ≠ 0 := by omega
    simp only [step, almostConstTM, Cfg.inputSymbol, Fin.ext_iff, Fin.val_zero, hstart, hend,
      hprev, reduceDIte, hcat, moveInputPos_zero]
    refine Cfg.ext_zero_tapes ?_ (by simp) (by simp)
    simp only [Option.some.injEq, Sum.inr.injEq, Subtype.mk.injEq]
    exact (h a ha).symm

/-- The machine `almostConstTM` computes `f` in at most `almostConstTime` steps and no space. -/
lemma computesEncodedFunInTimeAndSpace_almostConstTM (h : ∀ a ∉ S, encOut (f a) = out) :
    ComputesEncodedFunInTimeAndSpace (almostConstTM encIn encOut f S out) encIn encOut f
      (fun _ => almostConstTime encIn encOut f S out) (fun _ => 0) := by
  intro a
  obtain ⟨j, hjle, hj, hrun⟩ := reaches_write h a
  have hhalt := (almostConstTM encIn encOut f S out).runFrom_add
    ((almostConstTM encIn encOut f S out).initCfg (encIn a)) (j + 1) ((encOut (f a)).length + 1)
  rw [hrun, runFrom_write_halted] at hhalt
  use j + 1 + ((encOut (f a)).length + 1)
  refine ⟨?_, 0, le_rfl, ?_⟩
  · change j + 1 + ((encOut (f a)).length + 1) ≤ almostConstTime encIn encOut f S out
    rw [almostConstTime]
    omega
  · unfold ComputesInTimeAndSpace
    rw [hhalt]
    simp

end AlmostConstFun

section Results

variable {α β : Type*} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}

/-- Every function whose encoded output is constant outside of a finite set is computable in time
`almostConstTime` and zero space. -/
public theorem encodedComputableInTimeAndSpace_almostConstTime
    (f : α → β) (S : Finset α) (out : List Bool) (h : ∀ a ∉ S, encOut (f a) = out) :
    EncodedComputableInTimeAndSpace f encIn encOut
      (fun _ => almostConstTime encIn encOut f S out) (fun _ => 0) :=
  ⟨0, AlmostConstState encIn encOut f S out, inferInstance, almostConstTM encIn encOut f S out,
    computesEncodedFunInTimeAndSpace_almostConstTM h⟩

/-- Every almost constant function is computable in constant time and zero space. -/
public theorem encodedComputableInTimeAndSpace_of_exists_finite_ne
    {f : α → β} (h : ∃ b : β, {a : α | f a ≠ b}.Finite) :
    ∃ c, EncodedComputableInTimeAndSpace f encIn encOut (fun _ => c) (fun _ => 0) := by
  obtain ⟨b, hb⟩ := h
  refine ⟨_, encodedComputableInTimeAndSpace_almostConstTime f hb.toFinset (encOut b) ?_⟩
  intro a ha
  simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at ha
  rw [ha]

/-- Every constant function is computable in constant time and zero space. -/
public theorem encodedComputableInTimeAndSpace_of_const {α β : Type*}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} (b : β) :
    ∃ c, EncodedComputableInTimeAndSpace (Function.const α b) encIn encOut
      (fun _ => c) (fun _ => 0) :=
  encodedComputableInTimeAndSpace_of_exists_finite_ne ⟨b, by simp⟩

/-- A constant time bound for functions on a finite type. -/
public noncomputable def finiteFunTime {α β : Type*} [Finite α] (encIn : α ↪ List Bool)
    (encOut : β ↪ List Bool) (f : α → β) : ℕ :=
  haveI := Fintype.ofFinite α
  almostConstTime encIn encOut f Finset.univ []

/-- Every function on a finite type is computable in time `finiteFunTime` and zero space. -/
public theorem encodedComputableInTimeAndSpace_finiteFunTime {α β : Type*} [Finite α]
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} (f : α → β) :
    EncodedComputableInTimeAndSpace f encIn encOut
      (fun _ => finiteFunTime encIn encOut f) (fun _ => 0) :=
  encodedComputableInTimeAndSpace_almostConstTime f (@Finset.univ α (Fintype.ofFinite α)) []
    fun a ha => absurd (@Finset.mem_univ α (Fintype.ofFinite α) a) ha

/-- Every function on a finite type is computable in constant time and zero space. -/
public theorem encodedComputableInTimeAndSpace_of_finite {α β : Type*} [Finite α]
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    (f : α → β) :
    ∃ c, EncodedComputableInTimeAndSpace f encIn encOut (fun _ => c) (fun _ => 0) :=
  ⟨_, encodedComputableInTimeAndSpace_finiteFunTime f⟩

end Results

end Turing.MultiTapeTM
