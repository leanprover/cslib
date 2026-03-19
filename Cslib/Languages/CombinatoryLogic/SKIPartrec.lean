/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module

public import Cslib.Languages.CombinatoryLogic.Evaluation
public import Cslib.Languages.CombinatoryLogic.PartrecEquivalence
public import Mathlib.Computability.PartrecCode

@[expose] public section

/-!
# SKI-computable → Nat.Partrec (reverse direction)

This file proves the reverse direction of the SKI ↔ Partrec equivalence:
every function computed by an SKI term is partial recursive.

## Main definitions

- `SKI.encodeSKI` / `SKI.ofNatSKI`: encoding/decoding of SKI terms as natural numbers.
- `SKI.extractChurchK`: extract the natural number from a `churchK` normal form.
- `SKI.evalStepFn`: one step of evaluation as a total function (identity on normal forms).
- `SKI.evalNat`: the partial function `ℕ →. ℕ` computed by an SKI term.

## Main results

- `SKI.ski_eval_partrec`: the function computed by any SKI term is `Nat.Partrec`.
- `SKI.Computes.le_evalNat`: compatibility of `Computes` with `evalNat`.
- `SKI.partrec_iff_ski_evalNat`: equivalence of `Nat.Partrec` and SKI-computability.
-/

namespace Cslib

namespace SKI

open Red MRed Relation
open Nat.Partrec

/-! ### Encoding SKI terms as natural numbers -/

/-- Encode an SKI term as a natural number.
- `S → 0`, `K → 1`, `I → 2`
- `app a b → Nat.pair (encodeSKI a) (encodeSKI b) + 3` -/
def encodeSKI : SKI → ℕ
  | S => 0
  | K => 1
  | I => 2
  | a ⬝ b => Nat.pair (encodeSKI a) (encodeSKI b) + 3

/-- Decode a natural number to an SKI term. Total function (every `ℕ` maps to some SKI term).
Follows Mathlib's pattern for `ofNatCode` with inline termination proofs. -/
def ofNatSKI : ℕ → SKI
  | 0 => S
  | 1 => K
  | 2 => I
  | n + 3 =>
    have : n.unpair.1 < n + 3 :=
      Nat.lt_of_le_of_lt (Nat.unpair_left_le n) (by omega)
    have : n.unpair.2 < n + 3 :=
      Nat.lt_of_le_of_lt (Nat.unpair_right_le n) (by omega)
    ofNatSKI n.unpair.1 ⬝ ofNatSKI n.unpair.2

@[simp]
theorem ofNatSKI_encodeSKI (t : SKI) : ofNatSKI (encodeSKI t) = t := by
  induction t with
  | S => simp [encodeSKI, ofNatSKI]
  | K => simp [encodeSKI, ofNatSKI]
  | I => simp [encodeSKI, ofNatSKI]
  | app a b iha ihb => unfold encodeSKI ofNatSKI; simp [iha, ihb]

@[simp]
theorem encodeSKI_ofNatSKI (n : ℕ) : encodeSKI (ofNatSKI n) = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => simp [ofNatSKI, encodeSKI]
    | 1 => simp [ofNatSKI, encodeSKI]
    | 2 => simp [ofNatSKI, encodeSKI]
    | n + 3 =>
      unfold ofNatSKI
      simp only [encodeSKI]
      have h1 : n.unpair.1 ≤ n := Nat.unpair_left_le n
      have h2 : n.unpair.2 ≤ n := Nat.unpair_right_le n
      rw [ih n.unpair.1 (by omega), ih n.unpair.2 (by omega), Nat.pair_unpair]

/-- The encoding/decoding defines an equivalence `SKI ≃ ℕ`. -/
def equivNat : SKI ≃ ℕ where
  toFun := encodeSKI
  invFun := ofNatSKI
  left_inv := ofNatSKI_encodeSKI
  right_inv := encodeSKI_ofNatSKI

instance : Denumerable SKI := Denumerable.mk' equivNat

@[simp]
theorem encode_eq_encodeSKI (t : SKI) : Encodable.encode t = encodeSKI t := rfl

@[simp]
theorem ofNat_eq_ofNatSKI (n : ℕ) : Denumerable.ofNat SKI n = ofNatSKI n := rfl

/-! ### Extracting values from churchK normal forms -/

/-- Extract the natural number from a `churchK` normal form.
`churchK 0 = K`, `churchK (n+1) = K ⬝ churchK n`. -/
def extractChurchK : SKI → Option ℕ
  | K => some 0
  | K ⬝ x => (extractChurchK x).map (· + 1)
  | _ => none

@[simp]
theorem extractChurchK_churchK (n : ℕ) : extractChurchK (churchK n) = some n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [churchK, extractChurchK, ih]

theorem extractChurchK_some {t : SKI} {m : ℕ} (h : extractChurchK t = some m) :
    t = churchK m := by
  induction t generalizing m with
  | S => simp [extractChurchK] at h
  | K =>
    simp only [extractChurchK] at h
    cases h; rfl
  | I => simp [extractChurchK] at h
  | app a b _ ih_b =>
    match a with
    | K =>
      simp only [extractChurchK, Option.map_eq_some_iff] at h
      obtain ⟨m', hm', rfl⟩ := h
      have hb := ih_b hm'
      subst hb
      simp [churchK]
    | S => simp [extractChurchK] at h
    | I => simp [extractChurchK] at h
    | _ ⬝ _ => simp [extractChurchK] at h

/-! ### One-step evaluation as a total function -/

/-- One step of evaluation, returning the same term if already in normal form. -/
def evalStepFn (t : SKI) : SKI :=
  match t.evalStep with
  | .inl _ => t
  | .inr t' => t'

theorem evalStepFn_of_redexFree {t : SKI} (h : t.RedexFree) :
    evalStepFn t = t := by
  simp only [evalStepFn]
  have : (t.evalStep).isLeft = true := redexFree_iff_evalStep.mp h
  match ht : t.evalStep with
  | .inl _ => rfl
  | .inr _ => rw [ht] at this; cases this

theorem evalStepFn_red {t : SKI} (h : ¬t.RedexFree) :
    t ⭢ evalStepFn t := by
  simp only [evalStepFn]
  have : ¬(t.evalStep).isLeft = true := fun h' => h (redexFree_iff_evalStep.mpr h')
  match ht : t.evalStep with
  | .inl _ => rw [ht] at this; exact absurd rfl this
  | .inr t' => exact evalStep_right_correct t t' ht

/-- Iterating `evalStepFn` k times gives a multi-step reduction. -/
theorem iterate_evalStepFn_mred (t : SKI) (k : ℕ) :
    t ↠ evalStepFn^[k] t := by
  induction k with
  | zero => exact .refl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    set t' := evalStepFn^[k] t with ht'
    by_cases hrf : t'.RedexFree
    · rw [evalStepFn_of_redexFree hrf]; exact ih
    · exact Trans.trans ih (ReflTransGen.single (evalStepFn_red hrf))

/-- Once a term reaches a normal form, further iterations don't change it. -/
theorem iterate_evalStepFn_stable {t : SKI} (h : t.RedexFree) (k : ℕ) :
    evalStepFn^[k] t = t := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    exact evalStepFn_of_redexFree h

/-! ### The partial function computed by an SKI term -/

/-- The partial function `ℕ →. ℕ` computed by an SKI term `t`.

Given input `n`, we:
1. Build `t ⬝ toChurch(n) ⬝ K ⬝ K`
2. Iterate `evalStepFn` to search for a normal form
3. If the normal form matches `churchK m`, return `m` -/
noncomputable def evalNat (t : SKI) : ℕ →. ℕ := fun n =>
  Nat.rfindOpt (fun k =>
    extractChurchK (evalStepFn^[k] (t ⬝ toChurch n ⬝ K ⬝ K)))

/-! ### Key lemma: normal-order reduction reaches normal forms -/

/-- If `t ↠ nf` and `nf` is redex-free, then iterating `evalStepFn` eventually reaches `nf`.

This is the **standardization theorem** for SKI combinatory logic: normal-order
reduction (as implemented by `evalStep`) is normalizing — if a term has a normal form,
normal-order reduction finds it.

The proof requires showing that the specific evaluation strategy in `evalStep`
(leftmost-outermost / head reduction) avoids infinite loops when a normal form exists.
This is a deep result; see e.g. Curry & Feys (1958) or Hindley & Seldin (2008). -/
theorem exists_iterate_of_mred_redexFree {t nf : SKI}
    (hred : t ↠ nf) (hnf : nf.RedexFree) :
    ∃ k, evalStepFn^[k] t = nf := by
  sorry

/-! ### Monotonicity of the evaluation sequence -/

/-- Once `extractChurchK` succeeds at step `k`, it also succeeds at step `k'` for `k ≤ k'`
with the same result, because churchK values are redex-free and stable under iteration. -/
theorem extractChurchK_iterate_mono {t : SKI} {m k : ℕ}
    (hk : extractChurchK (evalStepFn^[k] t) = some m)
    {k' : ℕ} (hle : k ≤ k') :
    extractChurchK (evalStepFn^[k'] t) = some m := by
  have heq := extractChurchK_some hk
  rw [show k' = (k' - k) + k from by omega, Function.iterate_add_apply, heq,
    iterate_evalStepFn_stable (churchK_redexFree m), extractChurchK_churchK]

/-! ### Correctness: Computes t f → f ≤ evalNat t -/

/-- If `Computes t f`, then wherever `f` is defined, `evalNat t` agrees. -/
theorem Computes.le_evalNat {t : SKI} {f : ℕ →. ℕ} (hc : Computes t f) :
    ∀ n m, f n = Part.some m → evalNat t n = Part.some m := by
  intro n m hfn
  -- From Computes, get cm with IsChurch m cm and (t ⬝ toChurch n) ↠ cm
  obtain ⟨cm, hcm, hred⟩ := hc n (toChurch n) (toChurch_correct n) m hfn
  -- t ⬝ toChurch n ⬝ K ⬝ K ↠ cm ⬝ K ⬝ K ↠ Church m K K = churchK m
  have h_full : (t ⬝ toChurch n ⬝ K ⬝ K) ↠ churchK m :=
    Trans.trans (parallel_mRed (MRed.head K hred) .refl)
      (churchK_church m ▸ hcm K K)
  -- Find k such that iteration reaches churchK m
  obtain ⟨k, hk⟩ := exists_iterate_of_mred_redexFree h_full (churchK_redexFree m)
  -- evalNat uses rfindOpt; at step k, extractChurchK succeeds
  simp only [evalNat]
  rw [Part.eq_some_iff]
  apply (Nat.rfindOpt_mono
    (fun {_ _ _} hle hm => extractChurchK_iterate_mono hm hle)).mpr
  exact ⟨k, by rw [hk, extractChurchK_churchK]; rfl⟩

/-! ### Computability: evalNat t is Nat.Partrec -/

section Computability

/-- Encoding of `evalStepFn` operating directly on natural numbers. -/
def evalStepNat : ℕ → ℕ := fun n => encodeSKI (evalStepFn (ofNatSKI n))

/-- The encoding of `toChurch n` as a natural number. -/
def toChurchNat : ℕ → ℕ := fun n => encodeSKI (toChurch n)

/-- The encoding of `extractChurchK` operating on encoded terms. -/
def extractChurchKNat : ℕ → Option ℕ := fun n => extractChurchK (ofNatSKI n)

/-- `evalStepNat` correctly encodes `evalStepFn`. -/
theorem evalStepNat_correct (t : SKI) :
    evalStepNat (encodeSKI t) = encodeSKI (evalStepFn t) := by
  simp [evalStepNat]

/-- `extractChurchKNat` correctly encodes `extractChurchK`. -/
theorem extractChurchKNat_correct (t : SKI) :
    extractChurchKNat (encodeSKI t) = extractChurchK t := by
  simp [extractChurchKNat]

/-- The iterate of `evalStepNat` correctly encodes the iterate of `evalStepFn`. -/
theorem iterate_evalStepNat_correct (t : SKI) (k : ℕ) :
    evalStepNat^[k] (encodeSKI t) =
    encodeSKI (evalStepFn^[k] t) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      evalStepNat_correct]

/-! #### Primrec helpers (no sorry dependencies) -/

/-- Application on SKI terms is primitive recursive. -/
private theorem primrec_app : Primrec₂ (· ⬝ · : SKI → SKI → SKI) :=
  ((Primrec.ofNat SKI).comp
    (Primrec.nat_add.comp
      (Primrec₂.natPair.comp
        (Primrec.encode.comp .fst) (Primrec.encode.comp .snd))
      (Primrec.const 3))).of_eq
  fun ⟨a, b⟩ => by
    simp only [ofNat_eq_ofNatSKI, encode_eq_encodeSKI]
    change ofNatSKI (encodeSKI (a ⬝ b)) = _
    simp

/-- `toChurch` is primitive recursive. -/
private theorem primrec_toChurch : Primrec toChurch :=
  (Primrec.nat_iterate .id (.const (K ⬝ I))
    ((primrec_app.comp (.const SKI.Succ) .snd).to₂)).of_eq
  fun n => by
    change (fun x => SKI.Succ ⬝ x)^[n] (K ⬝ I) = toChurch n
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih, toChurch]

/-! #### Helper lemmas for computability proofs -/

/-- Encoding of `Option.map (· + 1)` in terms of the encoded option. -/
private theorem encode_option_map_succ (o : Option ℕ) :
    Encodable.encode (o.map (· + 1)) =
    if Encodable.encode o = 0 then 0 else Encodable.encode o + 1 := by
  cases o <;> simp

/-- `extractChurchK` returns `none` for applications whose left child is not `K`. -/
private theorem extractChurchK_app_neK {a b : SKI} (h : a ≠ K) :
    extractChurchK (a ⬝ b) = Option.none := by
  cases a with
  | K => exact absurd rfl h
  | S => rfl
  | I => rfl
  | app c d => rfl

/-! #### Nat.Primrec theorems -/

/-- Encoding of Church numerals is primitive recursive. -/
theorem nat_primrec_toChurchNat : Nat.Primrec toChurchNat :=
  Primrec.nat_iff.mp (Primrec.encode.comp primrec_toChurch)

/-- One step of SKI evaluation on encoded terms is primitive recursive.

This requires showing that the pattern matching in `evalStep` — which dispatches on the
top-level structure of the SKI term (S/K/I/app) and performs the appropriate reduction —
can be expressed as a primitive recursive function on the natural number encoding.
The proof would involve ~150-250 lines of careful case analysis on the encoding. -/
theorem nat_primrec_evalStepNat : Nat.Primrec evalStepNat := by
  sorry

/-- Extraction from churchK on encoded terms is primitive recursive.

Uses course-of-values recursion (`Primrec.nat_strong_rec`): the value at `n ≥ 3`
depends on the value at `(n - 3).unpair.2 < n`. -/
theorem nat_primrec_extractChurchKNat :
    Nat.Primrec fun n => Encodable.encode (extractChurchKNat n) := by
  rw [← Primrec.nat_iff]
  -- Define the body for course-of-values recursion
  let body : List ℕ → ℕ := fun hist =>
    if hist.length = 1 then 1
    else if 3 ≤ hist.length ∧ (hist.length - 3).unpair.1 = 1 then
      if (hist[(hist.length - 3).unpair.2]?).getD 0 = 0 then 0
      else (hist[(hist.length - 3).unpair.2]?).getD 0 + 1
    else 0
  -- Show body is Primrec
  have h_body : Primrec body := by
    have len : Primrec (List.length : List ℕ → ℕ) := Primrec.list_length
    have sub3 := Primrec.nat_sub.comp len (Primrec.const 3)
    have unp := Primrec.unpair.comp sub3
    have unp1 := Primrec.fst.comp unp
    have unp2 := Primrec.snd.comp unp
    have lkup : Primrec (fun hist : List ℕ => (hist[(hist.length - 3).unpair.2]?).getD 0) :=
      Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.id unp2) (Primrec.const 0)
    exact Primrec.ite (Primrec.eq.comp len (Primrec.const 1)) (Primrec.const 1)
      (Primrec.ite
        (PrimrecPred.and (Primrec.nat_le.comp (Primrec.const 3) len)
          (Primrec.eq.comp unp1 (Primrec.const 1)))
        (Primrec.ite (Primrec.eq.comp lkup (Primrec.const 0))
          (Primrec.const 0) (Primrec.succ.comp lkup))
        (Primrec.const 0))
  -- Apply course-of-values recursion
  exact (Primrec.nat_strong_rec
    (fun (_ : PUnit) n => Encodable.encode (extractChurchKNat n))
    (g := fun _ hist => some (body hist))
    (Primrec.option_some.comp (h_body.comp Primrec.snd))
    (by
      intro () n
      simp only [body, List.length_map, List.length_range]
      congr 1
      rcases n with _ | _ | _ | n
      · simp [extractChurchKNat, ofNatSKI, extractChurchK]
      · simp [extractChurchKNat, ofNatSKI, extractChurchK]
      · simp [extractChurchKNat, ofNatSKI, extractChurchK]
      · simp only [show ¬(n + 3 = 1) from by omega, ite_false,
          show 3 ≤ n + 3 from by omega, true_and, show n + 3 - 3 = n from by omega,
          extractChurchKNat, ofNatSKI]
        by_cases h : n.unpair.1 = 1
        · have hK : ofNatSKI 1 = K := by unfold ofNatSKI; rfl
          simp only [h, ite_true, hK, extractChurchK]
          have h_lt : n.unpair.2 < n + 3 :=
            Nat.lt_of_le_of_lt (Nat.unpair_right_le n) (by omega)
          simp only [List.getElem?_map, List.getElem?_range h_lt, Option.map_some,
            Option.getD_some]
          exact (encode_option_map_succ (extractChurchKNat n.unpair.2)).symm
        · simp only [h, ite_false]
          have : ofNatSKI n.unpair.1 ≠ K := by
            intro heq
            exact h ((encodeSKI_ofNatSKI _).symm.trans (congrArg encodeSKI heq))
          simp [extractChurchK_app_neK this])).comp (Primrec.const ()) Primrec.id

/-! #### Converting Nat.Primrec to Primrec on SKI -/

/-- `evalStepFn` is primitive recursive. -/
private theorem primrec_evalStepFn : Primrec evalStepFn :=
  ((Primrec.ofNat SKI).comp
    ((Primrec.nat_iff.mpr nat_primrec_evalStepNat).comp Primrec.encode)).of_eq
  fun t => by simp [evalStepNat]

/-- `extractChurchK` is primitive recursive. -/
private theorem primrec_extractChurchK : Primrec extractChurchK :=
  (Primrec.encode_iff.mp <|
    (Primrec.nat_iff.mpr nat_primrec_extractChurchKNat).comp Primrec.encode).of_eq
  fun t => by simp [extractChurchKNat]

/-- The function computed by any SKI term is partial recursive. -/
theorem ski_eval_partrec (t : SKI) : Nat.Partrec (evalNat t) := by
  rw [← Partrec.nat_iff]
  change Partrec fun n => Nat.rfindOpt fun k =>
    extractChurchK (evalStepFn^[k] (t ⬝ toChurch n ⬝ K ⬝ K))
  apply Partrec.rfindOpt
  -- Need: Computable₂ (fun n k => extractChurchK (evalStepFn^[k] (t ⬝ toChurch n ⬝ K ⬝ K)))
  apply Primrec₂.to_comp
  exact primrec_extractChurchK.comp
    (Primrec.nat_iterate .snd
      (primrec_app.comp (primrec_app.comp (primrec_app.comp
        (Primrec.const t) (primrec_toChurch.comp .fst))
        (Primrec.const K)) (Primrec.const K))
      (primrec_evalStepFn.comp₂ Primrec₂.right))

end Computability

/-! ### Combined equivalence -/

/-- Every partial recursive function has an SKI term whose `evalNat` agrees wherever `f`
is defined. This is weaker than full equality `evalNat t = f` but follows directly from
`Computes.le_evalNat` and `natPartrec_skiComputable`. -/
theorem nat_partrec_le_ski_evalNat {f : ℕ →. ℕ} (hf : Nat.Partrec f) :
    ∃ t : SKI, ∀ n m, f n = Part.some m → evalNat t n = Part.some m :=
  let ⟨t, ht⟩ := natPartrec_skiComputable f hf
  ⟨t, ht.le_evalNat⟩

/-- Full equivalence: a function is `Nat.Partrec` iff it is the function computed
by some SKI term.

The forward direction requires showing that the SKI term produced by `codeToSKINat`
computes *exactly* `f` (not just agreeing where `f` is defined). This needs a stronger
`ComputesExact` property of the construction: the term does not reduce to a Church
numeral on inputs where `f` is undefined. -/
theorem partrec_iff_ski_evalNat {f : ℕ →. ℕ} :
    Nat.Partrec f ↔ ∃ t : SKI, evalNat t = f := by
  constructor
  · intro hf
    obtain ⟨t, ht⟩ := natPartrec_skiComputable f hf
    -- ht.le_evalNat gives: wherever f is defined, evalNat t agrees.
    -- The missing piece: evalNat t is undefined wherever f is.
    exact ⟨t, sorry⟩
  · rintro ⟨t, rfl⟩
    exact ski_eval_partrec t

end SKI

end Cslib
