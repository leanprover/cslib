/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.AtomicRepresentation
public import Cslib.Foundations.RelationAlgebra.FastCycles
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Checked finite-network obstructions to representability

A refutation repeatedly asks for a missing composition witness and checks every permitted
one-point extension. A finite tree ending in impossible extensions rules out every atomic
representation, regardless of the cardinality of its base.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.NetworkRefutation

variable {j k n : ℕ}

/-- A complete matrix of atom labels on a finite list of points. -/
abbrev Network (j k n : ℕ) := Fin n → Fin n → Atom j k

/-- Diversity atoms in the catalogue's order, with each converse pair adjacent. -/
def alphabet (j k : ℕ) : List (DiversityAtom j k) :=
  (List.finRange j).map Sum.inl ++
    (List.finRange k).flatMap fun i => [Sum.inr (i, false), Sum.inr (i, true)]

private theorem mem_alphabet (a : DiversityAtom j k) : a ∈ alphabet j k := by
  rcases a with i | ⟨i, b⟩
  · simp [alphabet]
  · cases b <;> simp [alphabet]

/-- Enumerate rows lexicographically, pruning inconsistent prefixes before extending them. -/
def rows (j k : ℕ) : (n : ℕ) → (Fin n → List (DiversityAtom j k)) →
    (Fin n → Fin n → DiversityAtom j k → DiversityAtom j k → Bool) →
    List (Fin n → DiversityAtom j k)
  | 0, _, _ => [Fin.elim0]
  | n + 1, choices, compatible => (choices 0).flatMap fun a =>
      (rows j k n
        (fun i => (choices i.succ).filter fun b => compatible 0 i.succ a b)
        (fun i q => compatible i.succ q.succ)).map (Fin.cons a)

private theorem mem_rows (choices : Fin n → List (DiversityAtom j k))
    (compatible : Fin n → Fin n → DiversityAtom j k → DiversityAtom j k → Bool)
    (row : Fin n → DiversityAtom j k) (h : ∀ i, row i ∈ choices i)
    (hc : ∀ i q, i < q → compatible i q (row i) (row q) = true) :
    row ∈ rows j k n choices compatible := by
  induction n with
  | zero =>
    simp only [rows, List.mem_singleton]
    exact funext fun i => Fin.elim0 i
  | succ n ih =>
    rw [rows, List.mem_flatMap]
    refine ⟨row 0, h 0, ?_⟩
    rw [List.mem_map]
    refine ⟨Fin.tail row, ?_, Fin.cons_self_tail row⟩
    apply ih
    · intro i
      exact List.mem_filter.mpr ⟨h i.succ, hc 0 i.succ (Fin.succ_pos i)⟩
    · intro i q hiq
      exact hc i.succ q.succ (Fin.succ_lt_succ_iff.mpr hiq)

private theorem compatible_of_mem_rows (choices : Fin n → List (DiversityAtom j k))
    (compatible : Fin n → Fin n → DiversityAtom j k → DiversityAtom j k → Bool)
    (row : Fin n → DiversityAtom j k) (hr : row ∈ rows j k n choices compatible) :
    (∀ i, row i ∈ choices i) ∧
      ∀ i q, i < q → compatible i q (row i) (row q) = true := by
  induction n with
  | zero => exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ n ih =>
    simp only [rows, List.mem_flatMap, List.mem_map] at hr
    obtain ⟨a, ha, tail, ht, rfl⟩ := hr
    obtain ⟨hc, hp⟩ := ih _ _ _ ht
    constructor
    · intro i
      induction i using Fin.cases with
      | zero => exact ha
      | succ i => exact (List.mem_filter.mp (hc i)).1
    · intro i q hiq
      induction i using Fin.cases with
      | zero =>
        induction q using Fin.cases with
        | zero => exact (lt_irrefl _ hiq).elim
        | succ q => exact (List.mem_filter.mp (hc q)).2
      | succ i =>
        induction q using Fin.cases with
        | zero => exact (Fin.not_lt_zero _ hiq).elim
        | succ q => exact hp i q (Fin.succ_lt_succ_iff.mp hiq)

/-- Fix the requested witness legs before enumerating all other edge labels. -/
def rowChoices (x y : Fin n) (a b : Atom j k) (i : Fin n) : List (DiversityAtom j k) :=
  if i = x then a.toList else if i = y then (Atom.converse b).toList else alphabet j k

/-- Append a point using an extension row; reverse edges carry converse labels. -/
def extend (N : Network j k n) (row : Fin n → DiversityAtom j k) : Network j k (n + 1) :=
  Fin.lastCases (Fin.lastCases none fun i => Atom.converse (some (row i)))
    fun i => Fin.lastCases (some (row i)) (N i)

/-- All triangle-consistent extension rows realizing a specified two-edge witness. -/
def extensions (T : IntegralCycleTable j k) (N : Network j k n)
    (x y : Fin n) (a b : Atom j k) : List (Fin n → DiversityAtom j k) :=
  (rows j k n (rowChoices x y a b)
    (fun i q c d => decide (cycleClosure T.cycles (N i q) (some d) (some c)))).filter
      fun row => decide
    (some (row x) = a ∧ Atom.converse (some (row y)) = b ∧
      ∀ i q, i < q → cycleClosure T.cycles (N i q) (some (row q)) (some (row i)))

/-- Enumerate extensions using the packed table for each cycle lookup. -/
def extensionsCode (code : ℕ) (N : Network j k n)
    (x y : Fin n) (a b : Atom j k) : List (Fin n → DiversityAtom j k) :=
  (rows j k n (rowChoices x y a b)
    (fun i q c d => Code.bitAt code
      (Code.index (atomCount j k) (N i q).code (Atom.code (some d)) (Atom.code (some c))))).filter
      fun row => decide
    (some (row x) = a ∧ Atom.converse (some (row y)) = b)

/-- A verified table code gives exactly the same permitted network extensions. -/
theorem extensions_eq_of_encodes {T : IntegralCycleTable j k} {code : ℕ}
    (hcode : EncodesTable T.cycles code) (N : Network j k n)
    (x y : Fin n) (a b : Atom j k) :
    extensions T N x y a b = extensionsCode code N x y a b := by
  unfold EncodesTable at hcode
  simp only [extensions, extensionsCode, hcode]
  apply List.filter_congr
  intro row hr
  have hc := (compatible_of_mem_rows _ _ row hr).2
  simp only [decide_eq_true_eq] at hc
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact and_congr_right fun _ => and_iff_left hc

/-- Read a concrete matrix, defaulting missing entries to the identity atom. -/
def ofMatrix (M : List (List (Atom j k))) : Network j k n :=
  fun i q => (M.getD i.val []).getD q.val none

/-- Each node chooses a missing witness; its children cover all legal extensions in order. -/
inductive Certificate (j k : ℕ) where
  | node (x y : ℕ) (a b : Atom j k) (children : List (Certificate j k))
  | cache (matrix : List (List (Atom j k))) (child : Certificate j k)
  | subnetwork (vertices : List ℕ) (matrix : List (List (Atom j k)))
      (child : Certificate j k)

mutual
  /-- Check the chosen move and all its extension branches. -/
  def check {n : ℕ} (T : IntegralCycleTable j k) (N : Network j k n) : Certificate j k → Bool
    | .node x y a b children =>
      if hx : x < n then if hy : y < n then
        decide (cycleClosure T.cycles a b (N ⟨x, hx⟩ ⟨y, hy⟩) ∧
          ∀ z, ¬ (N ⟨x, hx⟩ z = a ∧ N z ⟨y, hy⟩ = b)) &&
          checkChildren T N (extensions T N ⟨x, hx⟩ ⟨y, hy⟩ a b) children
      else false else false
    | .cache matrix child =>
      decide (∀ i q, N i q = ofMatrix matrix i q) && check T (ofMatrix (n := n) matrix) child
    | .subnetwork vertices matrix child =>
      if h : ∀ i : Fin vertices.length, vertices[i] < n then
        decide (∀ i q : Fin vertices.length,
          N ⟨vertices[i], h i⟩ ⟨vertices[q], h q⟩ = ofMatrix matrix i q) &&
          check T (ofMatrix (n := vertices.length) matrix) child
      else false
  /-- Match each legal extension with exactly one checked child certificate. -/
  def checkChildren {n : ℕ} (T : IntegralCycleTable j k) (N : Network j k n)
      (rs : List (Fin n → DiversityAtom j k)) : List (Certificate j k) → Bool
    | [] => rs.isEmpty
    | c :: cs => match rs with
      | [] => false
      | row :: rest => check T (extend N row) c && checkChildren T N rest cs
end

mutual
  /-- Check an entire obstruction using the packed cycle table. -/
  def checkCode {n : ℕ} (code : ℕ) (N : Network j k n) : Certificate j k → Bool
    | .node x y a b children =>
      if hx : x < n then if hy : y < n then
        (Code.bitAt code (Code.index (atomCount j k) a.code b.code
          (N ⟨x, hx⟩ ⟨y, hy⟩).code) &&
          decide (∀ z, ¬ (N ⟨x, hx⟩ z = a ∧ N z ⟨y, hy⟩ = b))) &&
          checkChildrenCode code N (extensionsCode code N ⟨x, hx⟩ ⟨y, hy⟩ a b) children
      else false else false
    | .cache matrix child =>
      decide (∀ i q, N i q = ofMatrix matrix i q) &&
        checkCode code (ofMatrix (n := n) matrix) child
    | .subnetwork vertices matrix child =>
      if h : ∀ i : Fin vertices.length, vertices[i] < n then
        decide (∀ i q : Fin vertices.length,
          N ⟨vertices[i], h i⟩ ⟨vertices[q], h q⟩ = ofMatrix matrix i q) &&
          checkCode code (ofMatrix (n := vertices.length) matrix) child
      else false
  /-- Check the branches of an obstruction using the packed cycle table. -/
  def checkChildrenCode {n : ℕ} (code : ℕ) (N : Network j k n)
      (rs : List (Fin n → DiversityAtom j k)) : List (Certificate j k) → Bool
    | [] => rs.isEmpty
    | c :: cs => match rs with
      | [] => false
      | row :: rest => checkCode code (extend N row) c && checkChildrenCode code N rest cs
end

mutual
  /-- A verified table code gives the same result when checking an obstruction. -/
  theorem check_eq_of_encodes {n : ℕ} {T : IntegralCycleTable j k} {code : ℕ}
      (hcode : EncodesTable T.cycles code) (N : Network j k n) (c : Certificate j k) :
      check T N c = checkCode code N c := by
    cases c with
    | node x y a b children =>
      simp only [check, checkCode]
      split_ifs with hx hy <;> try rfl
      rw [hcode, Bool.decide_and, extensions_eq_of_encodes hcode,
        checkChildren_eq_of_encodes hcode]
    | cache matrix child =>
      simp only [check, checkCode, check_eq_of_encodes hcode]
    | subnetwork vertices matrix child =>
      simp only [check, checkCode]
      split_ifs <;> try rfl
      rw [check_eq_of_encodes hcode]
  /-- A verified table code gives the same result when checking obstruction branches. -/
  theorem checkChildren_eq_of_encodes {n : ℕ} {T : IntegralCycleTable j k} {code : ℕ}
      (hcode : EncodesTable T.cycles code) (N : Network j k n)
      (rs : List (Fin n → DiversityAtom j k)) (cs : List (Certificate j k)) :
      checkChildren T N rs cs = checkChildrenCode code N rs cs := by
    cases cs with
    | nil => rfl
    | cons c cs =>
      cases rs with
      | nil => rfl
      | cons row rest =>
        change (_ && _) = (_ && _)
        rw [check_eq_of_encodes hcode, checkChildren_eq_of_encodes hcode]
end

/-- A node checks once its move and all extension branches have been checked separately. -/
theorem check_node_of (T : IntegralCycleTable j k) (N : Network j k n)
    (x y : Fin n) (a b : Atom j k) (children : List (Certificate j k))
    (hmove : cycleClosure T.cycles a b (N x y) ∧
      ∀ z, ¬ (N x z = a ∧ N z y = b))
    (hchildren : checkChildren T N (extensions T N x y a b) children = true) :
    check T N (.node x.val y.val a b children) = true := by
  simp only [check, dite_eq_left x.isLt, dite_eq_left y.isLt, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hmove, hchildren⟩

/-- A cached concrete matrix replaces the current network only after checking equality. -/
theorem check_cache (T : IntegralCycleTable j k) (N : Network j k n)
    (M : List (List (Atom j k))) (c : Certificate j k) :
    check T N (.cache M c) =
      (decide (∀ i q, N i q = ofMatrix M i q) && check T (ofMatrix (n := n) M) c) := rfl

/-- Reuse a checked obstruction on a selected subnetwork. -/
theorem check_subnetwork_of (T : IntegralCycleTable j k) (N : Network j k n)
    (vertices : List ℕ) (M : List (List (Atom j k))) (c : Certificate j k)
    (hbound : ∀ i : Fin vertices.length, vertices[i] < n)
    (hmatrix : ∀ i q : Fin vertices.length,
      N ⟨vertices[i], hbound i⟩ ⟨vertices[q], hbound q⟩ = ofMatrix M i q)
    (hchecked : check T (ofMatrix (n := vertices.length) M) c = true) :
    check T N (.subnetwork vertices M c) = true := by
  rw [check, dite_eq_left hbound, hchecked, Bool.and_true, decide_eq_true_eq]
  exact hmatrix

/-- A finite network occurs inside an atomic representation. Distinctness is not assumed. -/
def Realizes {T : IntegralCycleTable j k} {Base : Type*} (r : AtomRepresentation T Base)
    (N : Network j k n) : Prop :=
  ∃ v : Fin n → Base, ∀ i q, r.label (v i) (v q) = N i q

private theorem realizes_extension {T : IntegralCycleTable j k} {Base : Type*}
    (r : AtomRepresentation T Base) (N : Network j k n) (v : Fin n → Base)
    (hv : ∀ i q, r.label (v i) (v q) = N i q) (x y : Fin n) (a b : Atom j k)
    (hc : cycleClosure T.cycles a b (N x y))
    (hmissing : ∀ z, ¬ (N x z = a ∧ N z y = b)) :
    ∃ row ∈ extensions T N x y a b, Realizes r (extend N row) := by
  classical
  obtain ⟨z, hxz, hzy⟩ := (r.composition a b (v x) (v y)).mp (hv x y ▸ hc)
  have hne (i : Fin n) : r.label (v i) z ≠ none := by
    intro h
    have heq := (r.identity (v i) z).mp h
    apply hmissing i
    constructor
    · rw [← hv x i, heq]
      exact hxz
    · rw [← hv i y, heq]
      exact hzy
  have hex (i : Fin n) : ∃ c, some c = r.label (v i) z :=
    Option.ne_none_iff_exists.mp (hne i)
  choose row hrow using hex
  refine ⟨row, ?_, ?_⟩
  · rw [extensions, List.mem_filter]
    refine ⟨?_, ?_⟩
    · apply mem_rows
      · intro i
        unfold rowChoices
        split_ifs with hix hiy
        · subst i
          rw [← hxz, ← hrow]
          simp
        · subst i
          rw [← hzy, r.converse, ← hrow]
          simp
        · exact mem_alphabet _
      · intro i q _
        rw [decide_eq_true_eq, hrow, hrow, ← hv]
        exact (r.composition _ _ _ _).mpr ⟨v q, rfl, rfl⟩
    rw [decide_eq_true_eq]
    refine ⟨(hrow x).trans hxz, ?_, ?_⟩
    · rw [hrow, ← r.converse]
      exact hzy
    · intro i q _
      rw [hrow, hrow, ← hv]
      exact (r.composition _ _ _ _).mpr ⟨v q, rfl, rfl⟩
  · refine ⟨Fin.lastCases z v, ?_⟩
    intro i q
    induction i using Fin.lastCases <;> induction q using Fin.lastCases
    · simpa only [extend, Fin.lastCases_last] using (r.identity z z).mpr rfl
    · simpa only [extend, Fin.lastCases_last, Fin.lastCases_castSucc, hrow] using
        r.converse (v _) z
    · simpa only [extend, Fin.lastCases_last, Fin.lastCases_castSucc] using (hrow _).symm
    · simpa only [extend, Fin.lastCases_castSucc] using hv _ _

mutual
  /-- A checked certificate refutes every realization of its initial network. -/
  theorem check_sound {n : ℕ} (T : IntegralCycleTable j k) (N : Network j k n)
      (c : Certificate j k) (h : check T N c = true) {Base : Type*}
      (r : AtomRepresentation T Base) : ¬ Realizes r N := by
    cases c with
    | node x y a b children =>
      simp only [check] at h
      split_ifs at h with hx hy
      obtain ⟨hmove, hchildren⟩ := by simpa only [Bool.and_eq_true] using h
      rw [decide_eq_true_eq] at hmove
      rintro ⟨v, hv⟩
      obtain ⟨row, hrow, hr⟩ := realizes_extension r N v hv _ _ a b hmove.1 hmove.2
      exact checkChildren_sound T N _ children hchildren r row hrow hr
    | cache matrix child =>
      rw [check, Bool.and_eq_true, decide_eq_true_eq] at h
      have heq : N = ofMatrix matrix := funext fun i => funext (h.1 i)
      rw [heq]
      exact check_sound T (ofMatrix matrix) child h.2 r
    | subnetwork vertices matrix child =>
      rw [check] at h
      split_ifs at h with hbound
      rw [Bool.and_eq_true, decide_eq_true_eq] at h
      rintro ⟨v, hv⟩
      apply check_sound T (ofMatrix matrix) child h.2 r
      refine ⟨fun i => v ⟨vertices[i], hbound i⟩, ?_⟩
      intro i q
      exact (hv _ _).trans (h.1 i q)
  /-- Every checked extension branch refutes the corresponding enlarged network. -/
  theorem checkChildren_sound {n : ℕ} (T : IntegralCycleTable j k) (N : Network j k n)
      (rs : List (Fin n → DiversityAtom j k)) (cs : List (Certificate j k))
      (h : checkChildren T N rs cs = true) {Base : Type*} (r : AtomRepresentation T Base)
      (row : Fin n → DiversityAtom j k) (hr : row ∈ rs) : ¬ Realizes r (extend N row) := by
    cases cs with
    | nil =>
      simp only [checkChildren, List.isEmpty_iff] at h
      simp [h] at hr
    | cons c cs =>
      cases rs with
      | nil => simp at hr
      | cons first rest =>
        change (_ && _) = true at h
        rw [Bool.and_eq_true] at h
        obtain ⟨hc, hcs⟩ := h
        rcases List.mem_cons.mp hr with rfl | hr
        · exact check_sound T (extend N row) c hc r
        · exact checkChildren_sound T N rest cs hcs r row hr
end

/-- The two-point network whose forward edge has the specified label. -/
def initial (a : Atom j k) : Network j k 2 :=
  ![![none, a], ![Atom.converse a, none]]

/-- Refuting the two-point network of one atom proves nonrepresentability of its algebra. -/
theorem not_representable (T : IntegralCycleTable j k) (a : Atom j k) (c : Certificate j k)
    (h : check T (initial a) c = true) : ¬ Representable (Complex T) := by
  intro hr
  obtain ⟨Base, ⟨r⟩⟩ := (representable_iff_nonempty_atomRepresentation T).mp hr
  obtain ⟨⟨x, y⟩, hxy⟩ := r.surjective a
  apply check_sound T (initial a) c h r
  refine ⟨![x, y], ?_⟩
  intro i q
  fin_cases i <;> fin_cases q
  · exact (r.identity x x).mpr rfl
  · exact hxy
  · exact (r.converse x y).trans (congrArg Atom.converse hxy)
  · exact (r.identity y y).mpr rfl

end Cslib.RelationAlgebra.NetworkRefutation
