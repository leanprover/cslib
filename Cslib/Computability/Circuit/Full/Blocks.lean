/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Full.Aggregation
public import Cslib.Computability.Circuit.Full.Decoder
public import Cslib.Computability.Circuit.Full.Dictionary

/-!
# Blocked table lookup

An address selects one of `B` blocks and one of `t` cells within that block.
`blockIndicator` marks the selected cell. For a nonzero marker, a prescription
on one block returns the addressed table entry when that block is selected,
and zero otherwise. Keeping the first nonzero contribution, or zero if all vanish,
therefore returns the addressed entry.

A block dictionary contains every prescription obtained by assigning values to that
block's cells. A fixed table chooses one prescription from each block by wiring;
the selector then performs its lookup. All tables with the same address use the
same dictionaries. This is the sharing step in Lupanov's construction.

`synthesis_lookups` counts only gates added after zero and all cell indicators are
available. It builds the dictionaries once and then combines the chosen prescriptions
for each table. Table entries determine which dictionary outputs to use; they are
fixed when constructing the circuit. Dictionary gates encode the marker and all
possible assigned values.

`synthesis_coordinateDictionaries` supplies the cell indicators by decoding available
coordinates. An injective placement of coordinate tuples into cells allows padding:
unused cells reuse the zero wire. `synthesis_sections` then assembles a function
whose table depends on a section index. It masks each table lookup to zero outside
its section and selects the surviving value, reusing the dictionaries for every section.
-/

@[expose] public section

namespace Cslib.Circuits.Full

variable {U : Type*} {n k d B t : ℕ} {s : Set ((Fin n → U) → U)}

/-- Return `marker` when the address selects cell `(b, i)`, and zero otherwise. -/
def blockIndicator [Zero U] (marker : U)
    (address : (Fin n → U) → Fin B × Fin t) (b : Fin B) (i : Fin t) : (Fin n → U) → U :=
  fun x => if address x = (b, i) then marker else 0

variable [DecidableEq U]

/-- A block prescription returns the addressed table entry on its block, and zero elsewhere. -/
theorem prescription_blockIndicator [Zero U] (marker : U) (hm : marker ≠ 0)
    (address : (Fin n → U) → Fin B × Fin t) (b : Fin B)
    (v : Fin B × Fin t → U) (x : Fin n → U) :
    prescription 0 marker (blockIndicator marker address b) (fun i => v (b, i)) x =
      if (address x).1 = b then v (address x) else 0 := by
  split_ifs with hb
  · simpa [← hb] using
      prescription_eq 0 marker (blockIndicator marker address b) (fun i => v (b, i))
        x (address x).2 (by simp [blockIndicator, ← hb]) (by
          intro j hj
          simp [blockIndicator, Prod.ext_iff, hj.symm, hm.symm])
  · apply prescription_eq_default
    intro i
    simp [blockIndicator, Prod.ext_iff, hb, hm.symm]

/-- Summing one prescription from each block returns the addressed table entry. -/
theorem sum_prescription_blockIndicator [AddCommMonoid U] (marker : U) (hm : marker ≠ 0)
    (address : (Fin n → U) → Fin B × Fin t) (v : Fin B × Fin t → U) (x : Fin n → U) :
    (∑ b, prescription 0 marker (blockIndicator marker address b) (fun i => v (b, i)) x) =
      v (address x) := by
  simp [prescription_blockIndicator marker hm, eq_comm]

/-- For each block, all prescriptions obtained by assigning a value to each of its cells.
These form a reusable set of circuit outputs. -/
def blockDictionaries [Zero U] (marker : U) (address : (Fin n → U) → Fin B × Fin t) :
    Set ((Fin n → U) → U) :=
  ⋃ b, Set.range (prescription 0 marker (blockIndicator marker address b))

/-- Given zero and the cell indicators, build all block dictionaries using at most
`B * (q + q^2 + ... + q^t)` additional gates, where `q = Fintype.card U`.
This cost is independent of the tables that will be read. -/
theorem synthesis_blockDictionaries [Zero U] [Fintype U] (hk : 2 ≤ k) (marker : U)
    (address : (Fin n → U) → Fin B × Fin t) (hzero : (fun _ => 0) ∈ s)
    (hindicators : ∀ b i, blockIndicator marker address b i ∈ s) :
    Synthesis (fullInterpretation (k := k)) s (blockDictionaries marker address)
      (B * ∑ j ∈ Finset.range t, Fintype.card U ^ (j + 1)) := by
  simpa [blockDictionaries] using Synthesis.iUnion
    (fun b => Set.range (prescription 0 marker (blockIndicator marker address b))) _
    (fun b => synthesis_prescriptions hk 0 marker _ hzero (hindicators b))

/-- Choose one dictionary output per block and keep the first nonzero value to compute
`table ∘ address`. Choosing the outputs is wiring; only combining them costs gates. -/
theorem synthesis_lookup [Zero U] (hk : 2 ≤ k)
    (marker : U) (hm : marker ≠ 0) (address : (Fin n → U) → Fin B × Fin t)
    (hs : blockDictionaries marker address ⊆ s) (table : Fin B × Fin t → U) :
    Synthesis (fullInterpretation (k := k)) s {table ∘ address}
      ((B - 1) ⌈/⌉ (k - 1)) := by
  let f := fun b => prescription 0 marker (blockIndicator marker address b) (fun i => table (b, i))
  have h := Synthesis.full_select hk (List.ofFn f) (table ∘ address)
    (by simpa using fun b => hs (Set.mem_iUnion_of_mem b ⟨fun i => table (b, i), rfl⟩))
    (by simp [f, prescription_blockIndicator marker hm]; tauto)
    (fun x => ⟨_, List.mem_ofFn.mpr ⟨(address x).1, rfl⟩,
      by simp [f, prescription_blockIndicator marker hm]⟩)
  simpa using h

omit [DecidableEq U] in
/-- Compute a finite family of lookups `tables j ∘ address`, reusing the same block dictionaries.
The first budget term builds the dictionaries once; each table then pays only for selection. -/
theorem synthesis_lookups [Zero U] [Fintype U]
    {ι : Type*} [Fintype ι] (hk : 2 ≤ k) (marker : U) (hm : marker ≠ 0)
    (address : (Fin n → U) → Fin B × Fin t) (hzero : (fun _ => 0) ∈ s)
    (hindicators : ∀ b i, blockIndicator marker address b i ∈ s)
    (tables : ι → Fin B × Fin t → U) :
    Synthesis (fullInterpretation (k := k)) s (Set.range fun j => tables j ∘ address)
      (B * (∑ j ∈ Finset.range t, Fintype.card U ^ (j + 1)) +
        Fintype.card ι * ((B - 1) ⌈/⌉ (k - 1))) := by
  classical
  have hdictionaries := synthesis_blockDictionaries hk marker address hzero hindicators
  simpa using hdictionaries.trans
    (Synthesis.family (fun j => tables j ∘ address) _
      (fun j => synthesis_lookup hk marker hm address Set.subset_union_right (tables j)))

/-- Each used cell reuses a decoded tuple indicator; unused cells reuse the zero wire.
The injective placement may leave cells unused, so the last block can be padded. -/
theorem blockIndicator_mem [Zero U] (marker : U) (coords : Fin d → (Fin n → U) → U)
    (index : (Fin d → U) ↪ Fin B × Fin t) (hzero : (fun _ => 0) ∈ s)
    (hindicators : Set.range (indicator 0 marker coords) ⊆ s) (b : Fin B) (i : Fin t) :
    blockIndicator marker (fun x => index (fun j => coords j x)) b i ∈ s := by
  classical
  by_cases h : ∃ a, index a = (b, i)
  · obtain ⟨a, ha⟩ := h
    convert hindicators ⟨a, rfl⟩ using 1
    ext x
    simp [blockIndicator, indicator, ← ha, index.injective.eq_iff]
  · convert hzero using 1
    ext x
    simp [blockIndicator, not_exists.mp h]

/-- Decode the available coordinates, then build dictionaries for their assigned blocks.
The budget adds the shared decoder and dictionary costs. Zero, the marker constant,
and the coordinates must already be available. -/
theorem synthesis_coordinateDictionaries [Zero U] [Fintype U] (hk : 2 ≤ k)
    (marker : U) (coords : Fin d → (Fin n → U) → U)
    (index : (Fin d → U) ↪ Fin B × Fin t)
    (hzero : (fun _ => 0) ∈ s) (hmarker : (fun _ => marker) ∈ s)
    (hcoords : ∀ i, coords i ∈ s) :
    Synthesis (fullInterpretation (k := k)) s
      (blockDictionaries marker (fun x => index (fun j => coords j x)))
      ((∑ j ∈ Finset.range d, Fintype.card U ^ (j + 1)) +
        B * ∑ j ∈ Finset.range t, Fintype.card U ^ (j + 1)) :=
  (synthesis_indicators hk 0 marker coords hmarker hcoords).trans
    (synthesis_blockDictionaries hk marker _ (Set.mem_union_left _ hzero)
      (blockIndicator_mem marker coords index (Set.mem_union_left _ hzero) Set.subset_union_right))

/-- Compute the table chosen by `sectionIndex`, using shared dictionaries and available
section indicators. Read each table, mask its value to zero outside its section, then select
the surviving value. Each section pays for its lookup and one masking gate; the final
budget term combines the masked values. -/
theorem synthesis_sections {α : Type*} [Zero U] [Fintype α] [DecidableEq α]
    (hk : 2 ≤ k) (marker : U) (hm : marker ≠ 0) (sectionIndex : (Fin n → U) → α)
    (address : (Fin n → U) → Fin B × Fin t)
    (hsections : ∀ a, (fun x => if sectionIndex x = a then marker else 0) ∈ s)
    (hdictionaries : blockDictionaries marker address ⊆ s) (tables : α → Fin B × Fin t → U) :
    Synthesis (fullInterpretation (k := k)) s {fun x => tables (sectionIndex x) (address x)}
      (Fintype.card α * (((B - 1) ⌈/⌉ (k - 1)) + 1) +
        ((Fintype.card α - 1) ⌈/⌉ (k - 1))) := by
  let part := fun a x => if sectionIndex x = a then tables a (address x) else 0
  have hpart (a : α) : Synthesis (fullInterpretation (k := k)) s {part a}
      (((B - 1) ⌈/⌉ (k - 1)) + 1) := by
    have hlookup := synthesis_lookup hk marker hm address hdictionaries (tables a)
    have hmask := Synthesis.full_gate (s := s ∪ {tables a ∘ address}) hk
      (fun w : Fin 2 → U => if w 0 = marker then w 1 else 0)
      (Fin.cons (fun x => if sectionIndex x = a then marker else 0)
        (fun _ => tables a ∘ address)) (by simp [Fin.forall_fin_succ, hsections])
    simpa [part, hm.symm] using hlookup.trans hmask
  have hselect := Synthesis.full_select (s := s ∪ Set.range part) hk
    (Finset.univ.toList.map part) (fun x => tables (sectionIndex x) (address x))
    (by simp) (by
      intro x f hf
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hf
      by_cases h : sectionIndex x = a <;> simp [part, h])
    (fun x => ⟨part (sectionIndex x), by simp, by simp [part]⟩)
  simpa using (Synthesis.family part _ hpart).trans hselect

end Cslib.Circuits.Full
