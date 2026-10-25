/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.AtomStructure
public import Mathlib.Data.Finset.Fold
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Integral atom structures

This module abstractly defines the atoms of an integral relation algebra, along with a
characterization of its identity and non-identity cyles that form an atom structure when
shown to be associative.

To concretely construct such an algebra, see the `integral_cycles%` elaborator
in `Cslib.Foundations.RelationAlgebra.IntegralCycles`.

-/

@[expose] public section

namespace Cslib.RelationAlgebra

/--
The atoms of an integral atom structure: the identity atom, `s` symmetric diversity (non-identity)
atoms, and `n` pairs of nonsymmetric atoms.
-/
inductive IntegralAtom (s n : ℕ) where
  /-- The identity atom. -/
  | one
  /-- A symmetric diversity atom. -/
  | symm (i : Fin s)
  /-- A nonsymmetric atom. `nsymm i true` is the converse of `nsymm i false`. -/
  | nsymm (i : Fin n) (conv : Bool)
  deriving DecidableEq, Fintype

namespace IntegralAtom

variable {s n : ℕ}

/-- The converse of an atom, where just nonsymmetric atoms are flipped. -/
def conv : IntegralAtom s n → IntegralAtom s n
  | one => one
  | symm i => symm i
  | nsymm i b => nsymm i (!b)

/-- An integral cycle is a triple of integral atoms. -/
abbrev Cycle (s n : ℕ) := IntegralAtom s n × IntegralAtom s n × IntegralAtom s n

/-- The Peircean orbit of a cycle under the converse and cycle rules. -/
def cycleOrbit : Cycle s n → Finset (Cycle s n)
  | (r, u, t) =>
    {(r, u, t), (conv u, conv r, conv t), (conv r, t, u),
      (conv t, r, conv u), (u, conv t, conv r), (t, conv u, r)}

/-- The union of the Peircean orbits of the generators and all identity cycles. -/
def cycleClosure (generators : Finset (Cycle s n)) : Finset (Cycle s n) :=
  (generators ∪ Finset.univ.image (fun a => (one, a, a))).biUnion cycleOrbit

@[simp, grind =]
theorem conv_one : conv (one : IntegralAtom s n) = one := rfl

@[simp, grind =]
theorem conv_conv (a : IntegralAtom s n) : conv (conv a) = a := by
  cases a <;> simp [conv]

theorem cycleOrbit_conv_cycles {c : Cycle s n} {r u t : IntegralAtom s n}
    (h : (r, u, t) ∈ cycleOrbit c) : (conv u, conv r, conv t) ∈ cycleOrbit c := by
  simp only [cycleOrbit, Finset.mem_insert] at *
  grind

theorem cycleOrbit_cycle_left {c : Cycle s n} {r u t : IntegralAtom s n}
    (h : (r, u, t) ∈ cycleOrbit c) : (conv r, t, u) ∈ cycleOrbit c := by
  simp only [cycleOrbit, Finset.mem_insert] at *
  grind

theorem cycleClosure_id_exist (g : Finset (Cycle s n)) (r : IntegralAtom s n) :
    (r, one, r) ∈ cycleClosure g := by
  apply Finset.mem_biUnion.mpr
  use (one, conv r, conv r)
  simp [cycleOrbit]

theorem cycleClosure_conv_cycles (g : Finset (Cycle s n)) {r u t : IntegralAtom s n}
    (h : (r, u, t) ∈ cycleClosure g) :
    (conv u, conv r, conv t) ∈ cycleClosure g := by
  obtain ⟨c, hc, h⟩ := Finset.mem_biUnion.mp h
  exact Finset.mem_biUnion.mpr ⟨c, hc, cycleOrbit_conv_cycles h⟩

theorem cycleClosure_cycle_left (g : Finset (Cycle s n)) {r u t : IntegralAtom s n}
    (h : (r, u, t) ∈ cycleClosure g) : (conv r, t, u) ∈ cycleClosure g := by
  obtain ⟨c, hc, h⟩ := Finset.mem_biUnion.mp h
  exact Finset.mem_biUnion.mpr ⟨c, hc, cycleOrbit_cycle_left h⟩

theorem cycleClosure_id_cycle (g : Finset (Cycle s n))
    (hg : ∀ c ∈ g, let (r, u, t) := c; r ≠ one ∧ u ≠ one ∧ t ≠ one)
    {r p : IntegralAtom s n} (h : (r, one, p) ∈ cycleClosure g) : p = r := by
  obtain ⟨c, hc, h⟩ := Finset.mem_biUnion.mp h
  simp [cycleOrbit] at h
  grind [conv_conv, conv_one]

/-- Construct an `AtomStructure` from diversity cycle generators whose closure is associative. -/
def ofCycles (generators : Finset (Cycle s n))
    (hassoc : ∀ {r q p u t}, (r, q, p) ∈ cycleClosure generators →
      (u, t, q) ∈ cycleClosure generators →
      ∃ q', (q', t, p) ∈ cycleClosure generators ∧ (r, u, q') ∈ cycleClosure generators)
    (hg : ∀ c ∈ generators, let (r, u, t) := c; r ≠ one ∧ u ≠ one ∧ t ≠ one) :
    AtomStructure (IntegralAtom s n) where
  conv := conv
  id := {one}
  cycles := cycleClosure generators
  assoc := hassoc
  id_cycle := by rintro _ _ _ rfl; exact cycleClosure_id_cycle _ hg
  id_exist r := ⟨one, rfl, cycleClosure_id_exist _ r⟩
  conv_cycles := cycleClosure_conv_cycles _
  cycle_left := cycleClosure_cycle_left _

end IntegralAtom

end Cslib.RelationAlgebra
