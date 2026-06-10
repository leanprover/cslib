/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Init
public import Cslib.Foundations.Logic.Connectives
public import Mathlib.Data.Finset.Basic

/-! # Bimodal Logic Formula

This module defines the formula type for bimodal (temporal-modal) logic with primitives
`{atom, bot, imp, box, untl, snce}`. This is the combined language that includes both
modal necessity and temporal until/since operators.

## Derived Connectives

All derived connectives from both modal and temporal logic are available:
- Propositional: `neg`, `top`, `and`, `or`
- Modal: `diamond` (◇φ := ¬□¬φ)
- Temporal: `some_future`, `all_future`, `some_past`, `all_past`
-/

@[expose] public section

namespace Cslib.Logic.Bimodal

/-- Bimodal logic formula type. Primitives: atoms, falsum, implication, box, until, since. -/
inductive Formula (Atom : Type u) : Type u where
  /-- Atomic proposition. -/
  | atom (p : Atom)
  /-- Falsum / bottom. -/
  | bot
  /-- Implication. -/
  | imp (φ₁ φ₂ : Formula Atom)
  /-- Necessity / box. -/
  | box (φ : Formula Atom)
  /-- Until temporal operator: φ₁ U φ₂. -/
  | untl (φ₁ φ₂ : Formula Atom)
  /-- Since temporal operator: φ₁ S φ₂. -/
  | snce (φ₁ φ₂ : Formula Atom)
deriving DecidableEq, BEq

/-- Negation: ¬φ := φ → ⊥ -/
abbrev Formula.neg (φ : Formula Atom) : Formula Atom := .imp φ .bot

/-- Verum / top: ⊤ := ⊥ → ⊥ -/
abbrev Formula.top : Formula Atom := .imp .bot .bot

/-- Disjunction: φ₁ ∨ φ₂ := ¬φ₁ → φ₂ -/
abbrev Formula.or (φ₁ φ₂ : Formula Atom) : Formula Atom :=
  .imp (.imp φ₁ .bot) φ₂

/-- Conjunction: φ₁ ∧ φ₂ := ¬(φ₁ → ¬φ₂) -/
abbrev Formula.and (φ₁ φ₂ : Formula Atom) : Formula Atom :=
  .imp (.imp φ₁ (.imp φ₂ .bot)) .bot

/-- Possibility / diamond: ◇φ := ¬□¬φ -/
abbrev Formula.diamond (φ : Formula Atom) : Formula Atom :=
  .neg (.box (.neg φ))

/-- Some future (eventually): F φ := ⊤ U φ -/
abbrev Formula.some_future (φ : Formula Atom) : Formula Atom :=
  .untl φ .top

/-- All future (globally): G φ := ¬F ¬φ -/
abbrev Formula.all_future (φ : Formula Atom) : Formula Atom :=
  .neg (.some_future (.neg φ))

/-- Some past: P φ := ⊤ S φ -/
abbrev Formula.some_past (φ : Formula Atom) : Formula Atom :=
  .snce φ .top

/-- All past (historically): H φ := ¬P ¬φ -/
abbrev Formula.all_past (φ : Formula Atom) : Formula Atom :=
  .neg (.some_past (.neg φ))

@[inherit_doc] scoped prefix:40 "¬" => Formula.neg
@[inherit_doc] scoped infix:36 " ∧ " => Formula.and
@[inherit_doc] scoped infix:35 " ∨ " => Formula.or
@[inherit_doc] scoped infix:30 " → " => Formula.imp
@[inherit_doc] scoped prefix:40 "□" => Formula.box
@[inherit_doc] scoped prefix:40 "◇" => Formula.diamond
@[inherit_doc] scoped infix:40 " U " => Formula.untl
@[inherit_doc] scoped infix:40 " S " => Formula.snce
@[inherit_doc] scoped prefix:40 "F" => Formula.some_future
@[inherit_doc] scoped prefix:40 "G" => Formula.all_future
@[inherit_doc] scoped prefix:40 "P" => Formula.some_past
@[inherit_doc] scoped prefix:40 "H" => Formula.all_past

/-- Temporal 'always' operator: △φ := Hφ ∧ (φ ∧ Gφ). -/
abbrev Formula.always (φ : Formula Atom) : Formula Atom :=
  .and (.all_past φ) (.and φ (.all_future φ))

/-- Temporal 'sometimes' operator: ▽φ := ¬△¬φ. -/
abbrev Formula.sometimes (φ : Formula Atom) : Formula Atom :=
  .neg (.always (.neg φ))

@[inherit_doc] scoped prefix:40 "△" => Formula.always
@[inherit_doc] scoped prefix:40 "▽" => Formula.sometimes

/-- Register `Bimodal.Formula` as an instance of `BimodalConnectives`. -/
instance : BimodalConnectives (Formula Atom) where
  bot := .bot
  imp := .imp
  box := .box
  untl := .untl
  snce := .snce

/-! ## Swap Temporal Duality -/

namespace Formula

variable {Atom : Type u}

/--
Swap temporal operators (past <-> future) in a formula.

This transformation is used in the temporal duality inference rule (TD):
if `|- phi` then `|- swap_temporal phi`.

The box operator is self-dual under temporal swap: `swap(box(phi)) = box(swap(phi))`.
-/
def swap_temporal : Formula Atom -> Formula Atom
  | .atom s => .atom s
  | .bot => .bot
  | .imp phi psi => .imp (swap_temporal phi) (swap_temporal psi)
  | .box phi => .box (swap_temporal phi)
  | .untl phi psi => .snce (swap_temporal phi) (swap_temporal psi)
  | .snce phi psi => .untl (swap_temporal phi) (swap_temporal psi)

/-- swap_temporal is an involution (applying it twice gives identity). -/
theorem swapTemporal_involution (phi : Formula Atom) :
    phi.swap_temporal.swap_temporal = phi := by
  induction phi with
  | atom _ => rfl
  | bot => rfl
  | imp _ _ ihp ihq => simp only [swap_temporal, ihp, ihq]
  | box _ ih => simp only [swap_temporal, ih]
  | untl _ _ ih1 ih2 => simp only [swap_temporal, ih1, ih2]
  | snce _ _ ih1 ih2 => simp only [swap_temporal, ih1, ih2]

/-- swap_temporal distributes over negation: swap(neg phi) = neg(swap phi). -/
theorem swapTemporal_neg (phi : Formula Atom) :
    (Formula.neg phi).swap_temporal = Formula.neg phi.swap_temporal := by
  simp only [Formula.neg, swap_temporal]

/-- swap_temporal distributes over diamond: swap(diamond phi) = diamond(swap phi). -/
theorem swapTemporal_diamond (phi : Formula Atom) :
    phi.diamond.swap_temporal = phi.swap_temporal.diamond := by
  simp only [diamond, neg, swap_temporal]

/-- swap_temporal exchanges some_future and some_past: swap(F phi) = P(swap phi). -/
@[simp]
theorem swapTemporal_someFuture (phi : Formula Atom) :
    (Formula.some_future phi).swap_temporal = Formula.some_past phi.swap_temporal := by
  simp only [Formula.some_past, Formula.top, swap_temporal]

/-- swap_temporal exchanges some_past and some_future: swap(P phi) = F(swap phi). -/
@[simp]
theorem swapTemporal_somePast (phi : Formula Atom) :
    (Formula.some_past phi).swap_temporal = Formula.some_future phi.swap_temporal := by
  simp only [Formula.some_future, Formula.top, swap_temporal]

/-- swap_temporal exchanges all_future and all_past: swap(G phi) = H(swap phi). -/
@[simp]
theorem swapTemporal_allFuture (phi : Formula Atom) :
    (Formula.all_future phi).swap_temporal = Formula.all_past phi.swap_temporal := by
  simp only [Formula.all_past, swap_temporal]

/-- swap_temporal exchanges all_past and all_future: swap(H phi) = G(swap phi). -/
@[simp]
theorem swapTemporal_allPast (phi : Formula Atom) :
    (Formula.all_past phi).swap_temporal = Formula.all_future phi.swap_temporal := by
  simp only [Formula.all_future, swap_temporal]

/-! ## Propositional Atoms -/

section Atoms

variable [DecidableEq Atom]

/-- The set of propositional atoms appearing in a formula. -/
def atoms : Formula Atom -> Finset Atom
  | .atom s => {s}
  | .bot => {}
  | .imp phi psi => atoms phi ∪ atoms psi
  | .box phi => atoms phi
  | .untl phi psi => atoms phi ∪ atoms psi
  | .snce phi psi => atoms phi ∪ atoms psi

/-- swap_temporal preserves atoms: swapping past/future does not change which atoms appear. -/
theorem atoms_swapTemporal (phi : Formula Atom) :
    atoms (swap_temporal phi) = atoms phi := by
  induction phi with
  | atom _ => rfl
  | bot => rfl
  | imp _ _ ih1 ih2 => simp only [swap_temporal, atoms]; rw [ih1, ih2]
  | box _ ih => simp only [swap_temporal, atoms]; rw [ih]
  | untl _ _ ih1 ih2 => simp only [swap_temporal, atoms]; rw [ih1, ih2]
  | snce _ _ ih1 ih2 => simp only [swap_temporal, atoms]; rw [ih1, ih2]

end Atoms

end Formula

end Cslib.Logic.Bimodal
