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
- Temporal: `someFuture`, `allFuture`, `somePast`, `allPast`
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
abbrev Formula.someFuture (φ : Formula Atom) : Formula Atom :=
  .untl φ .top

/-- All future (globally): G φ := ¬F ¬φ -/
abbrev Formula.allFuture (φ : Formula Atom) : Formula Atom :=
  .neg (.someFuture (.neg φ))

/-- Some past: P φ := ⊤ S φ -/
abbrev Formula.somePast (φ : Formula Atom) : Formula Atom :=
  .snce φ .top

/-- All past (historically): H φ := ¬P ¬φ -/
abbrev Formula.allPast (φ : Formula Atom) : Formula Atom :=
  .neg (.somePast (.neg φ))

@[inherit_doc] scoped prefix:40 "¬" => Formula.neg
@[inherit_doc] scoped infix:36 " ∧ " => Formula.and
@[inherit_doc] scoped infix:35 " ∨ " => Formula.or
@[inherit_doc] scoped infix:30 " → " => Formula.imp
@[inherit_doc] scoped prefix:40 "□" => Formula.box
@[inherit_doc] scoped prefix:40 "◇" => Formula.diamond
@[inherit_doc] scoped infix:40 " U " => Formula.untl
@[inherit_doc] scoped infix:40 " S " => Formula.snce
@[inherit_doc] scoped prefix:40 "F" => Formula.someFuture
@[inherit_doc] scoped prefix:40 "G" => Formula.allFuture
@[inherit_doc] scoped prefix:40 "P" => Formula.somePast
@[inherit_doc] scoped prefix:40 "H" => Formula.allPast

/-- Temporal 'always' operator: △φ := Hφ ∧ (φ ∧ Gφ). -/
abbrev Formula.always (φ : Formula Atom) : Formula Atom :=
  .and (.allPast φ) (.and φ (.allFuture φ))

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
if `|- phi` then `|- swapTemporal phi`.

The box operator is self-dual under temporal swap: `swap(box(phi)) = box(swap(phi))`.
-/
def swapTemporal : Formula Atom -> Formula Atom
  | .atom s => .atom s
  | .bot => .bot
  | .imp phi psi => .imp (swapTemporal phi) (swapTemporal psi)
  | .box phi => .box (swapTemporal phi)
  | .untl phi psi => .snce (swapTemporal phi) (swapTemporal psi)
  | .snce phi psi => .untl (swapTemporal phi) (swapTemporal psi)

/-- swapTemporal is an involution (applying it twice gives identity). -/
theorem swapTemporal_involution (phi : Formula Atom) :
    phi.swapTemporal.swapTemporal = phi := by
  induction phi with
  | atom _ => rfl
  | bot => rfl
  | imp _ _ ihp ihq => simp only [swapTemporal, ihp, ihq]
  | box _ ih => simp only [swapTemporal, ih]
  | untl _ _ ih1 ih2 => simp only [swapTemporal, ih1, ih2]
  | snce _ _ ih1 ih2 => simp only [swapTemporal, ih1, ih2]

/-- swapTemporal distributes over negation: swap(neg phi) = neg(swap phi). -/
theorem swapTemporal_neg (phi : Formula Atom) :
    (Formula.neg phi).swapTemporal = Formula.neg phi.swapTemporal := by
  simp only [Formula.neg, swapTemporal]

/-- swapTemporal distributes over diamond: swap(diamond phi) = diamond(swap phi). -/
theorem swapTemporal_diamond (phi : Formula Atom) :
    phi.diamond.swapTemporal = phi.swapTemporal.diamond := by
  simp only [diamond, neg, swapTemporal]

/-- swapTemporal exchanges someFuture and somePast: swap(F phi) = P(swap phi). -/
@[simp]
theorem swapTemporal_someFuture (phi : Formula Atom) :
    (Formula.someFuture phi).swapTemporal = Formula.somePast phi.swapTemporal := by
  simp only [Formula.somePast, Formula.top, swapTemporal]

/-- swapTemporal exchanges somePast and someFuture: swap(P phi) = F(swap phi). -/
@[simp]
theorem swapTemporal_somePast (phi : Formula Atom) :
    (Formula.somePast phi).swapTemporal = Formula.someFuture phi.swapTemporal := by
  simp only [Formula.someFuture, Formula.top, swapTemporal]

/-- swapTemporal exchanges allFuture and allPast: swap(G phi) = H(swap phi). -/
@[simp]
theorem swapTemporal_allFuture (phi : Formula Atom) :
    (Formula.allFuture phi).swapTemporal = Formula.allPast phi.swapTemporal := by
  simp only [Formula.allPast, swapTemporal]

/-- swapTemporal exchanges allPast and allFuture: swap(H phi) = G(swap phi). -/
@[simp]
theorem swapTemporal_allPast (phi : Formula Atom) :
    (Formula.allPast phi).swapTemporal = Formula.allFuture phi.swapTemporal := by
  simp only [Formula.allFuture, swapTemporal]

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

/-- swapTemporal preserves atoms: swapping past/future does not change which atoms appear. -/
theorem atoms_swapTemporal (phi : Formula Atom) :
    atoms (swapTemporal phi) = atoms phi := by
  induction phi with
  | atom _ => rfl
  | bot => rfl
  | imp _ _ ih1 ih2 => simp only [swapTemporal, atoms]; rw [ih1, ih2]
  | box _ ih => simp only [swapTemporal, atoms]; rw [ih]
  | untl _ _ ih1 ih2 => simp only [swapTemporal, atoms]; rw [ih1, ih2]
  | snce _ _ ih1 ih2 => simp only [swapTemporal, atoms]; rw [ih1, ih2]

end Atoms

end Formula

end Cslib.Logic.Bimodal
