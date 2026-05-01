/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
module

public import Cslib.Logics.Propositional.NaturalDeduction.Basic

/-! # Results on propositional theories -/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Proposition Theory InferenceSystem DerivableIn Derivation IsIntuitionistic IsClassical

variable {Atom : Type u} [DecidableEq Atom] [Bot Atom]

namespace Theory

instance instIsIntuitionisticIPL : IsIntuitionistic Atom (IPL Atom) where
  efq A := ax (efq_mem_ipl A)

instance instIsClassicalCPL : IsClassical Atom (CPL Atom) where
  dne A := ax (dne_mem_cpl A)

def LEM (Atom : Type u) [Bot Atom] : Theory Atom := {A ∨ ¬ A | A : Proposition Atom}

omit [DecidableEq Atom] in
lemma lem_mem_lem (A : Proposition Atom) : (A ∨ ¬ A) ∈ LEM Atom := ⟨A, rfl⟩

def Pierce (Atom : Type u) [Bot Atom] : Theory Atom :=
  {((A → B) → A) → A | (A : Proposition Atom) (B : Proposition Atom)}

omit [DecidableEq Atom] in
lemma pierce_mem_pierce (A B : Proposition Atom) : (((A → B) → A) → A) ∈ Pierce Atom := ⟨A, B, rfl⟩

instance instIsClassicalLEM : IsClassical Atom (LEM Atom ∪ IPL Atom : Theory Atom) where
  dne A := by
    apply implI
    apply orE (ax <| Set.mem_union_left _ <| lem_mem_lem A)
    · exact ass (Finset.mem_insert_self A _)
    · apply implE (A := ⊥) (ax <| Set.mem_union_right _ (efq_mem_ipl A))
      apply implE (A := ¬ A) <;> exact ass (by grind)

instance instIsClassicalPierce : IsClassical Atom (Pierce Atom ∪ IPL Atom : Theory Atom) where
  dne A := by
    apply implI
    apply implE (A := (A → ⊥) → A) (ax <| Set.mem_union_left _ <| pierce_mem_pierce A ⊥)
    apply implI
    apply implE (A := ⊥) (ax <| Set.mem_union_right _ (efq_mem_ipl A))
    apply implE (A := ¬ A) <;> exact ass (by grind)

end Cslib.Logic.PL.Theory
