/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
import Mathlib.Logic.Relation

-- not sure why this doesn't compile as an "instance" but oh well
def trans_of_subrelation {α : Type _} (s s' r : α → α → Prop) (hr : Transitive r)
    (h : ∀ a b : α, s a b → r a b) (h' : ∀ a b : α, s' a b → r a b) : Trans s s' r where
  trans := by
    intro a b c hab hbc
    replace hab := h _ _ hab
    replace hbc := h' _ _ hbc
    exact hr hab hbc

def trans_of_subrelation_left {α : Type _} (s r : α → α → Prop) (hr : Transitive r)
    (h : ∀ a b : α, s a b → r a b) : Trans s r r where
  trans := by
    intro a b c hab hbc
    replace hab := h _ _ hab
    exact hr hab hbc

def trans_of_subrelation_right {α : Type _} (s r : α → α → Prop) (hr : Transitive r)
    (h : ∀ a b : α, s a b → r a b) : Trans r s r where
  trans := by
    intro a b c hab hbc
    replace hbc := h _ _ hbc
    exact hr hab hbc
