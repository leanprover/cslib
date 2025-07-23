/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.ConcurrencyTheory.CCS.Semantics

open CCS Process

@[lts ltsNat "ₙ"]
def TrNat := @CCS.Tr ℕ ℕ (fun _ _ => False)

def p : Process ℕ ℕ := (pre Act.τ (pre (Act.name 1) nil))

example : p [Act.τ]⭢ₙ (pre (Act.name 1) nil) := by constructor

example : p [[Act.τ, Act.name 1]]↠ₙ nil :=
  calc
    (p [Act.τ]⭢ₙ (pre (Act.name 1) nil)) := by constructor
    _ [Act.name 1]⭢ₙ nil := by constructor
