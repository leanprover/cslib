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

-- WIP below, trying to get Trans to work for LTS

instance (lts : LTS State Label) : Trans (fun s1 => lts.Tr s1 μ1) (fun s2 => lts.Tr s2 μ2) (fun s3 => lts.MTr s3 [μ1, μ2]) where
  trans := by
    intro s1 s2 s3 htr1 htr2
    apply LTS.MTr.single at htr1
    apply LTS.MTr.single at htr2
    apply LTS.MTr.comp lts htr1 htr2

-- Problematic:
-- example : p [[Act.τ, Act.name 1]]↠ₙ nil := by
--   calc
--     (p [Act.τ]⭢ₙ (pre (Act.name 1) nil)) := by constructor
--     _ [Act.name 1]⭢ₙ nil := by constructor
