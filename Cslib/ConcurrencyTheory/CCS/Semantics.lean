/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Semantics.LTS.Basic
import Cslib.ConcurrencyTheory.CCS.Basic

/-! # Semantics of CCS

## Main definitions
- `CCS.Tr`: transition relation for CCS.
- `CCS.lts`: the `LTS` of CCS.

-/

variable
  {Name : Type u}
  {Constant : Type v}
  {defs : Constant → (CCS.Process Name Constant) → Prop}

namespace CCS

open Process

/-- The transition relation for CCS. This is a direct formalisation of the one found in
[Sangiorgi2011]. -/
@[lts CCS.lts]
inductive Tr : Process Name Constant → Act Name → Process Name Constant → Prop where
  | pre : Tr (pre μ p) μ p
  | parL : Tr p μ p' → Tr (par p q) μ (par p' q)
  | parR : Tr q μ q' → Tr (par p q) μ (par p q')
  | com : Tr p μ p' → Tr q μ.co q' → Tr (par p q) Act.τ (par p' q')
  | choiceL : Tr p μ p' → Tr (choice p q) μ p'
  | choiceR : Tr q μ q' → Tr (choice p q) μ q'
  | res : μ ≠ Act.name a → μ ≠ Act.coname a → Tr p μ p' → Tr (res a p) μ (res a p')
  | const : defs k p → Tr p μ p' → Tr (const k) μ p'

instance : HasTau (Act Name) where
  τ := Act.τ

/-- A process is (successfully) terminated if it is a composition of `nil`s. -/
inductive Terminated : Process Name Constant → Prop where
  | nil : Terminated Process.nil
  | par : Terminated p → Terminated q → Terminated (par p q)
  | choice : Terminated p → Terminated q → Terminated (choice p q)
  | res : Terminated p → Terminated (res a p)

end CCS
