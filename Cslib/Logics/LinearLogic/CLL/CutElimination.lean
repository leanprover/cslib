/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Logics.LinearLogic.CLL.Basic

/-! -/

@[expose] public section

namespace Cslib.Logic.CLL

open Cslib.Logic.InferenceSystem

/-- A `CutFreeProof` is a `Proof` without cuts (applications of `Proof.cut`). -/
abbrev CutFreeProof (Γ : Sequent Atom) := { q : ⇓Γ // q.cutFree }

-- TODO
/- Cut admissibility: given two proofs with dual propositions, returns a cut-free proof of their
cut. -/
-- def Proof.cutAdm
--     {a : Proposition Atom} (p : CutFreeProof (a ::ₘ Γ)) (q : CutFreeProof (a⫠ ::ₘ Δ)) :
--     CutFreeProof (Γ + Δ)

-- TODO
/- Cut elimination: given a proof of a sequent `Γ`, returns a cut-free proof of the same sequent.
-/
-- def Proof.cut_elim (p : ⇓Γ) : CutFreeProof Γ

end Cslib.Logic.CLL
