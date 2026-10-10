/-
Copyright (c) 2026 Maximiliano Onofre Martínez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maximiliano Onofre Martínez
-/

module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaConfluence
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullEtaConfluence
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaEta
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.ParEtaC

/-! # βη-Confluence for the λ-calculus

## Reference

* [T. Nipkow, *More Church-Rosser Proofs (in Isabelle/HOL)*][Nipkow2001]

-/

@[expose] public section

set_option linter.unusedDecidableInType false

namespace Cslib

universe u

variable {Var : Type u}
variable [HasFresh Var] [DecidableEq Var]

namespace LambdaCalculus.LocallyNameless.Untyped.Term

open Relation

/-- η-reduction and β-reduction strongly commute. -/
lemma stronglyCommute_eta_beta : StronglyCommute (@FullEta Var) FullBeta := by
  intro x y₁ y₂ h₁ st_beta
  rcases interaction _ 1 _ _ (parEtaC_of_fullEta h₁) st_beta with ⟨s', m, h, g⟩|⟨m, _, h⟩
  · exact ⟨s', .single g, ParEtaC.toFullEtaStar h⟩
  · exact ⟨y₁, .refl, ParEtaC.toFullEtaStar h⟩

open Commute in
/-- βη-reduction is confluent. -/
@[wikidata Q1308502]
theorem confluent_beta_eta : Confluent (@FullBetaEta Var) := by
  apply join_confluent
  · exact confluent_fullBeta
  · exact stronglyConfluent_eta.to_confluent
  apply symm
  exact stronglyCommute_eta_beta.to_commute

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
