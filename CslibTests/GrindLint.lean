import Cslib

set_option linter.hashCommand false

open Lean Elab.Command

elab "open_scoped_all" pre:ident : command => do
  let env ← getEnv
  let nss := env.getNamespaceSet.toList.filter (fun name => name.getRoot = pre.getId)
  for ns in nss do
    let cmd ← `(open scoped $(mkIdent ns))
    elabCommand cmd

open_scoped_all Cslib

/-
  This check verifies that `grind` annotations in Cslib do not trigger run-away instantiations.
  (This documentation and test is adapted from Mathlib.)

  Exceptions may be specified here using `#grind_lint skip`. This should be kept minimal, and some
  of these were added upon the inital commit of this test. PRs removing exceptions are welcome.

  If this test fails, please modify newly introduced `grind` annotations to use the
  `grind_pattern ... where ...` syntax to add side conditions that will prevent the run-away.

  See https://lean-lang.org/doc/reference/latest/The--grind--tactic/E___matching/ for details.
-/

#grind_lint skip Cslib.Bisimilarity.trans
#grind_lint skip Cslib.FLTS.toLTS_tr
#grind_lint skip Cslib.FinFun.coe_fromFun_id
#grind_lint skip Cslib.FinFun.fromFun_comm
#grind_lint skip Cslib.FinFun.fromFun_eq
#grind_lint skip Cslib.FinFun.fromFun_idem
#grind_lint skip Cslib.FinFun.fromFun_inter
#grind_lint skip Cslib.LTS.deterministic_not_lto
#grind_lint skip Cslib.LTS.deterministic_tr_image_singleton
#grind_lint skip Cslib.LTS.IsExecution.refl
#grind_lint skip Cslib.LTS.mem_saturate_image_τ
#grind_lint skip Cslib.ωSequence.drop_const
#grind_lint skip Cslib.ωSequence.get_cons_append_zero
#grind_lint skip Cslib.ωSequence.map_id
#grind_lint skip Cslib.Automata.DA.buchi_eq_finAcc_omegaLim
#grind_lint skip Cslib.LTS.MTr.stepL
#grind_lint skip Cslib.LTS.STr.trans_τ
#grind_lint skip Cslib.Automata.DA.FinAcc.toNAFinAcc_language_eq
#grind_lint skip Cslib.Automata.NA.Buchi.reindex_language_eq
#grind_lint skip Cslib.Automata.NA.FinAcc.toDAFinAcc_language_eq
#grind_lint skip Cslib.Automata.εNA.FinAcc.toNAFinAcc_language_eq
#grind_lint skip Cslib.CLL.Proof.parr_inversion.eq_1
#grind_lint skip Cslib.CLL.Proof.with_inversion₁.eq_1
#grind_lint skip Cslib.CLL.Proof.with_inversion₂.eq_1
#grind_lint skip Cslib.CLL.Proposition.Equiv.trans
#grind_lint skip Cslib.CLL.Proposition.bang_top_eqv_one.eq_1
#grind_lint skip Cslib.CLL.Proposition.expand.eq_10
#grind_lint skip Cslib.CLL.Proposition.parr_top_eqv_top.eq_1
#grind_lint skip Cslib.CLL.Proposition.tensor_assoc.eq_1
#grind_lint skip Cslib.CLL.Proposition.tensor_distrib_oplus.eq_1
#grind_lint skip Cslib.CLL.Proposition.tensor_symm.eq_1
#grind_lint skip Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub.arrow
#grind_lint skip Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub.sum
#grind_lint skip Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub.trans_tvar
#grind_lint skip Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.body_case
#grind_lint skip Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.body_let
#grind_lint skip Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.open_tm_body
#grind_lint skip Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.app
#grind_lint skip Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.inl
#grind_lint skip Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.inr
#grind_lint skip Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.sub
#grind_lint skip Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.tapp
#grind_lint skip Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.para_subst
#grind_lint skip Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.redex_app_l_cong
#grind_lint skip Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta.redex_app_r_cong
#grind_lint skip Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.subst_intro
#grind_lint skip Cslib.LambdaCalculus.LocallyNameless.Fsub.Env.Wf.sub
#grind_lint skip Cslib.LambdaCalculus.LocallyNameless.Fsub.Env.Wf.ty
#grind_lint skip Cslib.Logic.HML.bisimulation_satisfies
#grind_lint skip Cslib.Logic.HML.Satisfies.diamond

#guard_msgs in
#grind_lint check (min := 20) in Cslib
