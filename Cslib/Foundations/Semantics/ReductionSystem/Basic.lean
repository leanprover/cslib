/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Thomas Waring
-/

module

public import Cslib.Init
public import Cslib.Foundations.Data.Relation
public import Mathlib.Util.Notation3

@[expose] public section

/-!
# Reduction System

A reduction system is an operational semantics expressed as a relation between terms.
-/

namespace Cslib

universe u

/--
A reduction system is a relation between `Term`s.
-/
structure ReductionSystem (Term : Type u) where
  /-- The reduction relation. -/
  Red : Term → Term → Prop

namespace ReductionSystem

variable {Term : Type u} (rs : ReductionSystem Term)

section MultiStep

/-! ## Multi-step reductions -/

/-- Multi-step reduction relation. -/
abbrev MRed := Relation.ReflTransGen rs.Red

/-- All multi-step reduction relations are reflexive. -/
@[refl]
theorem MRed.refl (t : Term) : rs.MRed t t :=
  Relation.ReflTransGen.refl

/-- Any reduction is a multi-step -/
theorem MRed.single {a b : Term} (h : rs.Red a b) : rs.MRed a b :=
  Relation.ReflTransGen.single h

theorem MRed.step {a b c : Term} (hab : rs.MRed a b) (hbc : rs.Red b c) :
    rs.MRed a c :=
  Relation.ReflTransGen.tail hab hbc

theorem MRed.trans {a b c : Term} (hab : rs.MRed a b) (hbc : rs.MRed b c) :
    rs.MRed a c :=
  Relation.ReflTransGen.trans hab hbc

theorem MRed.cases_iff {a b : Term} :
    rs.MRed a b ↔ b = a ∨ ∃ c : Term, rs.MRed a c ∧ rs.Red c b :=
  Relation.ReflTransGen.cases_tail_iff rs.Red a b

@[induction_eliminator]
theorem MRed.induction_on {motive : ∀ {x y}, rs.MRed x y → Prop}
    (refl : ∀ t : Term, motive (MRed.refl rs t))
    (step : ∀ (a b c : Term) (hab : rs.MRed a b) (hbc : rs.Red b c), motive hab →
      motive (MRed.step rs hab hbc))
    {a b : Term} (h : rs.MRed a b) : motive h := by
  apply Relation.ReflTransGen.rec <;> grind

end MultiStep


section Reverse

/-- Reverse reduction relation -/
def RRed : Term → Term → Prop := Function.swap rs.Red

theorem RRed.single {a b : Term} (h : rs.Red a b) : rs.RRed b a := h

end Reverse

section Equivalence

/-- Equivalence closure relation -/
def Eqv : Term → Term → Prop := Relation.EqvGen rs.Red

theorem Eqv.refl (t : Term) : rs.Eqv t t :=
  Relation.EqvGen.refl t

theorem Eqv.single {a b : Term} (h : rs.Red a b) : rs.Eqv a b :=
  Relation.EqvGen.rel a b h

theorem Eqv.symm {a b : Term} (h : rs.Eqv a b) : rs.Eqv b a :=
  Relation.EqvGen.symm a b h

theorem Eqv.trans {a b c : Term} (h₁ : rs.Eqv a b) (h₂ : rs.Eqv b c) :
    rs.Eqv a c :=
  Relation.EqvGen.trans a b c h₁ h₂

theorem Eqv.ofMRed {a b : Term} (h : rs.MRed a b) : rs.Eqv a b :=
  Relation.ReflTransGen.to_eqvGen h

@[induction_eliminator]
theorem Eqv.induction_on {motive : ∀ {x y}, rs.Eqv x y → Prop}
    (rel : ∀ (a b : Term) (hab : rs.Red a b), motive (Eqv.single rs hab))
    (refl : ∀ t : Term, motive (Eqv.refl rs t))
    (symm : ∀ (a b : Term) (hab : rs.Eqv a b), motive hab → motive (Eqv.symm rs hab))
    (trans : ∀ (a b c : Term) (hab : rs.Eqv a b) (hbc : rs.Eqv b c), motive hab → motive hbc →
      motive (Eqv.trans rs hab hbc))
    {a b : Term} (h : rs.Eqv a b) : motive h := by
  apply Relation.EqvGen.rec <;> grind

end Equivalence

section Join

/-- Join relation -/
def Join : Term → Term → Prop := Relation.Join rs.Red

theorem Join_def {a b : Term} :
    rs.Join a b ↔ ∃ c : Term, rs.Red a c ∧ rs.Red b c := by rfl

theorem Join.symm : Symmetric rs.Join := Relation.symmetric_join

end Join

section MJoin

/-- Multi-step join relation -/
def MJoin : Term → Term → Prop := Relation.Join rs.MRed

theorem MJoin_def {a b : Term} :
    rs.MJoin a b ↔ ∃ c : Term, rs.MRed a c ∧ rs.MRed b c := by rfl

theorem MJoin.refl (t : Term) : rs.MJoin t t := by
  use t

theorem MJoin.symm : Symmetric rs.MJoin := Relation.symmetric_join

end MJoin

section Diamond

/-- A reduction system has the diamond property when all one-step reduction pairs with a common
origin are joinable -/
def Diamond : Prop := Relation.Diamond rs.Red

theorem isDiamond_def : rs.Diamond ↔
    ∀ {a b c : Term}, rs.Red a b → rs.Red a c → rs.Join b c :=
  Iff.rfl

end Diamond

section Confluence

/-- A reduction system is confluent when all multi-step reduction pairs with a common origin are
multi-step joinable -/
def Confluent : Prop := Relation.Confluent rs.Red

theorem Confluent_def : rs.Confluent ↔
    ∀ {a b c : Term}, rs.MRed a b → rs.MRed a c → rs.MJoin b c :=
  Iff.rfl

theorem isConfluent_of_unique_end (t : Term) (h : ∀ a : Term, rs.MRed a t) : rs.Confluent := by
  intro a b c hab hac
  exact ⟨t, h b, h c⟩

end Confluence

section ChurchRosser

/-- A reduction system is Church-Rosser when all equivalent terms are multi-step joinable -/
def ChurchRosser : Prop := Relation.ChurchRosser rs.Red

theorem ChurchRosser_def :
    rs.ChurchRosser ↔ ∀ {a b : Term}, rs.Eqv a b → rs.MJoin a b :=
  Iff.rfl

theorem isConfluent_iff_isChurchRosser : rs.Confluent ↔ rs.ChurchRosser :=
  Relation.Confluent_iff_ChurchRosser

end ChurchRosser

section Reducibility

/-- A term is reducible when there exists a one-step reduction from it. -/
def Reducible (t : Term) : Prop := Relation.Reducible rs.Red t

theorem Reducible_def (t : Term) :
    rs.Reducible t ↔ ∃ t' : Term, rs.Red t t' := by
  rfl

end Reducibility

section Normalization

/-- A term is in normal form when it is not reducible. -/
def Normal (t : Term) : Prop := ¬ rs.Reducible t

theorem Normal_iff (t : Term) :
    rs.Normal t ↔ ∀ t' : Term, ¬ rs.Red t t' := by
  unfold Normal Reducible
  rw [not_exists]

theorem eq_of_MRed_of_Normal {a b : Term} (ha : rs.Normal a) (hab : rs.MRed a b) :
    a = b := by
  induction hab with
  | refl => rfl
  | step a b c hab hbc hab' =>
    rw [← hab' ha] at hbc
    exact ((rs.Normal_iff a).mp ha c hbc).elim

/-- A reduction system is normalizing when every term reduces to at least one normal form. -/
def Normalizing : Prop := ∀ t : Term, ∃ n : Term, rs.MRed t n ∧ rs.Normal n

end Normalization

section Termination

/-- A reduction system is terminating when there are no infinite sequences of one-step reductions.
-/
def Terminating : Prop := Relation.Terminating rs.Red

theorem Terminating_def :
    rs.Terminating ↔ ¬ ∃ f : ℕ → Term, ∀ n : ℕ, rs.Red (f n) (f (n + 1)) := by
  unfold Terminating Relation.Terminating
  rw [wellFounded_iff_isEmpty_descending_chain, not_exists, isEmpty_subtype]

theorem isTerminating_iff_WellFounded : rs.Terminating ↔ WellFounded rs.RRed := by
  rfl

theorem isTerminating_of_WellFounded {r : Term → Term → Prop} (hr : WellFounded r)
    (h : ∀ a b : Term, rs.Red a b → r b a) : rs.Terminating := by
  rw [wellFounded_iff_isEmpty_descending_chain] at hr
  rw [Terminating_def]
  intro ⟨f, hf⟩
  exact hr.elim ⟨f, fun n ↦ h (f n) (f (n + 1)) (hf n)⟩

theorem isTerminating_of_WellFoundedLT [LT Term] [hw : WellFoundedLT Term]
    (h : ∀ a b : Term, rs.Red a b → b < a) : rs.Terminating :=
  rs.isTerminating_of_WellFounded hw.wf h

variable {rs : ReductionSystem Term}

theorem Terminating.isNormalizing (h : rs.Terminating) : rs.Normalizing := by
  rw [isTerminating_iff_WellFounded] at h
  intro t
  apply WellFounded.induction h t
  intro a ih
  by_cases ha : rs.Reducible a
  · obtain ⟨b, hab⟩ := ha
    obtain ⟨n, hbn, hn⟩ := ih b hab
    exact ⟨n, MRed.trans rs (MRed.single rs hab) hbn, hn⟩
  · unfold Normal
    use a

theorem Terminating.isConfluent_iff_all_unique_Normal (ht : rs.Terminating) :
    rs.Confluent ↔ ∀ a : Term, ∃! n : Term, rs.MRed a n ∧ rs.Normal n := by
  have hn : rs.Normalizing := ht.isNormalizing
  constructor
  · intro hc a
    apply existsUnique_of_exists_of_unique (hn a)
    rintro n₁ n₂ ⟨hr₁, hn₁⟩ ⟨hr₂, hn₂⟩
    rw [Confluent_def] at hc
    have hj : rs.MJoin n₁ n₂ := hc hr₁ hr₂
    obtain ⟨m, h₁, h₂⟩ := rs.MJoin_def.mp hj
    rw [eq_of_MRed_of_Normal rs hn₁ h₁, eq_of_MRed_of_Normal rs hn₂ h₂]
  · intro h
    rw [Confluent_def]
    intro a b c hab hac
    obtain ⟨na, ⟨han, hnnor⟩, H⟩ := h a
    use na
    obtain ⟨nb, hbnb, hnb⟩ := hn b
    obtain ⟨nc, hcnc, hnc⟩ := hn c
    have hanb : rs.MRed a nb := MRed.trans rs hab hbnb
    have hanc : rs.MRed a nc := MRed.trans rs hac hcnc
    have hnanb : nb = na := H nb ⟨hanb, hnb⟩
    have hnanc : nc = na := H nc ⟨hanc, hnc⟩
    rw [hnanb] at hbnb
    rw [hnanc] at hcnc
    exact ⟨hbnb, hcnc⟩

end Termination

section Convergence

/-- A reduction system is convergent when it is both confluent and terminating. -/
structure Convergent : Prop where
  isConfluent : rs.Confluent
  isTerminating : rs.Terminating

theorem Convergent_iff :
    rs.Convergent ↔ rs.Confluent ∧ rs.Terminating :=
  ⟨fun ⟨hc, ht⟩ ↦ ⟨hc, ht⟩, fun ⟨hc, ht⟩ ↦ ⟨hc, ht⟩⟩

variable {rs : ReductionSystem Term}

theorem Convergent.isNormalizing (h : rs.Convergent) : rs.Normalizing :=
  h.isTerminating.isNormalizing

theorem Convergent.unique_Normal (h : rs.Convergent) (a : Term) :
    ∃! n : Term, rs.MRed a n ∧ rs.Normal n :=
  h.isTerminating.isConfluent_iff_all_unique_Normal.mp h.isConfluent a

end Convergence

end ReductionSystem

open Lean Elab Meta Command Term

-- thank you to Kyle Miller for this:
-- https://leanprover.zulipchat.com/#narrow/channel/239415-metaprogramming-.2F-tactics/topic/Working.20with.20variables.20in.20a.20command/near/529324084

/-- A command to create a `ReductionSystem` from a relation, robust to use of `variable `-/
elab "create_reduction_sys" rel:ident name:ident : command => do
  liftTermElabM do
    let rel ← realizeGlobalConstNoOverloadWithInfo rel
    let ci ← getConstInfo rel
    forallTelescope ci.type fun args ty => do
      let throwNotRelation := throwError m!"type{indentExpr ci.type}\nis not a relation"
      unless args.size ≥ 2 do
        throwNotRelation
      unless ← isDefEq (← inferType args[args.size - 2]!) (← inferType args[args.size - 1]!) do
        throwNotRelation
      unless (← whnf ty).isProp do
        throwError m!"expecting Prop, not{indentExpr ty}"
      let params := ci.levelParams.map .param
      let rel := mkAppN (.const rel params) args[0:args.size-2]
      let bundle ← mkAppM ``ReductionSystem.mk #[rel]
      let value ← mkLambdaFVars args[0:args.size-2] bundle
      let type ← inferType value
      addAndCompile <| .defnDecl {
        name := name.getId
        levelParams := ci.levelParams
        type
        value
        safety := .safe
        hints := Lean.ReducibilityHints.abbrev
      }
      addTermInfo' name (.const name.getId params) (isBinder := true)
      addDeclarationRangesFromSyntax name.getId name

/--
  This command adds notations for a `ReductionSystem.Red` and `ReductionSystem.MRed`. This should
  not usually be called directly, but from the `reduction_sys` attribute.

  As an example `reduction_notation foo "β"` will add the notations "⭢β" and "↠β".

  Note that the string used will afterwards be registered as a notation. This means that if you have
  also used this as a constructor name, you will need quotes to access corresponding cases, e.g. «β»
  in the above example.
-/
syntax attrKind "reduction_notation" ident (str)? : command
macro_rules
  | `($kind:attrKind reduction_notation $rs $sym) =>
    `(
      @[nolint docBlame]
      $kind:attrKind notation3 t:39 " ⭢" $sym:str t':39 => (ReductionSystem.Red  $rs) t t'
      @[nolint docBlame]
      $kind:attrKind notation3 t:39 " ↠" $sym:str t':39 => (ReductionSystem.MRed $rs) t t'
     )
  | `($kind:attrKind reduction_notation $rs) =>
    `(
      @[nolint docBlame]
      $kind:attrKind notation3 t:39 " ⭢ " t':39 => (ReductionSystem.Red  $rs) t t'
      @[nolint docBlame]
      $kind:attrKind notation3 t:39 " ↠ " t':39 => (ReductionSystem.MRed $rs) t t'
     )


/--
  This attribute calls the `reduction_notation` command for the annotated declaration, such as in:

  ```
  @[reduction_sys rs "ₙ", simp]
  def PredReduction (a b : ℕ) : Prop := a = b + 1
  ```
-/
syntax (name := reduction_sys) "reduction_sys" ident (ppSpace str)? : attr

initialize Lean.registerBuiltinAttribute {
  name := `reduction_sys
  descr := "Register notation for a relation and its closures."
  add := fun decl stx _ => MetaM.run' do
    match stx with
    | `(attr | reduction_sys $rs $sym) =>
        let mut sym := sym
        unless sym.getString.endsWith " " do
          sym := Syntax.mkStrLit (sym.getString ++ " ")
        let rs := rs.getId.updatePrefix decl.getPrefix |> Lean.mkIdent
        liftCommandElabM <| Command.elabCommand (← `(create_reduction_sys $(mkIdent decl) $rs))
        liftCommandElabM <| (do
          modifyScope ({ · with currNamespace := decl.getPrefix })
          Command.elabCommand (← `(scoped reduction_notation $rs $sym)))
    | `(attr | reduction_sys $rs) =>
        let rs := rs.getId.updatePrefix decl.getPrefix |> Lean.mkIdent
        liftCommandElabM <| Command.elabCommand (← `(create_reduction_sys $(mkIdent decl) $rs))
        liftCommandElabM <| (do
          modifyScope ({ · with currNamespace := decl.getPrefix })
          Command.elabCommand (← `(scoped reduction_notation $rs)))
    | _ => throwError "invalid syntax for 'reduction_sys' attribute"
}

end Cslib
