/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.AtomStructure
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Tactic.DeriveFintype

/-!
# Integral atom structures

## References

* Peter Jipsen, [*List of small integral relation algebras*](
  https://www1.chapman.edu/~jipsen/gap/ramaddux.html).

-/

@[expose] public section

namespace Cslib.RelationAlgebra

/--
The atoms of an integral atom structure: the identity atom, `s` symmetric diversity (non-identity)
atoms, and `n` pairs of nonsymmetric atoms.
-/
inductive IntegralAtom (s n : ℕ) where
  /-- The identity atom. -/
  | one
  /-- A symmetric diversity atom. -/
  | symm (i : Fin s)
  /-- A nonsymmetric atom. `nsymm i true` is the converse of `nsymm i false`. -/
  | nsymm (i : Fin n) (conv : Bool)
  deriving DecidableEq, Fintype

namespace IntegralAtom

variable {s n : ℕ}

/-- The converse of an atom, where just nonsymmetric atoms are flipped. -/
def conv : IntegralAtom s n → IntegralAtom s n
  | one => one
  | symm i => symm i
  | nsymm i b => nsymm i (!b)

abbrev Cycle (s n : ℕ) := IntegralAtom s n × IntegralAtom s n × IntegralAtom s n

def cycleClosure (generators : Finset (Cycle s n)) : Finset (Cycle s n) :=
  Finset.univ.biUnion (fun a => {(one, a, a), (a, one, a), (a, conv a, one)}) ∪
    generators.biUnion fun (r, s, t) =>
      {(r, s, t), (conv s, conv r, conv t), (conv r, t, s),
        (conv t, r, conv s), (s, conv t, conv r), (t, conv s, r)}

public meta section

open Lean Elab Term Meta Parser Tactic

structure IntegralCyclesConfig where
  symm : Array Name := #[]
  nonsymm : Array Name := #[]

private def elabIntegralCycleNames (item : ConfigEval.ConfigItem) : TermElabM (Array Name) := do
  item.checkNotBool
  match item.value with
  | `($name:ident) => return #[name.getId.eraseMacroScopes]
  | `([$names,*]) => names.getElems.mapM fun name => do
      unless name.raw.isIdent do throwErrorAt name "expected an atom name"
      return name.raw.getId.eraseMacroScopes
  | value => ConfigEval.evalTermOrExprWithElab ⟨value⟩

private declare_term_config_elab elabIntegralCyclesConfig IntegralCyclesConfig where
  option symm := fun cfg item => return { cfg with symm := ← elabIntegralCycleNames item }
  option nonsymm := fun cfg item => return { cfg with nonsymm := ← elabIntegralCycleNames item }

syntax (name := integralCycles) "integral_cycles%" optConfig
  ("(" ident ("~")? "," ident ("~")? "," ident ("~")? ")")* : term

@[no_expose, term_elab integralCycles]
def elabIntegralCycles : TermElab := fun stx expectedType? => do
  let `(integral_cycles% $cfg:optConfig $[($r $[~%$rc]?, $s $[~%$sc]?, $t $[~%$tc]?)]*) := stx
    | throwUnsupportedSyntax
  let config ← elabIntegralCyclesConfig cfg (logExceptions := false)
  let atomTerm (ref : Ident) (isConverse : Bool) : TermElabM (TSyntax `term) := do
    let name := ref.getId.eraseMacroScopes
    if let some i := config.symm.findIdx? (· == name) then
      `(IntegralAtom.symm $(quote i))
    else if let some i := config.nonsymm.findIdx? (· == name) then
      `(IntegralAtom.nsymm $(quote i) $(quote isConverse))
    else
      throwErrorAt ref "undeclared atom '{name}'"
  let mut cycleTerms : Array (TSyntax `term) := #[]
  for r in r, rc in rc, s in s, sc in sc, t in t, tc in tc do
    cycleTerms := cycleTerms.push <|
      ← `(($(← atomTerm r rc.isSome), $(← atomTerm s sc.isSome), $(← atomTerm t tc.isSome)))
  let s := quote config.symm.size
  let n := quote config.nonsymm.size
  let generators ← `(term| ([$[$cycleTerms:term],*] : List (Cycle $s $n)).toFinset)
  let generated ← `(term|
    ({ conv := IntegralAtom.conv
       id := {IntegralAtom.one}
       cycles := ↑(cycleClosure (s := $s) (n := $n) $generators)
       assoc := by decide +kernel
       id_cycle := by decide +kernel
       id_exist := by decide +kernel
       conv_cycles := by decide +kernel
       cycle_left := by decide +kernel } : RelationAlgebra.AtomStructure (IntegralAtom $s $n)))
  withoutErrToSorry <| withSynthesize <| elabTermEnsuringType generated expectedType?

end

instance (generators : Finset (Cycle s n)) :
    DecidablePred (· ∈ (cycleClosure generators : Set (Cycle s n))) :=
  fun _ => inferInstance

def ra_1_1 : AtomStructure (IntegralAtom 0 0) := integral_cycles%

def ra_1_2 : AtomStructure (IntegralAtom 1 0) :=
  integral_cycles% (symm := a)

def ra_2_2 : AtomStructure (IntegralAtom 1 0) :=
  integral_cycles% (symm := a) (a, a, a)

def ra_1_3 : AtomStructure (IntegralAtom 0 1) :=
  integral_cycles% (nonsymm := a) (a, a, a)

def ra_2_3 : AtomStructure (IntegralAtom 0 1) :=
  integral_cycles% (nonsymm := a) (a, a, a~)

def ra_3_3 : AtomStructure (IntegralAtom 0 1) :=
  integral_cycles% (nonsymm := a) (a, a, a~) (a, a, a)

def ra_1_7 : AtomStructure (IntegralAtom 2 0) :=
  integral_cycles% (symm := [a, b]) (a, b, b)

def ra_2_7 : AtomStructure (IntegralAtom 2 0) :=
  integral_cycles% (symm := [a, b]) (a, b, b) (a, a, a)

def ra_3_7 : AtomStructure (IntegralAtom 2 0) :=
  integral_cycles% (symm := [a, b]) (a, b, b) (b, b, b)

def ra_4_7 : AtomStructure (IntegralAtom 2 0) :=
  integral_cycles% (symm := [a, b]) (a, b, b) (a, a, a) (b, b, b)

def ra_5_7 : AtomStructure (IntegralAtom 2 0) :=
  integral_cycles% (symm := [a, b]) (a, a, b) (a, b, b)

def ra_6_7 : AtomStructure (IntegralAtom 2 0) :=
  integral_cycles% (symm := [a, b]) (a, a, b) (a, b, b) (a, a, a)

def ra_7_7 : AtomStructure (IntegralAtom 2 0) :=
  integral_cycles% (symm := [a, b]) (a, a, b) (a, b, b) (a, a, a) (b, b, b)

-- TODO: proof of counts
-- every RA with m/n atoms is iso to one of these, and there are 1, 2, 3, 7, ... in the quotient
-- leave docs that explain this doesn't scale, this is brute force for small ones!

end IntegralAtom

end Cslib.RelationAlgebra
