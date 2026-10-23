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

open Lean Elab Term Meta

declare_syntax_cat integralCycleAtom
syntax ident ("˘")? : integralCycleAtom

declare_syntax_cat integralCycle
syntax "(" integralCycleAtom "," integralCycleAtom "," integralCycleAtom ")" : integralCycle

declare_syntax_cat integralCycleOption
syntax "(" &"symm" ":=" ident,* ")" : integralCycleOption
syntax "(" &"nonsymm" ":=" ident,* ")" : integralCycleOption

syntax (name := integralCycles)
  "integral_cycles%" (atomic(integralCycleOption))* integralCycle* : term

@[term_elab integralCycles]
def elabIntegralCycles : TermElab := fun stx expectedType? => do
  let `(integral_cycles% $options:integralCycleOption* $cycles:integralCycle*) := stx
    | throwUnsupportedSyntax
  let parseAtom (stx : Syntax) : TermElabM (Ident × Bool) := do
    let `(integralCycleAtom| $name:ident $[˘%$mark]?) := stx | throwUnsupportedSyntax
    return (name, mark.isSome)
  let mut symmNames : Array Name := #[]
  let mut nonsymmNames : Array Name := #[]
  let mut hasSymm := false
  let mut hasNonsymm := false
  for option in options do
    let (isNonsymm, names) ← match option with
      | `(integralCycleOption| (symm := $names:ident,*)) => pure (false, names.getElems)
      | `(integralCycleOption| (nonsymm := $names:ident,*)) => pure (true, names.getElems)
      | _ => throwUnsupportedSyntax
    if isNonsymm then
      if hasNonsymm then
        throwErrorAt option "duplicate nonsymm declaration"
      hasNonsymm := true
    else
      if hasSymm then
        throwErrorAt option "duplicate symm declaration"
      hasSymm := true
    for name in names do
      if symmNames.contains name.getId || nonsymmNames.contains name.getId then
        throwErrorAt name "atom '{name.getId}' is declared more than once"
      if isNonsymm then
        nonsymmNames := nonsymmNames.push name.getId
      else
        symmNames := symmNames.push name.getId
  let cycles ← cycles.mapM fun cycle => do
    let `(integralCycle| ($r, $s, $t)) := cycle
      | throwUnsupportedSyntax
    return (← parseAtom r, ← parseAtom s, ← parseAtom t)
  let mut names : Array Name := #[]
  let mut converseNames : Array Name := #[]
  for (r, s, t) in cycles do
    for (name, isConverse) in #[r, s, t] do
      unless names.contains name.getId do
        names := names.push name.getId
      if isConverse && !converseNames.contains name.getId then
        converseNames := converseNames.push name.getId
  for name in names do
    unless symmNames.contains name || nonsymmNames.contains name do
      if converseNames.contains name then
        nonsymmNames := nonsymmNames.push name
      else
        symmNames := symmNames.push name
  let atomTerm (atom : Ident × Bool) : TermElabM (TSyntax `term) := do
    let (name, isConverse) := atom
    if let some i := symmNames.findIdx? (· == name.getId) then
      `(IntegralAtom.symm $(quote i))
    else if let some i := nonsymmNames.findIdx? (· == name.getId) then
      `(IntegralAtom.nsymm $(quote i) $(quote isConverse))
    else
      throwErrorAt name "unknown atom '{name.getId}'"
  let cycleTerms ← cycles.mapM fun (r, s, t) => do
    `(($(← atomTerm r), $(← atomTerm s), $(← atomTerm t)))
  let s := quote symmNames.size
  let n := quote nonsymmNames.size
  let generators ← if cycleTerms.isEmpty then
    `(term| (∅ : Finset (Cycle $s $n)))
  else
    `(term| ({$[$cycleTerms:term],*} : Finset (Cycle $s $n)))
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

def ra_1_2 : AtomStructure (IntegralAtom 1 0) := integral_cycles% (symm := a)

def ra_2_2 : AtomStructure (IntegralAtom 1 0) := integral_cycles% (a, a, a)

def ra_1_3 : AtomStructure (IntegralAtom 0 1) := integral_cycles% (nonsymm := a) (a, a, a)

def ra_2_3 : AtomStructure (IntegralAtom 0 1) := integral_cycles% (a, a, a˘)

def ra_3_3 : AtomStructure (IntegralAtom 0 1) := integral_cycles% (a, a, a˘) (a, a, a)

def ra_1_7 : AtomStructure (IntegralAtom 2 0) := integral_cycles% (a, b, b)

def ra_2_7 : AtomStructure (IntegralAtom 2 0) := integral_cycles% (a, b, b) (a, a, a)

def ra_3_7 : AtomStructure (IntegralAtom 2 0) := integral_cycles% (a, b, b) (b, b, b)

def ra_4_7 : AtomStructure (IntegralAtom 2 0) := integral_cycles% (a, b, b) (a, a, a) (b, b, b)

def ra_5_7 : AtomStructure (IntegralAtom 2 0) := integral_cycles% (a, a, b) (a, b, b)

def ra_6_7 : AtomStructure (IntegralAtom 2 0) := integral_cycles% (a, a, b) (a, b, b) (a, a, a)

def ra_7_7 : AtomStructure (IntegralAtom 2 0) :=
  integral_cycles% (a, a, b) (a, b, b) (a, a, a) (b, b, b)

-- TODO: proof of counts
-- every RA with m/n atoms is iso to one of these, and there are 1, 2, 3, 7, ... in the quotient
-- leave docs that explain this doesn't scale, this is brute force for small ones!

end IntegralAtom

end Cslib.RelationAlgebra
