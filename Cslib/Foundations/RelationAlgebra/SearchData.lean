/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.SearchCertificate
public meta import Lean.Elab.Term

/-!
# Large numeric literals for search data

`nat_lit% "digits"` elaborates a decimal string directly to a natural-number literal. Lean string
gaps allow generated data to span source lines without introducing runtime parsing or arithmetic.
The result is ordinary numeric data; every use in a certificate is still checked by the kernel.

`certificate_lit% "prefix tokens" [helpers]` similarly elaborates search certificates directly to
ordinary constructor expressions. It changes only data entry, leaving the counting checker intact.
-/

public meta section

namespace Cslib.RelationAlgebra.Search

open Lean Elab Term Counting

/-- Elaborate decimal string data to an ordinary natural-number literal. -/
elab "nat_lit% " literal:str : term =>
  match literal.getString.toNat? with
  | some value => pure (mkNatLit value)
  | none => throwErrorAt literal "expected a nonempty string of decimal digits"

/-- Parse one decimal index from certificate data. -/
def parseCertificateIndex : List String → Except String (Nat × List String)
  | [] => .error "expected a decimal index"
  | token :: rest =>
    match token.toNat? with
    | some value => .ok (value, rest)
    | none => .error "expected a decimal index"

/-- Parse ordinary certificate constructor expressions from prefix tokens. -/
partial def parseCertificateTokens (helpers : Array Expr) :
    List String → Except String (Expr × List String)
  | [] => .error "unexpected end of input"
  | tag :: tokens => do
    match tag with
    | "a" => return (Lean.mkConst ``Certificate.accept, tokens)
    | "r" =>
      let (witness, rest) ← parseCertificateIndex tokens
      return (mkApp (Lean.mkConst ``Certificate.reject) (mkNatLit witness), rest)
    | "b" =>
      let (index, rest) ← parseCertificateIndex tokens
      let (low, rest) ← parseCertificateTokens helpers rest
      let (high, rest) ← parseCertificateTokens helpers rest
      return (mkAppN (Lean.mkConst ``Certificate.branch) #[mkNatLit index, low, high], rest)
    | "f" =>
      let (index, rest) ← parseCertificateIndex tokens
      let (value, rest) ← parseCertificateIndex rest
      let value ← match value with
        | 0 => pure (Lean.mkConst ``Bool.false)
        | 1 => pure (Lean.mkConst ``Bool.true)
        | _ => throw "forced value must be 0 or 1"
      let (witness, rest) ← parseCertificateIndex rest
      let (next, rest) ← parseCertificateTokens helpers rest
      return (mkAppN (Lean.mkConst ``Certificate.force)
        #[mkNatLit index, value, mkNatLit witness, next], rest)
    | "s" =>
      let (witness, rest) ← parseCertificateIndex tokens
      let (next, rest) ← parseCertificateTokens helpers rest
      return (mkAppN (Lean.mkConst ``Certificate.simplify) #[mkNatLit witness, next], rest)
    | "c" =>
      let (index, rest) ← parseCertificateIndex tokens
      return (mkApp (Lean.mkConst ``Certificate.reference) (mkNatLit index), rest)
    | "h" =>
      let (index, rest) ← parseCertificateIndex tokens
      match helpers[index]? with
      | some helper => return (helper, rest)
      | none => throw "helper index out of range"
    | _ => throw "unknown instruction tag"

/-- Elaborate prefix certificate data into ordinary constructor expressions. -/
elab "certificate_lit% " literal:str " [" helpers:term,* "]" : term => do
  let helpers ← helpers.getElems.mapM fun helper =>
    elabTerm helper (some (Lean.mkConst ``Certificate))
  let tokens := (literal.getString.splitOn " ").filter fun token => !token.isEmpty
  match parseCertificateTokens helpers tokens with
  | .error message => throwErrorAt literal "invalid certificate literal: {message}"
  | .ok (value, []) => return value
  | .ok (_, _ :: _) => throwErrorAt literal "invalid certificate literal: trailing input"


end Cslib.RelationAlgebra.Search
