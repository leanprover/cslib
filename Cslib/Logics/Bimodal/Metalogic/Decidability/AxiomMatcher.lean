/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import Cslib.Logics.Bimodal.Metalogic.Decidability.Tableau
import Cslib.Logics.Bimodal.ProofSystem.Derivation

/-!
# Axiom Pattern Matcher for Tableau Decision Procedure

This module provides the `matchAxiom` function that checks whether a given
formula is an instance of one of the 42 axiom schemata of bimodal logic TM.
It is extracted from the full ProofSearch.Core module (which contains ~1,195
lines of search infrastructure) as the minimal prerequisite for Closure.lean
and ProofExtraction.lean.

## Main Definitions

- `matchAxiom`: Match a formula against all 42 axiom schemata, returning
  `some ⟨φ, witness⟩` if the formula matches axiom schema `φ` with witness
  `witness : Axiom φ`
- `matches_axiom`: Boolean check for axiom pattern match
- `matchDerived`: Stub for derived theorem matching (returns `none`)
- `bounded_search_with_proof`: Stub for proof search (returns `(none, 0, 0)`)
- `identity`: Identity combinator `A → A` from prop_k + prop_s axioms

## Implementation Notes

The `matchAxiom` function is a pure pattern-matching function with no side
effects. It checks the formula against each axiom schema in order:
1. Propositional: efq, imp_k, peirce
2. Modal: modal_k_dist, modal_5_collapse, modal_4, modal_future, modal_b, modal_t
3. Ground temporal: serial_future/past, discrete_*, dense_indicator
4. 1-parameter temporal: connect_future/past, F_until_equiv, P_since_equiv, z1, density
5. 2-parameter temporal: self_accum_*, absorb_*, until_F, since_P, temp_linearity*,
   prior_UZ, prior_SZ
6. 3-parameter temporal: left_mono_*, right_mono_*, enrichment_*
7. 4-parameter temporal: linear_until, linear_since
8. imp_s (last, very general: φ → (ψ → φ))

Ordering matters: more specific patterns must come before more general ones
(e.g., modal_4 before modal_t, since □φ → □□φ would also match □ψ → ψ with
ψ = □φ).

Ported from BimodalLogic/Automation/ProofSearch/Core.lean with adaptations
for universe-polymorphic `Formula Atom`.

## References

* Gore, R. (1999). Tableau Methods for Modal and Temporal Logics
-/

set_option linter.style.longLine false

namespace Cslib.Logic.Bimodal.Metalogic.Decidability

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.DerivationTree

variable {Atom : Type u} [DecidableEq Atom]

/-- Bundled axiom witness: a formula together with an `Axiom` proof that it is an axiom. -/
abbrev AxiomWitness (Atom : Type u) := Sigma (@Axiom Atom)

/-!
## Axiom Pattern Matcher
-/

/--
Match a formula against axiom patterns, returning the Axiom witness if matched.

This function enables proof term construction by returning the actual
Axiom constructor that matches the formula pattern. Now that Axiom is a Type
(not Prop), we can use the witness in DerivationTree construction.

**Returns**: `some ⟨φ, witness⟩` if φ matches an axiom schema, `none` otherwise

**Performance**: O(1) - pattern matching on formula structure

**Design Notes**:
- Uses `Sigma Axiom` to package the witness with its formula type
- The formula returned is the matched formula (same as input on success)
- Each axiom pattern is checked in sequence with early return on match
- Uses a decomposition approach to handle derived operators
-/
def matchAxiom (φ : Formula Atom) : Option (AxiomWitness Atom) :=
  -- Decompose into implication (all 42 axioms are implications or negations)
  match φ with
  | .imp lhs rhs =>
      -- efq: ⊥ → φ
      (if lhs = .bot then some ⟨_, Axiom.efq rhs⟩ else none)

      -- imp_k: (φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))
      <|> (match lhs, rhs with
           | .imp a (.imp b c), .imp (.imp a' b') (.imp a'' c') =>
               if a = a' ∧ a' = a'' ∧ b = b' ∧ c = c' then
                 some ⟨_, Axiom.imp_k a b c⟩
               else none
           | _, _ => none)

      -- peirce: ((φ → ψ) → φ) → φ
      <|> (match lhs, rhs with
           | .imp (.imp phi psi) phi', phi'' =>
               if phi = phi' ∧ phi' = phi'' then
                 some ⟨_, Axiom.peirce phi psi⟩
               else none
           | _, _ => none)

      -- modal_k_dist: □(φ → ψ) → (□φ → □ψ)
      <|> (match lhs, rhs with
           | .box (.imp phi psi), .imp (.box phi') (.box psi') =>
               if phi = phi' ∧ psi = psi' then
                 some ⟨_, Axiom.modal_k_dist phi psi⟩
               else none
           | _, _ => none)

      -- modal_5_collapse: ◇□φ → □φ
      <|> (match lhs, rhs with
           | .diamond (.box phi), .box phi' =>
               if phi = phi' then
                 some ⟨_, Axiom.modal_5_collapse phi⟩
               else none
           | _, _ => none)

      -- modal_4: □φ → □□φ
      <|> (match lhs, rhs with
           | .box phi, .box (.box phi') =>
               if phi = phi' then
                 some ⟨_, Axiom.modal_4 phi⟩
               else none
           | _, _ => none)

      -- modal_future: □φ → □(Gφ)
      <|> (match lhs, rhs with
           | .box phi, .box (.all_future phi') =>
               if phi = phi' then
                 some ⟨_, Axiom.modal_future phi⟩
               else none
           | _, _ => none)

      -- modal_b: φ → □◇φ
      <|> (match lhs, rhs with
           | phi, .box (.diamond phi') =>
               if phi = phi' then
                 some ⟨_, Axiom.modal_b phi⟩
               else none
           | _, _ => none)

      -- modal_t: □φ → φ (general; must come after modal_4, modal_future)
      <|> (match lhs, rhs with
           | .box phi, phi' =>
               if phi = phi' then
                 some ⟨_, Axiom.modal_t phi⟩
               else none
           | _, _ => none)

      -------------------------------------------------------------------
      -- Ground axioms (0-parameter)
      -------------------------------------------------------------------

      -- serial_future: ⊤ → F(⊤)
      <|> (match lhs, rhs with
           | .imp .bot .bot, .some_future (.imp .bot .bot) =>
               some ⟨_, Axiom.serial_future⟩
           | _, _ => none)

      -- serial_past: ⊤ → P(⊤)
      <|> (match lhs, rhs with
           | .imp .bot .bot, .some_past (.imp .bot .bot) =>
               some ⟨_, Axiom.serial_past⟩
           | _, _ => none)

      -- discrete_symm_fwd: U(⊤,⊥) → S(⊤,⊥)
      <|> (match lhs, rhs with
           | .untl (.imp .bot .bot) .bot, .snce (.imp .bot .bot) .bot =>
               some ⟨_, Axiom.discrete_symm_fwd⟩
           | _, _ => none)

      -- discrete_symm_bwd: S(⊤,⊥) → U(⊤,⊥)
      <|> (match lhs, rhs with
           | .snce (.imp .bot .bot) .bot, .untl (.imp .bot .bot) .bot =>
               some ⟨_, Axiom.discrete_symm_bwd⟩
           | _, _ => none)

      -- discrete_propagate_fwd: U(⊤,⊥) → G(U(⊤,⊥))
      <|> (match lhs, rhs with
           | .untl (.imp .bot .bot) .bot, .all_future (.untl (.imp .bot .bot) .bot) =>
               some ⟨_, Axiom.discrete_propagate_fwd⟩
           | _, _ => none)

      -- discrete_propagate_bwd: U(⊤,⊥) → H(U(⊤,⊥))
      <|> (match lhs, rhs with
           | .untl (.imp .bot .bot) .bot, .all_past (.untl (.imp .bot .bot) .bot) =>
               some ⟨_, Axiom.discrete_propagate_bwd⟩
           | _, _ => none)

      -- discrete_box_necessity: U(⊤,⊥) → □(U(⊤,⊥))
      <|> (match lhs, rhs with
           | .untl (.imp .bot .bot) .bot, .box (.untl (.imp .bot .bot) .bot) =>
               some ⟨_, Axiom.discrete_box_necessity⟩
           | _, _ => none)

      -- dense_indicator: ¬U(⊤,⊥) = U(⊤,⊥) → ⊥
      <|> (match lhs, rhs with
           | .untl (.imp .bot .bot) .bot, .bot =>
               some ⟨_, Axiom.dense_indicator⟩
           | _, _ => none)

      -------------------------------------------------------------------
      -- 1-parameter axioms
      -------------------------------------------------------------------

      -- connect_future (BX4): φ → G(P(φ))
      <|> (match lhs, rhs with
           | phi, .all_future (.some_past phi') =>
               if phi = phi' then
                 some ⟨_, Axiom.connect_future phi⟩
               else none
           | _, _ => none)

      -- connect_past (BX4'): φ → H(F(φ))
      <|> (match lhs, rhs with
           | phi, .all_past (.some_future phi') =>
               if phi = phi' then
                 some ⟨_, Axiom.connect_past phi⟩
               else none
           | _, _ => none)

      -- F_until_equiv (BX12): F(φ) → U(φ, ⊤)
      <|> (match lhs, rhs with
           | .some_future phi, .untl phi' (.imp .bot .bot) =>
               if phi = phi' then
                 some ⟨_, Axiom.F_until_equiv phi⟩
               else none
           | _, _ => none)

      -- P_since_equiv (BX12'): P(φ) → S(φ, ⊤)
      <|> (match lhs, rhs with
           | .some_past phi, .snce phi' (.imp .bot .bot) =>
               if phi = phi' then
                 some ⟨_, Axiom.P_since_equiv phi⟩
               else none
           | _, _ => none)

      -- z1: G(Gφ→φ) → (F(Gφ)→Gφ)
      <|> (match lhs, rhs with
           | .all_future (.imp (.all_future phi) phi'),
             .imp (.some_future (.all_future phi'')) (.all_future phi''') =>
               if phi = phi' ∧ phi' = phi'' ∧ phi'' = phi''' then
                 some ⟨_, Axiom.z1 phi⟩
               else none
           | _, _ => none)

      -- density: GGφ → Gφ
      <|> (match lhs, rhs with
           | .all_future (.all_future phi), .all_future phi' =>
               if phi = phi' then
                 some ⟨_, Axiom.density phi⟩
               else none
           | _, _ => none)

      -------------------------------------------------------------------
      -- 2-parameter axioms
      -------------------------------------------------------------------

      -- self_accum_until (BX5): U(ψ,φ) → U(ψ, φ∧U(ψ,φ))
      <|> (match lhs, rhs with
           | .untl psi phi, .untl psi' (.and phi' (.untl psi'' phi'')) =>
               if phi = phi' ∧ phi' = phi'' ∧ psi = psi' ∧ psi' = psi'' then
                 some ⟨_, Axiom.self_accum_until phi psi⟩
               else none
           | _, _ => none)

      -- self_accum_since (BX5'): S(ψ,φ) → S(ψ, φ∧S(ψ,φ))
      <|> (match lhs, rhs with
           | .snce psi phi, .snce psi' (.and phi' (.snce psi'' phi'')) =>
               if phi = phi' ∧ phi' = phi'' ∧ psi = psi' ∧ psi' = psi'' then
                 some ⟨_, Axiom.self_accum_since phi psi⟩
               else none
           | _, _ => none)

      -- absorb_until (BX6): U(φ∧U(ψ,φ), φ) → U(ψ,φ)
      <|> (match lhs, rhs with
           | .untl (.and phi (.untl psi phi')) phi'', .untl psi' phi''' =>
               if phi = phi' ∧ phi' = phi'' ∧ phi'' = phi''' ∧ psi = psi' then
                 some ⟨_, Axiom.absorb_until phi psi⟩
               else none
           | _, _ => none)

      -- absorb_since (BX6'): S(φ∧S(ψ,φ), φ) → S(ψ,φ)
      <|> (match lhs, rhs with
           | .snce (.and phi (.snce psi phi')) phi'', .snce psi' phi''' =>
               if phi = phi' ∧ phi' = phi'' ∧ phi'' = phi''' ∧ psi = psi' then
                 some ⟨_, Axiom.absorb_since phi psi⟩
               else none
           | _, _ => none)

      -- until_F (BX10): U(ψ,φ) → F(ψ)
      <|> (match lhs, rhs with
           | .untl psi _phi, .some_future psi' =>
               if psi = psi' then
                 some ⟨_, Axiom.until_F _phi psi⟩
               else none
           | _, _ => none)

      -- since_P (BX10'): S(ψ,φ) → P(ψ)
      <|> (match lhs, rhs with
           | .snce psi _phi, .some_past psi' =>
               if psi = psi' then
                 some ⟨_, Axiom.since_P _phi psi⟩
               else none
           | _, _ => none)

      -- temp_linearity (BX11): F(φ)∧F(ψ) → F(φ∧ψ) ∨ F(φ∧F(ψ)) ∨ F(F(φ)∧ψ)
      <|> (match lhs, rhs with
           | .and (.some_future phi) (.some_future psi),
             .or (.some_future (.and phi' psi'))
               (.or (.some_future (.and phi'' (.some_future psi'')))
                 (.some_future (.and (.some_future phi''') psi'''))) =>
               if phi = phi' ∧ phi' = phi'' ∧ phi'' = phi''' ∧
                  psi = psi' ∧ psi' = psi'' ∧ psi'' = psi''' then
                 some ⟨_, Axiom.temp_linearity phi psi⟩
               else none
           | _, _ => none)

      -- temp_linearity_past (BX11'): P(φ)∧P(ψ) → P(φ∧ψ) ∨ P(φ∧P(ψ)) ∨ P(P(φ)∧ψ)
      <|> (match lhs, rhs with
           | .and (.some_past phi) (.some_past psi),
             .or (.some_past (.and phi' psi'))
               (.or (.some_past (.and phi'' (.some_past psi'')))
                 (.some_past (.and (.some_past phi''') psi'''))) =>
               if phi = phi' ∧ phi' = phi'' ∧ phi'' = phi''' ∧
                  psi = psi' ∧ psi' = psi'' ∧ psi'' = psi''' then
                 some ⟨_, Axiom.temp_linearity_past phi psi⟩
               else none
           | _, _ => none)

      -- prior_UZ: F(φ) → U(φ, ¬φ)
      <|> (match lhs, rhs with
           | .some_future phi1, .untl phi2 (.neg phi3) =>
               if phi1 = phi2 ∧ phi2 = phi3 then
                 some ⟨_, Axiom.prior_UZ phi1⟩
               else none
           | _, _ => none)

      -- prior_SZ: P(φ) → S(φ, ¬φ)
      <|> (match lhs, rhs with
           | .some_past phi1, .snce phi2 (.neg phi3) =>
               if phi1 = phi2 ∧ phi2 = phi3 then
                 some ⟨_, Axiom.prior_SZ phi1⟩
               else none
           | _, _ => none)

      -------------------------------------------------------------------
      -- 3-parameter axioms
      -------------------------------------------------------------------

      -- left_mono_until_G (BX2G): G(φ→χ) → (U(ψ,φ) → U(ψ,χ))
      <|> (match lhs, rhs with
           | .all_future (.imp phi chi),
             .imp (.untl psi phi') (.untl psi' chi') =>
               if phi = phi' ∧ chi = chi' ∧ psi = psi' then
                 some ⟨_, Axiom.left_mono_until_G phi chi psi⟩
               else none
           | _, _ => none)

      -- left_mono_since_H (BX2H): H(φ→χ) → (S(ψ,φ) → S(ψ,χ))
      <|> (match lhs, rhs with
           | .all_past (.imp phi chi),
             .imp (.snce psi phi') (.snce psi' chi') =>
               if phi = phi' ∧ chi = chi' ∧ psi = psi' then
                 some ⟨_, Axiom.left_mono_since_H phi chi psi⟩
               else none
           | _, _ => none)

      -- right_mono_until (BX3): G(φ→ψ) → (U(φ,χ) → U(ψ,χ))
      <|> (match lhs, rhs with
           | .all_future (.imp phi psi),
             .imp (.untl phi' chi) (.untl psi' chi') =>
               if phi = phi' ∧ psi = psi' ∧ chi = chi' then
                 some ⟨_, Axiom.right_mono_until phi psi chi⟩
               else none
           | _, _ => none)

      -- right_mono_since (BX3'): H(φ→ψ) → (S(φ,χ) → S(ψ,χ))
      <|> (match lhs, rhs with
           | .all_past (.imp phi psi),
             .imp (.snce phi' chi) (.snce psi' chi') =>
               if phi = phi' ∧ psi = psi' ∧ chi = chi' then
                 some ⟨_, Axiom.right_mono_since phi psi chi⟩
               else none
           | _, _ => none)

      -- enrichment_until (BX13): p∧U(ψ,φ) → U(ψ∧S(p,φ), φ)
      <|> (match lhs, rhs with
           | .and pp (.untl psi phi),
             .untl (.and psi' (.snce pp' phi')) phi'' =>
               if phi = phi' ∧ phi' = phi'' ∧ psi = psi' ∧ pp = pp' then
                 some ⟨_, Axiom.enrichment_until phi psi pp⟩
               else none
           | _, _ => none)

      -- enrichment_since (BX13'): p∧S(ψ,φ) → S(ψ∧U(p,φ), φ)
      <|> (match lhs, rhs with
           | .and pp (.snce psi phi),
             .snce (.and psi' (.untl pp' phi')) phi'' =>
               if phi = phi' ∧ phi' = phi'' ∧ psi = psi' ∧ pp = pp' then
                 some ⟨_, Axiom.enrichment_since phi psi pp⟩
               else none
           | _, _ => none)

      -------------------------------------------------------------------
      -- 4-parameter axioms
      -------------------------------------------------------------------

      -- linear_until (BX7): U(ψ,φ)∧U(θ,χ) → U(ψ∧θ,φ∧χ) ∨ U(ψ∧χ,φ∧χ) ∨ U(φ∧θ,φ∧χ)
      <|> (match lhs, rhs with
           | .and (.untl psi phi) (.untl theta chi),
             .or (.or (.untl (.and psi' theta') (.and phi' chi'))
                      (.untl (.and psi'' chi'') (.and phi'' chi''')))
                 (.untl (.and phi'''' theta'') (.and phi''''' chi'''')) =>
               if psi = psi' ∧ psi' = psi'' ∧
                  theta = theta' ∧ theta' = theta'' ∧
                  phi = phi' ∧ phi' = phi'' ∧ phi'' = phi'''' ∧ phi'''' = phi''''' ∧
                  chi = chi' ∧ chi' = chi'' ∧ chi'' = chi''' ∧ chi''' = chi'''' then
                 some ⟨_, Axiom.linear_until phi psi chi theta⟩
               else none
           | _, _ => none)

      -- linear_since (BX7'): S(ψ,φ)∧S(θ,χ) → S(ψ∧θ,φ∧χ) ∨ S(ψ∧χ,φ∧χ) ∨ S(φ∧θ,φ∧χ)
      <|> (match lhs, rhs with
           | .and (.snce psi phi) (.snce theta chi),
             .or (.or (.snce (.and psi' theta') (.and phi' chi'))
                      (.snce (.and psi'' chi'') (.and phi'' chi''')))
                 (.snce (.and phi'''' theta'') (.and phi''''' chi'''')) =>
               if psi = psi' ∧ psi' = psi'' ∧
                  theta = theta' ∧ theta' = theta'' ∧
                  phi = phi' ∧ phi' = phi'' ∧ phi'' = phi'''' ∧ phi'''' = phi''''' ∧
                  chi = chi' ∧ chi' = chi'' ∧ chi'' = chi''' ∧ chi''' = chi'''' then
                 some ⟨_, Axiom.linear_since phi psi chi theta⟩
               else none
           | _, _ => none)

      -------------------------------------------------------------------
      -- imp_s must be LAST (very general: φ → (ψ → φ))
      -------------------------------------------------------------------

      -- imp_s: φ → (ψ → φ)
      <|> (match lhs, rhs with
           | phi, .imp psi phi' =>
               if phi = phi' then
                 some ⟨_, Axiom.imp_s phi psi⟩
               else none
           | _, _ => none)

  | _ => none

/--
Check if a formula matches any of the 42 TM axiom schemata.

Delegates to `matchAxiom` and returns `true` on match, `false` otherwise.
-/
def matches_axiom (φ : Formula Atom) : Bool :=
  (matchAxiom φ).isSome

/-!
## Stub Functions

These stubs replace the full ProofSearch.Core infrastructure that is not
needed for the core decidability module. They will be filled in when the
full automation module is ported.
-/

/--
Stub for derived theorem matching. Returns `none`.

The full implementation would match patterns like `temp_future_derived`:
`box phi -> G(box phi)`. This is deferred since the decidability procedure
does not require derived theorem matching for correctness.
-/
def matchDerived (φ : Formula Atom) :
    Option (DerivationTree FrameClass.Base ([] : Context Atom) φ) := none

/--
Stub for bounded proof search with proof term construction.
Returns `(none, 0, 0)`.

The full implementation performs depth-limited DFS to find derivation trees.
This is deferred since the decidability procedure uses tableau expansion
rather than forward proof search.
-/
def bounded_search_with_proof_stub
    (_ : Context Atom) (φ : Formula Atom) (_ : Nat) :
    Option (DerivationTree FrameClass.Base ([] : Context Atom) φ) × Nat × Nat :=
  (none, 0, 0)

/-!
## Identity Combinator

The identity combinator `A -> A` is needed by ProofExtraction.lean for
constructing proofs from axiom instances. It is built from `imp_k` and
`imp_s` axioms via modus ponens (standard SKK combinator proof).

Proof sketch:
- imp_k A (A->A) A : (A -> ((A->A) -> A)) -> ((A -> (A->A)) -> (A -> A))
- imp_s A (A->A) : A -> ((A->A) -> A)
- MP gives: (A -> (A->A)) -> (A -> A)
- imp_s A A : A -> (A -> A)
- MP gives: A -> A
-/
def identity (A : Formula Atom) :
    DerivationTree FrameClass.Base ([] : Context Atom) (A.imp A) :=
  -- Step 1: imp_k A (A->A) A
  let s1 := DerivationTree.axiom ([] : Context Atom)
    ((A.imp ((A.imp A).imp A)).imp ((A.imp (A.imp A)).imp (A.imp A)))
    (Axiom.imp_k A (A.imp A) A) (FrameClass.base_le _)
  -- Step 2: imp_s A (A->A)
  let s2 := DerivationTree.axiom ([] : Context Atom)
    (A.imp ((A.imp A).imp A))
    (Axiom.imp_s A (A.imp A)) (FrameClass.base_le _)
  -- Step 3: MP(s1, s2) : (A -> (A->A)) -> (A -> A)
  let s3 := DerivationTree.modus_ponens ([] : Context Atom)
    (A.imp ((A.imp A).imp A))
    ((A.imp (A.imp A)).imp (A.imp A)) s1 s2
  -- Step 4: imp_s A A : A -> (A -> A)
  let s4 := DerivationTree.axiom ([] : Context Atom)
    (A.imp (A.imp A))
    (Axiom.imp_s A A) (FrameClass.base_le _)
  -- Step 5: MP(s3, s4) : A -> A
  DerivationTree.modus_ponens ([] : Context Atom)
    (A.imp (A.imp A)) (A.imp A) s3 s4

end Cslib.Logic.Bimodal.Metalogic.Decidability
