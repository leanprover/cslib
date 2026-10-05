/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.FastCycles
public import Cslib.Foundations.RelationAlgebra.WitnessRepresentation

/-!
# Numeric verification of composition-witness policies

The triangle condition for a witness policy quantifies over eight atoms. Checking its numeric
form avoids repeatedly constructing finite enumerations and decoding atom equality.
-/

@[expose] public section

namespace Cslib.RelationAlgebra

namespace Code

/-- Check the triangle condition of a witness policy using atom codes. -/
def witnessTriangleCheck (n j t : ℕ) (label : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) : Bool :=
  let C a b c := bitAt t (index n a b c)
  allBelow (fun a => !decide (a ≠ 0) ||
    allBelow (fun b => !decide (b ≠ 0) ||
      allBelow (fun c => !C a b c ||
        allBelow (fun d => allBelow (fun e => !C d (conv j e) c ||
          !decide ((d, e) ≠ (a, conv j b)) ||
          allBelow (fun d' => allBelow (fun e' => !C d' (conv j e') c ||
            !decide ((d', e') ≠ (a, conv j b)) ||
            allBelow (fun h => !C d h d' || !C e h e' ||
              C h (label a b c d' e') (label a b c d e)) n) n) n) n) n) n) n) n

end Code

/-- A successful numeric triangle check supplies the corresponding witness-policy field. -/
theorem witnessTriangle_of_check {j k t : ℕ} {cycles : Finset (Cycle j k)}
    (ht : EncodesTable cycles t)
    (label : Atom j k → Atom j k → Atom j k → Atom j k → Atom j k → Atom j k)
    (labelCode : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ)
    (hlabel : ∀ a b c d e, (label a b c d e).code =
      labelCode a.code b.code c.code d.code e.code)
    (hcheck : Code.witnessTriangleCheck (atomCount j k) j t labelCode = true)
    {a b c d e d' e' h : Atom j k} (ha : a ≠ none) (hb : b ≠ none)
    (hc : cycleClosure cycles a b c)
    (hp : cycleClosure cycles d (Atom.converse e) c)
    (hp' : cycleClosure cycles d' (Atom.converse e') c)
    (hne : (d, e) ≠ (a, Atom.converse b))
    (hne' : (d', e') ≠ (a, Atom.converse b))
    (hd : cycleClosure cycles d h d') (he : cycleClosure cycles e h e') :
    cycleClosure cycles h (label a b c d' e') (label a b c d e) := by
  simp only [Code.witnessTriangleCheck, Bool.or_assoc, Code.allBelow_eq_true, Code.not_or_eq_true,
    decide_eq_true_eq] at hcheck
  have hpair {x y : Atom j k} (hne : (x, y) ≠ (a, Atom.converse b)) :
      (x.code, y.code) ≠ (a.code, Code.conv j b.code) := by
    intro hxy
    apply hne
    apply Prod.ext
    · exact Atom.code_injective (congrArg Prod.fst hxy)
    · apply Atom.code_injective
      simpa only [Atom.code_converse] using congrArg Prod.snd hxy
  have hcycle (x y z : Atom j k) (h : cycleClosure cycles x y z) :=
    (cycleClosure_iff_bitAt ht x y z).mp h
  rw [cycleClosure_iff_bitAt ht, hlabel, hlabel]
  apply hcheck a.code a.code_lt ((Atom.code_eq_zero).not.mpr ha)
    b.code b.code_lt ((Atom.code_eq_zero).not.mpr hb) c.code c.code_lt (hcycle _ _ _ hc)
    d.code d.code_lt e.code e.code_lt
    (by simpa only [Atom.code_converse] using hcycle _ _ _ hp) (hpair hne)
    d'.code d'.code_lt e'.code e'.code_lt
    (by simpa only [Atom.code_converse] using hcycle _ _ _ hp') (hpair hne')
    h.code h.code_lt (hcycle _ _ _ hd) (hcycle _ _ _ he)

end Cslib.RelationAlgebra
