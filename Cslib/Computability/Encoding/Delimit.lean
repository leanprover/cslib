/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Init

/-!
# Delimited Boolean words

Defines `delimit` which turns arbitrary Boolean words into a self-delimiting, prefix-free code.
The input words may be empty, contain any bit pattern, or be prefixes of one another.

`delimit` writes each data bit `b` as `[true, b]` and ends the codeword with `[false]`. This means
that `true` introduces one data bit and `false` terminates the word, which makes the boundary
recognizable in one left-to-right pass, even when arbitrary data follows it. A word of length `n`
has a delimited code of length `2 * n + 1`.

`delimit_prefix_delimit` states prefix-freeness: one delimited codeword is a prefix of another
exactly when their original words are equal. `undelimit_delimit_append` and
`dropDelimited_delimit_append` recover a word and the suffix following its codeword.

The guarantee concerns individual delimited words. A variable-length list of concatenated
codewords needs its own delimiter if the entire list encoding is to be prefix-free.
-/

@[expose] public section

namespace Cslib.Encoding

/-! ### Delimited words -/

/-- Each symbol `b` of `w` as `[true, b]`, followed by `[false]`. -/
def delimit (w : List Bool) : List Bool :=
  w.flatMap (fun b => [true, b]) ++ [false]

/-- Read complete tagged bits until the delimiter or end of input. An incomplete trailing tag
is ignored. -/
def undelimit : List Bool → List Bool
  | true :: b :: v => b :: undelimit v
  | _ => []

/-- The suffix after the first delimiter, or `[]` if the input ends before a delimiter. -/
def dropDelimited : List Bool → List Bool
  | true :: _ :: v => dropDelimited v
  | false :: v => v
  | _ => []

@[simp]
theorem delimit_nil : delimit [] = [false] := rfl

@[simp]
theorem delimit_cons (b : Bool) (w : List Bool) : delimit (b :: w) =
    true :: b :: delimit w := rfl

@[simp]
theorem length_delimit (w : List Bool) : (delimit w).length = 2 * w.length + 1 := by
  induction w <;> grind [delimit_nil, delimit_cons]

@[simp]
theorem delimit_ne_nil (w : List Bool) : delimit w ≠ [] := by simp [delimit]

/-! Equation lemmas for `undelimit` and `dropDelimited`. These are needed by `simp` because
`delimit_cons` rewrites `delimit (b :: w)` before the round-trip lemmas below can apply. -/

@[simp] theorem undelimit_nil : undelimit [] = [] := rfl

@[simp] theorem undelimit_false_cons (v : List Bool) : undelimit (false :: v) = [] := rfl

@[simp] theorem undelimit_true_nil : undelimit [true] = [] := rfl

@[simp] theorem undelimit_true_cons_cons (b : Bool) (v : List Bool) :
    undelimit (true :: b :: v) = b :: undelimit v := rfl

@[simp] theorem dropDelimited_nil : dropDelimited [] = [] := rfl

@[simp] theorem dropDelimited_false_cons (v : List Bool) : dropDelimited (false :: v) = v := rfl

@[simp] theorem dropDelimited_true_nil : dropDelimited [true] = [] := rfl

@[simp] theorem dropDelimited_true_cons_cons (b : Bool) (v : List Bool) :
    dropDelimited (true :: b :: v) = dropDelimited v := rfl

@[simp]
theorem undelimit_delimit_append (w u : List Bool) : undelimit (delimit w ++ u) = w := by
  induction w <;> simp [*]

@[simp]
theorem undelimit_delimit (w : List Bool) : undelimit (delimit w) = w := by
  simpa using undelimit_delimit_append w []

@[simp]
theorem dropDelimited_delimit_append (w u : List Bool) :
    dropDelimited (delimit w ++ u) = u := by
  induction w <;> simp [*]

/-- A delimited word followed by another word determines both. -/
theorem delimit_append_inj {w w' u u' : List Bool} (h : delimit w ++ u = delimit w' ++ u') :
    w = w' ∧ u = u' :=
  ⟨by simpa using congrArg undelimit h, by simpa using congrArg dropDelimited h⟩

@[simp]
theorem delimit_append_inj_iff {w w' u u' : List Bool} :
    delimit w ++ u = delimit w' ++ u' ↔ w = w' ∧ u = u' :=
  ⟨delimit_append_inj, by rintro ⟨rfl, rfl⟩; rfl⟩

/-- Delimiting is injective. -/
theorem delimit_injective : Function.Injective delimit := fun _ _ h =>
  (delimit_append_inj (u := []) (u' := []) (by simpa using h)).1

@[simp]
theorem delimit_inj {w w' : List Bool} : delimit w = delimit w' ↔ w = w' :=
  delimit_injective.eq_iff

/-- The image of `delimit` is prefix-free, independently of the input words. -/
@[simp]
theorem delimit_prefix_delimit {w v : List Bool} :
    delimit w <+: delimit v ↔ w = v := by
  constructor
  · rintro ⟨suffix, hs⟩
    exact (delimit_append_inj (u := suffix) (u' := [])
      (by simpa only [List.append_nil] using hs)).1
  · rintro rfl
    exact List.prefix_refl _

end Cslib.Encoding
