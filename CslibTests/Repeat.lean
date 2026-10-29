/-
Copyright (c) 2026 Yusuf Demir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yusuf Demir
-/

import Cslib.Foundations.Data.List.Repeat

/-! # Occurrences and right-maximal repeats

The right-maximal repeats of `mississimiss` are `i`, `iss`, `issi`, `miss`, `s`, `si`, `ss` and
`ssi`. Note that `iss` and its proper infixes `i`, `s` and `ss` are all right-maximal.
-/

set_option linter.hashCommand false

namespace CslibTests.Repeat

open List

/-- The running example. -/
def mississimiss : List Char := "mississimiss".toList

#guard "iss".toList.occurrences mississimiss = [1, 4, 9]
#guard "s".toList.occurrences mississimiss = [2, 3, 5, 6, 10, 11]
#guard "miss".toList.occurrences mississimiss = [0, 8]

-- `miss` and `iss` are right-maximal only because of their occurrences at the end of the word.
#guard "miss".toList.IsRightMaximalRepeat mississimiss
#guard "iss".toList.IsRightMaximalRepeat mississimiss

-- `is` occurs three times, always followed by `s`.
#guard "is".toList.IsRepeat mississimiss
#guard ¬ "is".toList.IsRightMaximalRepeat mississimiss

#guard (rightMaximalRepeats mississimiss).length = 8
#guard ["i", "iss", "issi", "miss", "s", "si", "ss", "ssi"].all
  fun s => s.toList ∈ rightMaximalRepeats mississimiss

-- A word of length `n` has at most `n - 1` right-maximal repeats, and `aaaa` has three.
#guard (rightMaximalRepeats "aaaa".toList).length = 3

end CslibTests.Repeat
