import Cslib

namespace CslibTests

open Cslib
open Cslib.Crypto.Protocols.SecretSharing

def trivialParams : Shamir.Params ℚ (Fin 1) where
  threshold := 0
  threshold_lt_card := by decide
  point _ := 1
  point_injective := by
    intro i j _
    fin_cases i
    fin_cases j
    rfl
  point_nonzero _ := by norm_num

def rationalParams : Shamir.Params ℚ (Fin 2) where
  threshold := 1
  threshold_lt_card := by decide
  point i := (i : ℚ) + 1
  point_injective := by
    intro i j hij
    fin_cases i
    · fin_cases j
      · rfl
      · simp at hij
    · fin_cases j
      · simp at hij
      · rfl
  point_nonzero i := by
    fin_cases i <;> norm_num

noncomputable def trivialRawScheme :
    Scheme ℚ (Shamir.Randomness trivialParams) (Fin 1) ℚ :=
  Shamir.Internal.rawSchemeWith trivialParams (PMF.pure (fun i => nomatch i))

def rationalTail : Shamir.Randomness rationalParams := fun _ => 7

noncomputable def rationalRawScheme :
    Scheme ℚ (Shamir.Randomness rationalParams) (Fin 2) ℚ :=
  Shamir.Internal.rawSchemeWith rationalParams (PMF.pure rationalTail)

example : Shamir.authorized trivialParams (Finset.univ : Finset (Fin 1)) := by
  exact Shamir.authorized_univ trivialParams

example : ¬ Shamir.authorized rationalParams ({0} : Finset (Fin 2)) := by
  simp [Shamir.authorized, rationalParams]

example :
    trivialRawScheme.reconstruct
        (Finset.univ : Finset (Fin 1))
        (trivialRawScheme.view (Finset.univ : Finset (Fin 1))
          (fun i => nomatch i) (5 : ℚ)) = 5 := by
  exact Scheme.reconstruct_view_eq_secret
    trivialRawScheme (fun i => nomatch i) (5 : ℚ) (Shamir.authorized_univ trivialParams)

example :
    rationalRawScheme.reconstruct
        (Finset.univ : Finset (Fin 2))
        (rationalRawScheme.view (Finset.univ : Finset (Fin 2))
          rationalTail (5 : ℚ)) = 5 := by
  exact Scheme.reconstruct_view_eq_secret
    rationalRawScheme rationalTail (5 : ℚ) (Shamir.authorized_univ rationalParams)

end CslibTests
