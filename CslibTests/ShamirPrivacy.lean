import Cslib
import Mathlib.Algebra.Field.ZMod

namespace CslibTests

open Cslib
open Cslib.Crypto.Protocols.SecretSharing

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

def privacyParams : Shamir.Params (ZMod 5) (Fin 3) where
  threshold := 1
  threshold_lt_card := by decide
  point
    | 0 => 1
    | 1 => 2
    | 2 => 3
  point_injective := by decide
  point_nonzero i := by
    fin_cases i <;> decide

def zeroTail : Shamir.Randomness privacyParams := fun _ => 0

noncomputable def insecureRawScheme :
    Scheme (ZMod 5) (Shamir.Randomness privacyParams) (Fin 3) (ZMod 5) :=
  Shamir.Internal.rawSchemeWith privacyParams (PMF.pure zeroTail)

def singletonCoalition : Finset (Fin 3) := {0}

example : ¬ Shamir.authorized privacyParams singletonCoalition := by
  simp [singletonCoalition, Shamir.authorized, privacyParams]

example :
    insecureRawScheme.view singletonCoalition zeroTail (0 : ZMod 5) ≠
      insecureRawScheme.view singletonCoalition zeroTail (3 : ZMod 5) := by
  intro h
  have h0 := congrFun h ⟨0, by simp [singletonCoalition]⟩
  have h0' : (3 : ZMod 5) = 0 := by
    simpa [insecureRawScheme, singletonCoalition, Shamir.Internal.tailPolynomial,
      Shamir.Internal.sharingPolynomial_eval, privacyParams] using h0
  exact (by decide : (3 : ZMod 5) ≠ 0) h0'

example :
    (Shamir.scheme privacyParams).viewDist singletonCoalition (0 : ZMod 5) =
      (Shamir.scheme privacyParams).viewDist singletonCoalition (3 : ZMod 5) := by
  have hs : ¬ (Shamir.scheme privacyParams).authorized singletonCoalition := by
    simp [Shamir.scheme_authorized_iff, singletonCoalition, privacyParams]
  exact Shamir.viewIndist (F := ZMod 5) privacyParams
    singletonCoalition hs 0 3

example (v : singletonCoalition → ZMod 5)
    (hv : v ∈ ((PMF.uniformOfFintype (ZMod 5)).bind
      ((Shamir.scheme privacyParams).viewDist singletonCoalition)).support) :
    (Shamir.scheme privacyParams).posteriorSecretDist
        singletonCoalition
        (PMF.uniformOfFintype (ZMod 5))
        v
        hv =
      PMF.uniformOfFintype (ZMod 5) := by
  have hs : ¬ (Shamir.scheme privacyParams).authorized singletonCoalition := by
    simp [Shamir.scheme_authorized_iff, singletonCoalition, privacyParams]
  exact Shamir.perfectlyPrivate (F := ZMod 5) privacyParams
    singletonCoalition hs
    (PMF.uniformOfFintype (ZMod 5)) v hv

end CslibTests
