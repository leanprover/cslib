import Cslib.Foundations.Semantics.LTS.Basic
import Cslib.Logics.HennessyMilnerLogic.Basic

namespace Cslib
open HennessyMilner

universe u v

structure HMLGame where
  Label : Type v
  Process : Type u
  S : LTS Process Label
  G : Process × Formula Label
  -- This is the problematic line adapted
  G_d : {(p, φ) : Process × Formula Label | φ = Formula.modal _ _ }
