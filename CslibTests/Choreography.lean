/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Languages.Mech.Choreography.Basic

namespace CslibTests.Choreography

open Cslib.Mech Cslib.Languages.Mech

/-! Alice (`true`) and Bob (`false`) have separate local signatures. -/

inductive AliceName | number | flag deriving DecidableEq

inductive BobName | text deriving DecidableEq

abbrev aliceSig : LocalSig where
  VarName := AliceName
  VarType
    | .number => Nat
    | .flag => Bool

abbrev bobSig : LocalSig where
  VarName := BobName
  VarType _ := String

abbrev sig : Sig Bool
  | true => aliceSig
  | false => bobSig

def number : sig.Var true Nat := ⟨.number, rfl⟩
def flag : sig.Var true Bool := ⟨.flag, rfl⟩
def text : sig.Var false String := ⟨.text, rfl⟩

local notation "Chor" => Choreography Bool sig PEmpty PEmpty

-- Choreographies share the local-expression notation of Stateful Processes.
example : (`(Mech| true . number ≔ {$number + 1}; 0) : Chor) =
    .pre (.assign true number ((fun n : Nat => n + 1) <$> number)) 0 := rfl

-- A communication connects an expression of the sender with a variable of the receiver.
example : (`(Mech| true . {toString ($number * 2)} ⮕ false . text; 0) : Chor) =
    .pre (.com true ((fun n : Nat => toString (n * 2)) <$> number) false text) 0 := rfl

example : (`(Mech| if true . {$number < 3} then 0 else 0) : Chor) =
    .cond true ((fun n : Nat => n < 3) <$> number) 0 0 := rfl

-- Plain expression terms need no braces.
example : (`(Mech| true . LocalSig.Expr.val "hi" ⮕ false . text; 0) : Chor) =
    .pre (.com true (.val "hi") false text) 0 := rfl

example : (`(Mech| if true . LocalSig.Expr.var flag then 0 else 0) : Chor) =
    .cond true (.var flag) 0 0 := rfl

-- A participant can only assign its own variables.
/-- error: Application type mismatch: The argument
  text
has type
  sig.Var false String
but is expected to have type
  sig.Var true String
in the application
  Prefix.assign true text -/
#guard_msgs in
example : Prefix Bool sig PEmpty := .assign (α := String) true text (.val "hi")

end CslibTests.Choreography
