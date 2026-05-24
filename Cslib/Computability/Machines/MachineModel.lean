/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Mathlib.Data.Part
public import Cslib.Computability.Machines.SingleTapeTuring.Basic
public import Mathlib.Data.Nat.Bits
public import Mathlib.Tactic.DeriveFintype
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
public import Mathlib.Tactic.Sat.FromLRAT

@[expose] public section

open Cslib Relation

namespace Complexity

/-- A generic model of a machine that performs computations on a data type that is specific
to the machine type. -/
class MachineModel (Machine : Type*) where
  /-- The input and output data type of the machine. -/
  DataType : Type
  /-- A size measure for the data type. -/
  size : DataType → ℕ
  /-- Execute the machine `m` on input `x` and return the output, the consumed time
  and the consumed space (if it terminates). -/
  runEncoded (m : Machine) (x : DataType) : Part (DataType × ℕ × ℕ)

/-- This class specifies a way to encode arbitrary lean types into the internal type of the
machine. -/
class MachineEncodable (Machine : Type*) [MachineModel Machine] (α : Type) where
  encode : α → (MachineModel.DataType Machine)
  decode : (MachineModel.DataType Machine) → Option α
  encodeDecode : ∀ x, decode (encode x) = some x

namespace MachineModel

variable {Machine : Type*} [MachineModel Machine]
  {α β : Type} [MachineEncodable Machine α] [MachineEncodable Machine β]

/-- Run the machine `m` on `x` and return the output, the consumed time and the consumed space
(if it terminates).
Failure to decode the ouput is treated in the same way as non-termination.
This is a lifted version of `runEncoded` to work with encodable types. -/
def run (m : Machine) (x : α) : Part (β × ℕ × ℕ) := do
  (runEncoded m (MachineEncodable.encode x)).bind fun (out, time, space) =>
    match MachineEncodable.decode out with
    | some out' => Part.some (out', time, space)
    | none => Part.none

/-- The size of an encodable lean type in the internal data type. -/
def encodedSize (x : α) : ℕ := size (MachineEncodable.encode (Machine := Machine) x)

/-- The output of the machine `m` on input `input`, if it terminates. -/
def runOutput (m : Machine) (input : α) : Part β :=
    (run m input).map fun (out, _, _) => out

/-- The time consumption of the machine `m` on input `input`, if it terminates. -/
def runTime (m : Machine) (input : α) : Part ℕ :=
    (run (β := β) m input).map fun (_, time, _) => time

/-- The space consumption of the machine `m` on input `input`, if it terminates. -/
def runSpace (m : Machine) (input : α) : Part ℕ :=
    (run (β := β) m input).map fun (_, _, space) => space

/-- A machine `m` computes the function `f` using the encoding of the machine model. -/
def ComputesFunction (m : Machine) (f : α → β) : Prop :=
    ∀ x : α, runOutput m x = Part.some (f x)

/-- A machine `m` terminates in `O(t(n))` time on inputs of size `n`. -/
def RunsInOTime (m : Machine) (t : ℕ → ℕ) : Prop :=
    ∃ c₁ c₂ : ℕ, ∀ x : α, ∃ t' : ℕ,
      runTime (β := β) m x = Part.some t' ∧
      t' ≤ c₁ * (t (encodedSize (Machine := Machine) x)) + c₂

/-- The machine model can compute the function `f` in time `O(t)`. -/
def ComputableInOTime (f : α → β) (t : ℕ → ℕ) : Prop :=
    ∃ m : Machine, RunsInOTime (α := α) (β := β) m t ∧ ComputesFunction m f

/-- A machine `m` terminates using `O(s)` space. -/
def RunsInOSpace (m : Machine) (s : ℕ → ℕ) : Prop :=
    ∃ c₁ c₂ : ℕ, ∀ x : α, ∃ s' : ℕ,
      runSpace (β := β) m x = Part.some s' ∧
      s' ≤ c₁ * s (encodedSize (Machine := Machine) x) + c₂

/-- The machine model can compute the function `f` in space `O(s)`. -/
def ComputableInOSpace (f : α → β) (s : ℕ → ℕ) : Prop :=
    ∃ m : Machine, RunsInOSpace (α := α) (β := β) m s ∧ ComputesFunction m f

/-- The machine `m` is a universal machine in the machine model in the sense that it can
simulate all other machines of the same model.
TODO: We should require that we can always encode the tuple. -/
def UniversalMachine {Machine : Type} [MachineModel Machine]
    [MachineEncodable Machine Machine] (u : Machine) : Prop :=
  ∀ m : Machine, ∀ α β : Type, ∀ [MachineEncodable Machine α] [MachineEncodable Machine β],
  ∀ [MachineEncodable Machine (Machine × α)],
  ∀ x : α, runOutput (β := β) u (m, x) = runOutput m x

/- The next two definitions are important: If two machine models are linearly space-related
and polynomially time-related, it is generally agreed that they capture the same kind of
complexity theory.

For some computation models, this is true except for space bounds below linear - we could
have a special exception for those.

In order to make this consistent relative to encodings, we need to ensure that the encodings
do not blow up the input too much: -/

/-- The encodings of two machine models are linearly related in size for a type `α`. -/
def LinearlySizeRelatedEncodings (Machine₁ Machine₂ : Type) [MachineModel Machine₁] [MachineModel Machine₂]
  (α : Type) [MachineEncodable Machine₁ α] [MachineEncodable Machine₂ α] : Prop :=
  ∃ k, ∀ x : α,
      encodedSize (Machine := Machine₁) x ≤ k * encodedSize (Machine := Machine₂) x ∧
      encodedSize (Machine := Machine₂) x ≤ k * encodedSize (Machine := Machine₁) x


/-- Two machine models are linearly space-related, if all functions that are encodable in both
models are computable in the same space bound. -/
def LinearlySpaceRelated
  (Machine₁ Machine₂ : Type) [MachineModel Machine₁] [MachineModel Machine₂]
  (α β : Type)
  [MachineEncodable Machine₁ α] [MachineEncodable Machine₁ β]
  [MachineEncodable Machine₂ α] [MachineEncodable Machine₂ β] : Prop :=
  LinearlySizeRelatedEncodings Machine₁ Machine₂ α →
    LinearlySizeRelatedEncodings Machine₁ Machine₂ β →
    ∀ f : α → β, ∀ s,
      ComputableInOSpace (Machine := Machine₁) f s ↔ ComputableInOSpace (Machine := Machine₂) f s

/-- Two machine models are polynomially time-related if all functions that are encodable in both
models can be simulated with a polynomial overhead. -/
def PolynomiallyTimeRelated
  (Machine₁ Machine₂ : Type) [MachineModel Machine₁] [MachineModel Machine₂]
  (α β : Type)
  [MachineEncodable Machine₁ α] [MachineEncodable Machine₁ β]
  [MachineEncodable Machine₂ α] [MachineEncodable Machine₂ β] : Prop :=
  LinearlySizeRelatedEncodings Machine₁ Machine₂ α →
    LinearlySizeRelatedEncodings Machine₁ Machine₂ β →
    ∃ k₁ k₂,
    ∀ f : α → β, ∀ t,
      ComputableInOTime (Machine := Machine₁) f t →
        ComputableInOTime (Machine := Machine₂) f (fun n => (t n) ^ k₁) ∧
      ComputableInOTime (Machine := Machine₂) f t →
        ComputableInOTime (Machine := Machine₁) f (fun n => (t n) ^ k₂)

/-- The function `s` is space constructible if there is a machine that has `s(n)` as its
space consumption on any input of length `n`.
Note: Usually one supplies `1^n` as input, but there is no canonical way to do this here.
The point is that the input has size `n` and no other information apart from that, but we should
get the same result by requiring the (exact) same space consumption for all inputs of this size. -/
def SpaceConstructible (s : ℕ → ℕ) : Prop :=
  ∃ m : Machine, ∀ n, ∀ α, ∀ [MachineEncodable Machine α], ∀ x : α,
    encodedSize (Machine := Machine) (α := α) x = n → runSpace (β := β) m x = Part.some (s n)

/-- The function `t` is time constructible if there is a machine that has `t` as its time
consumption.
Note: Usually one supplies `1^n` as input, but there is no canonical way to do this here.
The point is that the input has size `n` and no other information apart from that, but we should
get the same result by requiring the (exact) same space consumption for all inputs of this size. -/
def TimeConstructible (t : ℕ → ℕ) : Prop :=
  ∃ m : Machine, ∀ n, ∀ α, ∀ [MachineEncodable Machine α], ∀ x : α,
    encodedSize (Machine := Machine) (α := α) x = n ∧ runTime (β := β) m x = Part.some (t n)


end MachineModel

/-
The rest if this file is just some examples that show how MachineModel is used.
-/

namespace SingleTapeTMMachineModel

/-
Example instances using single-tape Turing machines.
We use one machine model per alphabet. In complexity theory, most results are relative to some
alphabet with at least two elements and the alphabet is often omitted, so I think this is fine.
-/

open Turing.SingleTapeTM

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/-- If the Turing machine `tm` halts on input `input` after exactly `n` steps in a valid output
configuration, returns the output. Otherwise, returns `none`.
This translates the reachability-based definition of SingleTapeTM to a step-based one. -/
def outputAfterStep (tm : Turing.SingleTapeTM Symbol) (input : List Symbol) (n : ℕ) :
    Option (List Symbol) :=
  match (Option.bind · tm.step)^[n] (some (initCfg tm input)) with
  | some ⟨none, t⟩ =>
    if t.left.toList = [] then
      (t.head :: t.right.toList).reduceOption
    else
      none
  | _ => none

instance : MachineModel (Turing.SingleTapeTM Symbol) where
  DataType := List Symbol
  size := List.length
  runEncoded (tm : Turing.SingleTapeTM Symbol) (input : List Symbol) :=
    ⟨(∃ n, (outputAfterStep tm input n).isSome),
      fun h =>
        let n := Nat.find h
        let output := (outputAfterStep tm input n).get (Nat.find_spec h)
        (output, n, 0)⟩

/- Let us use an alphabet and define some encodings. -/

inductive Alph : Type
  | zero
  | one
  | left
  | right
  deriving Inhabited, Fintype

abbrev TM := Turing.SingleTapeTM Alph

def encodeBool : Bool → Alph
  | false => .zero
  | true  => .one

def decodeBool : Alph → Option Bool
  | .zero => some false
  | .one  => some true
  | _     => none

instance : MachineEncodable TM Bool where
  encode x := [encodeBool x]
  decode c := c.head?.bind decodeBool
  encodeDecode x := by cases x <;> rfl

instance : MachineEncodable TM ℕ where
  encode n := (Nat.bits n).map encodeBool
  decode s := sorry
  encodeDecode n := sorry

inductive Literal where
  | pos (i : ℕ)
  | neg (i : ℕ)

instance : MachineEncodable TM Literal where
  encode l := match l with
  | .pos i => Alph.zero :: (MachineEncodable.encode (Machine := TM) i)
  | .neg i => Alph.one :: (MachineEncodable.encode (Machine := TM) i)
  decode := sorry
  encodeDecode := sorry

variable {α β : Type} [MachineEncodable TM α]
  [MachineEncodable TM β]

instance : MachineEncodable TM (List α) where
  encode l :=
    Alph.left :: (l.map (MachineEncodable.encode (Machine := TM))).flatten
      ++ [Alph.right]
  decode := sorry
  encodeDecode := sorry

instance : MachineEncodable TM (α × β) where
  encode := fun (a, b) =>
    Alph.left :: MachineEncodable.encode (Machine := TM) a
      ++ Alph.right :: Alph.left
      :: MachineEncodable.encode (Machine := TM) b
      ++ [Alph.right]
  decode := sorry
  encodeDecode := sorry

/-- A list of positive-assigned variables satisfies a cnf -/
def satisfies (pos_vars : List ℕ) (cnf : List (List Literal)) : Bool :=
  cnf.all (fun c => c.any (fun l => match l with
    | .pos i => i ∈ pos_vars
    | .neg i => i ∉ pos_vars))

/-- A theorem that states that boolean formula evaluation (given in CNF) is in cubic time. -/
theorem formula_evaluation_in_p :
    MachineModel.ComputableInOTime (Machine := TM) (β := Bool)
      (fun (pos_vars, cnf) => satisfies pos_vars cnf) (fun n => n ^ 3) := sorry

end SingleTapeTMMachineModel

namespace LambdaCalculusMachineModel

/-
Now let us take a look at lambda calculus.
Disclaimer: I don't know much about lambda calculus.
The aspect to illustrate here is that the internal data type is not a list of symbols from a
finite alphabet. Still, there is a reasonable size measure and a computation notion that
happens directly on that type.
-/

open LambdaCalculus.LocallyNameless.Untyped

variable {Var : Type}

/-- The size of a lambda term.
Note: Not sure if that has been defined somewhere else. -/
def size : Term Var → ℕ
  | Term.bvar _ => 1
  | Term.fvar _ => 1
  | Term.abs t => 1 + size t
  | Term.app l r => 1 + size l + size r

/-- Performs a single leftmost-outermost β-reduction step.
Returns `some t'` if a redex was contracted, `none` if `t` is in β-normal form.
Note: I could not find a computable beta reduction in Cslib.
I also do not know if this here is correct. -/
def betaStep : Term Var → Option (Term Var)
  | Term.app (Term.abs M) N => some (Term.open' M N)
  | Term.app f a =>
      match betaStep f with
      | some f' => some (Term.app f' a)
      | none =>
        match betaStep a with
        | some a' => some (Term.app f a')
        | none => none
  | Term.abs M =>
      match betaStep M with
      | some M' => some (Term.abs M')
      | none => none
  | Term.bvar _ | Term.fvar _ => none

/-- Iterates `betaStep` for at most `fuel` steps. Returns `some (t', steps, maxSize)` where
`t'` is the β-normal form reached, `steps` is the number of β-reductions performed, and
`maxSize` is the maximum `size` of any intermediate term (including the starting term and the
normal form). Returns `none` if the normal form was not reached within `fuel` steps. -/
def reduceToNormal (fuel : ℕ) (term : Term Var) : Option (Term Var × ℕ × ℕ) :=
  match betaStep term with
  | none => some (term, 0, size term)
  | some t' =>
    match fuel with
    | 0 => none
    | n + 1 =>
      (reduceToNormal n t').map fun (r, k, m) => (r, k + 1, max (size term) m)

instance : MachineModel (Term Var) where
  DataType := Term Var
  size := size
  runEncoded m input :=
    let start := Term.app m input
    { Dom := ∃ n, (reduceToNormal n start).isSome
      get := fun h => (reduceToNormal (Nat.find h) start).get (Nat.find_spec h) }

end LambdaCalculusMachineModel

/-
I am working on another machine model where the internal representation is

inductive Data where
  | l : List Data → Data

and the computation is stated in a functional way that is not step-based, but has a clear
notion of "time consumed" and "space consumed", so this would be another reason to specify
the machine model in such an abstract way.

-/

end Complexity
