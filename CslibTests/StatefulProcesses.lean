/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Languages.StatefulProcesses.Network
import Cslib.Languages.Mech.Choreography.Basic

namespace CslibTests.Heterogeneous

open Cslib.Mech Cslib.StatefulProcesses

inductive Name | number | flag | message deriving DecidableEq

abbrev signature : LocalSig where
  VarName := Name
  VarType
    | .number => Nat
    | .flag => Bool
    | .message => String

-- The network signature in which every participant has the local signature `signature`.
abbrev sig : Sig Bool := fun _ => signature

def number : signature.Var Nat := ⟨.number, rfl⟩
def flag : signature.Var Bool := ⟨.flag, rfl⟩
def message : signature.Var String := ⟨.message, rfl⟩

def initial : signature.Store
  | .number => 4
  | .flag => true
  | .message => "hello"

-- A total store holds values of different types.
example : initial[number] = 4 ∧ initial[flag] = true ∧ initial[message] = "hello" :=
  ⟨rfl, rfl, rfl⟩

example : initial[number := 9][number] = 9 := by simp
example : initial[number := 9][flag] = true := rfl

-- Braces embed Lean terms, with `$` referring to participant-local variables.
example : (`(SP|number ≔ {Nat.succ 4}; 0) : Process Bool signature PEmpty PEmpty) =
    `(SP|number ≔ (fun _ : PUnit => Nat.succ 4) <$> .val PUnit.unit; 0) := rfl

example : (`(SP|number ≔ {$number + 1}; 0) : Process Bool signature PEmpty PEmpty) =
    `(SP|number ≔ (fun n : Nat => n + 1) <$> number; 0) := rfl

example : (`(SP|number ≔ {$number + $number}; 0) : Process Bool signature PEmpty PEmpty) =
    `(SP|number ≔ Nat.add <$> number <*> number; 0) := rfl

example (offset : Nat) :
    (`(SP|number ≔ {(fun n : Nat => n + $number) offset}; 0) :
      Process Bool signature PEmpty PEmpty) =
    `(SP|number ≔ (fun n : Nat => (fun z : Nat => z + n) offset) <$> number; 0) := rfl

example : (`(SP|number ≔ {$number ^ 2}; 0) : Process Bool signature PEmpty PEmpty) =
    `(SP|number ≔ (fun n : Nat => n ^ 2) <$> number; 0) := rfl

-- Ordinary Lean binders remain usable when they do not shadow a `$` handle.
example : (`(SP|number ≔ {(let k : Nat := 2; k + $number)}; 0) :
    Process Bool signature PEmpty PEmpty) =
    `(SP|number ≔ (fun n : Nat => (let k : Nat := 2; k + n)) <$> number; 0) := rfl

-- The same notation works for prefixes and for heterogeneous reads.
example : (`(SPpre|number ≔ {$number + 1}) : Prefix Bool signature PEmpty) =
    `(SPpre|number ≔ (fun n : Nat => n + 1) <$> number) := rfl

example : (`(SP|message ≔ {if $flag then $message else "no"}; 0) :
    Process Bool signature PEmpty PEmpty) =
    `(SP|message ≔
      (fun (b : Bool) (s : String) => if b then s else "no") <$> flag <*> message; 0) := rfl

-- Generated binders do not capture same-named Lean identifiers.
example (localValue : Nat) :
    (`(SP|number ≔ {$number + localValue}; 0) : Process Bool signature PEmpty PEmpty) =
    `(SP|number ≔ (fun n : Nat => n + localValue) <$> number; 0) := rfl

-- Antiquotations in a nested Lean syntax quotation are not local-store reads.
example (stx : Lean.TSyntax `term) : Process Bool signature PEmpty PEmpty :=
  `(SP|number ≔ {(fun (_ : Lean.MacroM (Lean.TSyntax `term)) => 1) `(term| $stx)}; 0)

-- Reads may occur in ordinary Lean conditionals.
example : (`(SP|number ≔ {if $flag then $number else 0}; 0) :
    Process Bool signature PEmpty PEmpty) =
    `(SP|number ≔ (fun (b : Bool) (n : Nat) => if b then n else 0) <$> flag <*> number; 0) := rfl

-- `$` reads the sender's local state in a communication.
def bracedExchange : Cfg Bool sig PEmpty PEmpty where
  net := fun p => if p then `(SP|false ! {$number + 1}; 0) else `(SP|true ? number; 0)
  store := fun p => if p then initial else initial[number := 2]

example : (Cfg.lts (S := sig) (SelLabel := PEmpty) (ProcName := PEmpty)).Tr
    bracedExchange (.com true false 5) ⟨0, bracedExchange.store[⟨false, number⟩ := 5]⟩ := by
  apply Cfg.Tr.com (S := sig) (e := (fun n : Nat => n + 1) <$> number)
    (x := number) (hstore := rfl)
  · apply Network.Tr.com (by constructor) (by constructor)
    ext p
    cases p <;> rfl
  · exact .call (.var _) rfl

-- Braced conditions use the same expression semantics.
example : (`(SP| if {$flag} then 0 else 0) : Process Bool signature PEmpty PEmpty) =
    (Process.cond ((fun b : Bool => b) <$> flag) 0 0 :
      Process Bool signature PEmpty PEmpty) := rfl

def bracedConditional : Cfg Bool sig PEmpty PEmpty where
  net := fun _ => `(SP| if {$flag} then 0 else 0)
  store := fun _ => initial

example : (Cfg.lts (S := sig) (SelLabel := PEmpty) (ProcName := PEmpty)).Tr
    bracedConditional (.local true)
    ⟨Function.update bracedConditional.net true 0, bracedConditional.store⟩ := by
  apply Cfg.Tr.condThen (S := sig) (cfg := bracedConditional)
    (cfg' := ⟨Function.update bracedConditional.net true 0, bracedConditional.store⟩)
    (e := (fun b : Bool => b) <$> flag) (hstore := rfl)
  · exact Network.Tr.local rfl .condThen rfl
  · exact .call (.var _) rfl

-- Reject ambiguous references rather than accidentally capturing an inner binder.
/-- error: a `$` variable also occurs as a plain identifier in this expression; rename the Lean identifier to avoid capturing a local binder -/
#guard_msgs in
example : Process Bool signature PEmpty PEmpty :=
  `(SP|number ≔ {(fun number : signature.Var Nat => $number) number}; 0)

-- A `$` read must refer to a variable with a compatible value type.
/-- error: failed to synthesize instance of type class
  HAdd flag.Type ℕ ℕ

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command. -/
#guard_msgs in
example : Process Bool signature PEmpty PEmpty := `(SP|number ≔ {$flag + 1}; 0)

-- An assignment cannot put a Boolean into a numeric variable.
/-- error: Application type mismatch: The argument
  true
has type
  Bool
but is expected to have type
  ℕ
in the application
  LocalSig.Expr.val true -/
#guard_msgs in
example : Process Unit signature PEmpty PEmpty := `(SP|number ≔ .val true; 0)

-- Local expressions can also be written outside processes.
example : (`(MechExpr| {$number + 1}) : signature.Expr Nat) =
    ((fun n : Nat => n + 1) <$> number : signature.Expr Nat) := rfl

-- A guard can be a plain expression term.
example : (`(SP| if LocalSig.Expr.var flag then 0 else 0) : Process Bool signature PEmpty PEmpty) =
    Process.cond (LocalSig.Expr.var flag) 0 0 := rfl

-- A `$` read outside a braced computation that spans the whole expression is rejected.
/-- error: `$` reads are only allowed in a braced computation `{…}` that spans the whole expression -/
#guard_msgs in
example : Process Bool signature PEmpty PEmpty := `(SP|number ≔ {$number} + 1; 0)

-- The FFI rejects an incompatible local variable at elaboration time.
/-- error: Application type mismatch: The argument
  flag
has type
  signature.Var Bool
but is expected to have type
  signature.Var ℕ
in the application
  LocalSig.Expr.var flag -/
#guard_msgs in
example : signature.Expr Nat := (fun n : Nat => n + 1) <$> .var flag

-- A symbolic communication also requires matching sender and receiver types.
/-- error: Application type mismatch: The argument
  number
has type
  signature.Var ℕ
but is expected to have type
  sig.Var false Bool
in the application
  Network.TrLabel.com true (LocalSig.Expr.val true) false number -/
#guard_msgs in
example : Network.TrLabel Bool sig PEmpty :=
  .com true (.val true) false number

-- Communication evaluates at the sender and writes at the receiver.
def exchange : Cfg Bool sig PEmpty PEmpty where
  net := fun p => if p then `(SP|false ! LocalSig.Expr.var number; 0) else `(SP|true ? number; 0)
  store := fun p => if p then initial else initial[number := 2]

example : (Cfg.lts (S := sig) (SelLabel := PEmpty) (ProcName := PEmpty)).Tr
    exchange (.com true false 4)
    ⟨0, exchange.store[⟨false, number⟩ := 4]⟩ := by
  -- The concrete rules can be applied by naming the configuration.
  apply Cfg.Tr.com (cfg := exchange) (e := LocalSig.Expr.var number) (x := number) (hstore := rfl)
  · apply Network.Tr.com (by constructor) (by constructor)
    ext p
    cases p <;> rfl
  · exact .var _

-- An assignment of a Lean function call.
def incrementCfg : Cfg Bool sig PEmpty PEmpty where
  net := fun _ => `(SP|number ≔ (fun n : Nat => n + 1) <$> number; 0)
  store := fun _ => initial

example : (Cfg.lts (S := sig) (SelLabel := PEmpty) (ProcName := PEmpty)).Tr
    incrementCfg (.local true) ⟨Function.update incrementCfg.net true 0,
      incrementCfg.store[⟨true, number⟩ := 5]⟩ := by
  apply Cfg.Tr.assign (cfg := incrementCfg) (e := (fun n : Nat => n + 1) <$> number)
    (x := number) (v := 5) (hstore := rfl)
  · exact Network.Tr.local rfl .pre rfl
  · exact .call (.var _) rfl

-- The other participant's local store is preserved.
example : (exchange.store[⟨false, number⟩ := 4] true)[number] = 4 := rfl

-- Local stores are read with `σ[x]` and written with `σ[x := v]`; the operations `Store.read` and
-- `Store.write` are rewritten to the notation.
example : initial.read number = initial[number] := by simp

example : initial.write number 7 = initial[number := 7] := by simp

example : initial[number := 7][number] = 7 := by simp

-- Global stores are written with `gs[⟨p, x⟩ := v]`; `Sig.Store.write` is rewritten to it.
example (gs : sig.Store) : gs.write false number 7 = gs[⟨false, number⟩ := 7] := by simp

example : (exchange.store[⟨false, number⟩ := 7] false)[number] = 7 := by simp

example : exchange.store[⟨false, number⟩ := 7] true = exchange.store true :=
  Sig.Store.subst_apply_of_ne _ _ _ _ _ (by decide)

-- Independent writes may have different value types.
example (σ : signature.Store) : σ[number := 7][flag] = σ[flag] :=
  LocalSig.Store.getElem_subst_of_ne _ _ _ _ (by decide)

example (σ : signature.Store) : σ[number := 1][number := 2] = σ[number := 2] := by simp

example (σ : signature.Store) : σ[number := 1][flag := false] = σ[flag := false][number := 1] :=
  LocalSig.Store.subst_comm _ _ _ _ _ (by decide)

example (gs : sig.Store) :
    gs[⟨true, number⟩ := 1][⟨false, flag⟩ := false] =
      gs[⟨false, flag⟩ := false][⟨true, number⟩ := 1] :=
  Sig.Store.subst_comm_of_ne _ _ _ _ _ _ _ (by decide)

example (gs : sig.Store) :
    gs[⟨true, number⟩ := 1][⟨true, flag⟩ := false] =
      gs[⟨true, flag⟩ := false][⟨true, number⟩ := 1] :=
  Sig.Store.subst_comm_of_name_ne _ _ _ _ _ _ (by decide)

-- Lean functions infer their argument types, including for heterogeneous local reads.
def describeFFI : signature.Expr String :=
  (fun (n : Nat) (b : Bool) (s : String) => if b then s ++ toString n else s) <$>
    number <*> flag <*> message

example : describeFFI.Eval initial "hello4" :=
  .call (.pair (.call (.pair (.call (.var _) rfl) (.var _)) rfl) (.var _)) rfl

example : LocalSig.Expr.Eval initial (Nat.add <$> number <*> number) 8 :=
  .call (.pair (.call (.var _) rfl) (.var _)) rfl

-- Lean functions may close over ordinary Lean parameters.
example (offset : Nat) :
    LocalSig.Expr.Eval initial (.map (fun n => n + offset) (.var number)) (4 + offset) :=
  .call (.var _) rfl

-- Ordinary Lean names retain lexical scope, even when they shadow a variable handle.
example (number : Nat) :
    LocalSig.Expr.Eval initial
      ((fun n : Nat => n + number) <$> .var CslibTests.Heterogeneous.number) (4 + number) :=
  .call (.var _) rfl

-- Multiple heterogeneous reads can be passed to an ordinary Lean function as a pair.
def describeExpr : signature.Expr String :=
  .map (fun (data : (Nat × Bool) × String) =>
    if data.1.2 then data.2 ++ toString data.1.1 else data.2)
    (.pair (.pair (.var number) (.var flag)) (.var message))

example : describeExpr.Eval initial "hello4" :=
  .call (.pair (.pair (.var _) (.var _)) (.var _)) rfl

/-! Relational calls: a call may evaluate to any result related to the value of its argument. -/

-- The current number or its successor.
def choice : signature.Expr Nat := .call (fun n m => m = n ∨ m = n + 1) (.var number)

example : choice.Eval initial 4 := .call (.var _) (Or.inl rfl)
example : choice.Eval initial 5 := .call (.var _) (Or.inr rfl)

example : ¬ choice.Eval initial 6 := by
  rw [choice, LocalSig.Expr.Eval.call_iff]
  rintro ⟨a, ha, h⟩
  rw [LocalSig.Expr.Eval.var_iff] at ha
  subst ha
  change 6 = 4 ∨ 6 = 4 + 1 at h
  omega

-- The same expression is accepted by both stateful processes and choreographies.
example : Cslib.Languages.Mech.Choreography Bool sig PEmpty PEmpty :=
  .pre (.assign true number choice) 0

example : Process Bool signature PEmpty PEmpty := `(SP|number ≔ choice; 0)

-- Lean functions can consume nondeterministic results.
def plusThree : signature.Expr Nat := .map (fun n => n + 3) choice

example : plusThree.Eval initial 7 := .call (.call (.var _) (Or.inl rfl)) rfl
example : plusThree.Eval initial 8 := .call (.call (.var _) (Or.inr rfl)) rfl

example : LocalSig.Expr.Eval initial ((fun n : Nat => n + 3) <$> choice) 8 :=
  .call (.call (.var _) (Or.inr rfl)) rfl

-- Both components of a pair can make independent nondeterministic choices.
example : LocalSig.Expr.Eval initial (.pair choice choice) (4, 5) :=
  .pair (.call (.var _) (Or.inl rfl)) (.call (.var _) (Or.inr rfl))

-- Calls compose, and each occurrence may make its own nondeterministic choice.
example : LocalSig.Expr.Eval initial (.call (fun n m => m = n ∨ m = n + 1) choice) 6 :=
  .call (.call (.var _) (Or.inr rfl)) (Or.inr rfl)

def choiceCfg : Cfg Bool sig PEmpty PEmpty where
  net := fun _ => `(SP|number ≔ choice; 0)
  store := fun _ => initial

example : (Cfg.lts (S := sig) (SelLabel := PEmpty) (ProcName := PEmpty)).Tr
    choiceCfg (.local true) ⟨Function.update choiceCfg.net true 0,
      choiceCfg.store[⟨true, number⟩ := 4]⟩ := by
  apply Cfg.Tr.assign (S := sig) (e := choice) (x := number) (v := 4) (hstore := rfl)
  · exact Network.Tr.local rfl .pre rfl
  · exact .call (.var _) (Or.inl rfl)

example : (Cfg.lts (S := sig) (SelLabel := PEmpty) (ProcName := PEmpty)).Tr
    choiceCfg (.local true) ⟨Function.update choiceCfg.net true 0,
      choiceCfg.store[⟨true, number⟩ := 5]⟩ := by
  apply Cfg.Tr.assign (S := sig) (e := choice) (x := number) (v := 5) (hstore := rfl)
  · exact Network.Tr.local rfl .pre rfl
  · exact .call (.var _) (Or.inr rfl)

-- A Lean function applied to a nondeterministic result.
def mixedCfg : Cfg Bool sig PEmpty PEmpty where
  net := fun _ => `(SP|number ≔ (fun n : Nat => n + 3) <$> choice; 0)
  store := fun _ => initial

example : (Cfg.lts (S := sig) (SelLabel := PEmpty) (ProcName := PEmpty)).Tr
    mixedCfg (.local true) ⟨Function.update mixedCfg.net true 0,
      mixedCfg.store[⟨true, number⟩ := 8]⟩ := by
  apply Cfg.Tr.assign (S := sig) (e := (fun n : Nat => n + 3) <$> choice)
    (x := number) (v := 8) (hstore := rfl)
  · exact Network.Tr.local rfl .pre rfl
  · exact .call (.call (.var _) (Or.inr rfl)) rfl

-- Communication evaluates relational calls like assignment.
def choiceExchange : Cfg Bool sig PEmpty PEmpty where
  net := fun p => if p then `(SP|false ! choice; 0) else `(SP|true ? number; 0)
  store := fun _ => initial

example : (Cfg.lts (S := sig) (SelLabel := PEmpty) (ProcName := PEmpty)).Tr
    choiceExchange (.com true false 5) ⟨0, choiceExchange.store[⟨false, number⟩ := 5]⟩ := by
  apply Cfg.Tr.com (S := sig) (e := choice) (x := number) (hstore := rfl)
  · apply Network.Tr.com (by constructor) (by constructor)
    ext p
    cases p <;> rfl
  · exact .call (.var _) (Or.inr rfl)

/-! Read sets: the variables read by an expression are computable. -/

example : choice.vars = {Name.number} := rfl

example : describeExpr.vars = {Name.number, Name.flag, Name.message} := by decide

example : (`(MechExpr| {if $flag then $number else 0}) : signature.Expr Nat).vars =
    {Name.flag, Name.number} := by decide

-- An expression has the same values in stores that agree on the variables it reads.
example : ((LocalSig.Expr.var number).map (· + 1)).Eval initial[flag := false] 5 := by
  have h : ((LocalSig.Expr.var number).map (· + 1)).Eval initial 5 := .call (.var number) rfl
  refine (LocalSig.Expr.Eval.congr fun x hx => ?_).mp h
  simp only [LocalSig.Expr.vars_map, LocalSig.Expr.vars_var, Finset.mem_singleton] at hx
  exact (LocalSig.Store.getElem_subst_of_ne _ _ _ _ (by rw [hx]; decide)).symm

-- Boolean guards continue to use the symbolic and concrete transition layers.
def conditional : Cfg Bool sig PEmpty PEmpty where
  net := fun _ => Process.cond (.var flag) 0 0
  store := fun _ => initial

example : (Cfg.lts (S := sig) (SelLabel := PEmpty) (ProcName := PEmpty)).Tr
    conditional (.local true) ⟨Function.update conditional.net true 0, conditional.store⟩ := by
  apply Cfg.Tr.condThen (S := sig) (cfg := conditional)
    (cfg' := ⟨Function.update conditional.net true 0, conditional.store⟩)
    (e := LocalSig.Expr.var flag) (hstore := rfl)
  · exact Network.Tr.local rfl .condThen rfl
  · exact .var _

-- A relational guard can enable both branches of a conditional.
def coin : signature.Expr Bool := .call (fun (_ : Unit) (_ : Bool) => True) (.val ())

def coinCfg : Cfg Bool sig PEmpty PEmpty where
  net := fun _ => Process.cond coin 0 0
  store := fun _ => initial

example : (Cfg.lts (S := sig) (SelLabel := PEmpty) (ProcName := PEmpty)).Tr
    coinCfg (.local true) ⟨Function.update coinCfg.net true 0, coinCfg.store⟩ := by
  apply Cfg.Tr.condThen (cfg := coinCfg)
    (cfg' := ⟨Function.update coinCfg.net true 0, coinCfg.store⟩) (hstore := rfl)
  · exact Network.Tr.local rfl .condThen rfl
  · exact .call (.val _) trivial

example : (Cfg.lts (S := sig) (SelLabel := PEmpty) (ProcName := PEmpty)).Tr
    coinCfg (.local true) ⟨Function.update coinCfg.net true 0, coinCfg.store⟩ := by
  apply Cfg.Tr.condElse (cfg := coinCfg) (v := false)
    (cfg' := ⟨Function.update coinCfg.net true 0, coinCfg.store⟩) (hne := by simp) (hstore := rfl)
  · exact Network.Tr.local rfl .condElse rfl
  · exact .call (.val _) trivial

-- Selection remains independent of local value types.
def selection : Network Bool sig Bool PEmpty := fun p =>
  if p then Process.pre (.sendLabel false true) 0
  else Process.recvLabel true [(true, 0)]

example : (Network.lts (S := sig) (SelLabel := Bool) (ProcName := PEmpty)).Tr
    selection (.sel true false true) 0 := by
  apply Network.Tr.sel (prP := 0) (prQ := 0) (by constructor) (by
    apply Process.Tr.recvLabel
    simp)
  ext p
  cases p <;> rfl

-- A guard may be a proposition: the first branch is taken when it evaluates to `True`, and the
-- second branch whenever it evaluates to anything else.
def propGuard (bound : Nat) : Cfg Bool sig PEmpty PEmpty where
  net := fun _ => `(SP| if {$number < bound} then 0 else 0)
  store := fun _ => initial

example : (Cfg.lts (S := sig) (SelLabel := PEmpty) (ProcName := PEmpty)).Tr
    (propGuard 5) (.local true)
    ⟨Function.update (propGuard 5).net true 0, (propGuard 5).store⟩ := by
  apply Cfg.Tr.condThen (cfg := propGuard 5)
    (cfg' := ⟨Function.update (propGuard 5).net true 0, (propGuard 5).store⟩) (hstore := rfl)
  · exact Network.Tr.local rfl .condThen rfl
  · exact .call (.var _) (by
      simp only [propGuard, Cslib.HasTrue.true_prop]
      exact (eq_true (by decide)).symm)

example : (Cfg.lts (S := sig) (SelLabel := PEmpty) (ProcName := PEmpty)).Tr
    (propGuard 3) (.local true)
    ⟨Function.update (propGuard 3).net true 0, (propGuard 3).store⟩ := by
  apply Cfg.Tr.condElse (cfg := propGuard 3) (v := (4 < 3)) (hne := by simp)
    (cfg' := ⟨Function.update (propGuard 3).net true 0, (propGuard 3).store⟩) (hstore := rfl)
  · exact Network.Tr.local rfl .condElse rfl
  · exact .call (.var _) rfl

-- A guard never blocks both branches: any value other than the true value enables the second.
example {α : Type} [Cslib.HasTrue α] (pr₁ pr₂ : Process Bool signature PEmpty PEmpty) (v : α)
    (hv : v ≠ Cslib.HasTrue.true) :
    (Cfg.lts (S := sig) (SelLabel := PEmpty) (ProcName := PEmpty)).Tr
      ⟨fun _ => .cond (.val v) pr₁ pr₂, fun _ => initial⟩ (.local true)
      ⟨Function.update (fun _ : Bool => .cond (.val v) pr₁ pr₂) true pr₂, fun _ => initial⟩ :=
  Cfg.Tr.condElse (Network.Tr.local rfl .condElse rfl) (.val v) hv rfl

-- Conditionals are matched by naming their guard instance.
def countConds : Process Bool signature PEmpty PEmpty → Nat
  | .cond (inst := _) _ pr₁ pr₂ => countConds pr₁ + countConds pr₂ + 1
  | .pre _ pr => countConds pr
  | _ => 0

example : countConds `(SP| if {$number < 3} then if {$flag} then 0 else 0 else 0) = 2 := rfl

end CslibTests.Heterogeneous

namespace CslibTests.PerParticipant

open Cslib.Mech Cslib.StatefulProcesses

/-! Participants have their own local signatures: the same variable name may have different types
at different participants. -/

inductive Name | x deriving DecidableEq

-- Alice's `x` is a number and Bob's `x` is a string.
abbrev aliceSig : LocalSig where
  VarName := Name
  VarType _ := Nat

abbrev bobSig : LocalSig where
  VarName := Name
  VarType _ := String

abbrev sig : Sig Bool
  | true => aliceSig
  | false => bobSig

def aliceX : sig.Var true Nat := ⟨.x, rfl⟩
def bobX : sig.Var false String := ⟨.x, rfl⟩

example : aliceX.name = bobX.name := rfl

-- Alice sends a string computed from her number to Bob.
def greeting : Cfg Bool sig PEmpty PEmpty where
  net
    | true => `(SP| false ! {toString ($aliceX + 1)}; 0)
    | false => `(SP| true ? bobX; 0)
  store
    | true, .x => (41 : Nat)
    | false, .x => ""

example : (Cfg.lts (S := sig) (SelLabel := PEmpty) (ProcName := PEmpty)).Tr
    greeting (.com true false "42") ⟨0, greeting.store[⟨false, bobX⟩ := "42"]⟩ := by
  apply Cfg.Tr.com (e := `(MechExpr| {toString ($aliceX + 1)})) (x := bobX) (hstore := rfl)
  · apply Network.Tr.com (by constructor) (by constructor)
    funext p
    cases p <;> rfl
  · exact .call (.var _) rfl

example : (greeting.store[⟨false, bobX⟩ := "42"] false)[bobX] = "42" := by simp

-- A communication requires the receiver's variable to have the type of the sent value.
/-- error: Application type mismatch: The argument
  bobX
has type
  sig.Var false String
but is expected to have type
  sig.Var false ℕ
in the application
  Network.TrLabel.com true (LocalSig.Expr.var aliceX) false bobX -/
#guard_msgs in
example : Network.TrLabel Bool sig PEmpty := .com true (.var aliceX) false bobX

end CslibTests.PerParticipant

namespace CslibTests.Universes

open Cslib.Mech Cslib.StatefulProcesses

/-! Signatures are universe polymorphic in names and values. -/

-- Names in `Type 1`.
inductive Name : Type 1 | type | flag | count deriving DecidableEq

-- Values in `Type 1`: a store can hold types. The universes of the signature are inferred.
abbrev signature : LocalSig where
  VarName := Name
  VarType
    | .type => Type
    | .flag => ULift Bool
    | .count => ULift Nat

example : signature = LocalSig.mk.{1, 1} signature.VarName signature.VarType := rfl

abbrev sig : Sig Bool := fun _ => signature

def type : signature.Var Type := ⟨.type, rfl⟩
def flag : signature.Var (ULift Bool) := ⟨.flag, rfl⟩
def count : signature.Var (ULift Nat) := ⟨.count, rfl⟩

def initial : signature.Store
  | .type => Nat
  | .flag => ⟨true⟩
  | .count => ⟨0⟩

-- Nullary Lean calls take the unit of the value universe.
example : LocalSig.Expr.Eval initial (`(MechExpr| {ULift.up 3})) ⟨3⟩ :=
  .call (.val _) rfl

-- The guard type of a braced guard is the type of its body; outside `Type` it can be a lift such
-- as `ULift Bool`.
example : (`(SP| if {$flag} then 0 else 0) : Process Bool signature PEmpty PEmpty) =
    (Process.cond ((fun b : ULift Bool => b) <$> flag) 0 0 :
      Process Bool signature PEmpty PEmpty) := rfl

def guarded : Cfg Bool sig PEmpty PEmpty where
  net := fun _ => `(SP| if {$flag} then 0 else 0)
  store := fun _ => initial

example : (Cfg.lts (S := sig) (SelLabel := PEmpty) (ProcName := PEmpty)).Tr
    guarded (.local true) ⟨Function.update guarded.net true 0, guarded.store⟩ := by
  apply Cfg.Tr.condThen (cfg := guarded)
    (cfg' := ⟨Function.update guarded.net true 0, guarded.store⟩) (hstore := rfl)
  · exact Network.Tr.local rfl .condThen rfl
  · exact .call (.var _) rfl

-- Communicated values may be types, which the observable label records.
def typeExchange : Cfg Bool sig PEmpty PEmpty where
  net := fun p => if p then `(SP| false ! {$type × $type}; 0) else `(SP| true ? type; 0)
  store := fun _ => initial

example : (Cfg.lts (S := sig) (SelLabel := PEmpty) (ProcName := PEmpty)).Tr
    typeExchange (.com true false (Nat × Nat))
    ⟨0, typeExchange.store[⟨false, type⟩ := (Nat × Nat)]⟩ := by
  apply Cfg.Tr.com (S := sig)
    (e := (fun (a b : Type) => a × b) <$> type <*> type) (x := type)
    (hstore := rfl)
  · apply Network.Tr.com (by constructor) (by constructor)
    ext p
    cases p <;> rfl
  · exact .call (.pair (.call (.var _) rfl) (.var _)) rfl

-- Choreographies use the same signatures and guards.
example : Cslib.Languages.Mech.Choreography Bool sig PEmpty PEmpty :=
  .cond true (.var flag) (.pre (.com true (.var type) false type) 0) 0

-- Stores can hold types.
example : initial[type] = Nat := rfl

-- Protocols can be written generically over all universes of the signature.
example {Pid : Type*} {L : LocalSig.{u, v}} (p : Pid) (x : L.Var (ULift Bool))
    (y : L.Var (ULift Bool)) : Process Pid L PEmpty PEmpty :=
  `(SP| p ? x; y ≔ {$x}; if {$y} then 0 else 0)

/-! Lean functions may be polymorphic. -/

inductive SmallName | number | flag deriving DecidableEq

abbrev smallSignature : LocalSig where
  VarName := SmallName
  VarType
    | .number => Nat
    | .flag => Bool

abbrev smallSig : Sig Bool := fun _ => smallSignature

def number : smallSignature.Var Nat := ⟨.number, rfl⟩
def smallFlag : smallSignature.Var Bool := ⟨.flag, rfl⟩

def smallInitial : smallSignature.Store
  | .number => 3
  | .flag => true

example : LocalSig.Expr.Eval smallInitial (Prod.fst <$> .pair (.var number) (.var smallFlag)) 3 :=
  .call (.pair (.var _) (.var _)) rfl

-- Polymorphic Lean functions and guards combine in processes.
def incrementById : Process Bool smallSignature PEmpty PEmpty :=
  `(SP| number ≔ id <$> ((· + 1) <$> number); 0)

def smallCfg : Cfg Bool smallSig PEmpty PEmpty where
  net := fun _ => `(SP| if {$smallFlag} then number ≔ id <$> ((· + 1) <$> number); 0 else 0)
  store := fun _ => smallInitial

example : (Cfg.lts (S := smallSig) (SelLabel := PEmpty) (ProcName := PEmpty)).Tr smallCfg
    (.local true) ⟨Function.update smallCfg.net true incrementById, smallCfg.store⟩ := by
  apply Cfg.Tr.condThen (cfg := smallCfg)
    (cfg' := ⟨Function.update smallCfg.net true incrementById, smallCfg.store⟩) (hstore := rfl)
  · exact Network.Tr.local rfl .condThen rfl
  · exact .call (.var _) rfl

end CslibTests.Universes
