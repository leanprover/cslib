import Cslib.Foundations.Semantics.LTS.TraceExecution


namespace CslibTests.TraceExecution

open Cslib.Foundations.Semantics.LTS

-- Define a simple 3-state LTS
-- States: 0, 1, 2. Labels: "a", "b"
inductive MyState | s0 | s1 | s2 deriving DecidableEq, Repr
inductive MyLabel | a | b deriving DecidableEq, Repr

inductive MyTrans : MyState → MyLabel → MyState → Prop
| s0_to_s1 : MyTrans .s0 .a .s1
| s1_to_s2 : MyTrans .s1 .b .s2

def myLTS : LTS MyState MyLabel := {
  Tr := MyTrans
}

-- Test 1: Valid Execution Inductive
-- s0 -a-> s1 -b-> s2
example : IsExecution myLTS .s0 [.a, .b] [.s1, .s2] .s2 := by
  apply IsExecution.step
  · exact MyTrans.s0_to_s1
  · apply IsExecution.step
    · exact MyTrans.s1_to_s2
    · apply IsExecution.refl

-- Test 2: Invalid Execution (Wrong label)
example : ¬ IsExecution myLTS .s0 [.b, .b] [.s1, .s2] .s2 := by
  intro h
  cases h with
  | step tr _ =>
    -- The first transition must be s0 -b-> ?
    -- MyTrans does not have a 'b' transition from s0
    cases tr

-- Test 3: Indexed Execution
-- s0 -a-> s1 -b-> s2
-- Indexed view:
-- μs = [a, b]
-- ss = [s1, s2]
-- i=0: from s0 to ss[0]=s1 via μs[0]=a. OK.
-- i=1: from ss[0]=s1 to ss[1]=s2 via μs[1]=b. OK.
example : IsExecution_Indexed myLTS .s0 [.a, .b] [.s1, .s2] .s2 := by
  unfold IsExecution_Indexed
  apply And.intro
  · rfl -- length check
  · apply And.intro
    · left; rfl -- end state check
    · intro i
      fin_cases i
      · -- i = 0
        simp
        -- Need to handle the 'let' bindings or simplify carefully
        -- logic: current = s0, next = s1, label = a
        -- This manual expansion might be tricky due to the 'let' with proof terms in the definition
        -- But for a specific case, reduction should work.
        exact MyTrans.s0_to_s1
      · -- i = 1
        simp
        exact MyTrans.s1_to_s2

end CslibTests.TraceExecution
