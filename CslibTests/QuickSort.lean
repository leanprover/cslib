import Cslib.Algorithms.Lean.QuickSort.QuickSort
import Cslib.Algorithms.Lean.TimeM

open Cslib.Algorithms.Lean.TimeM

def testQuickSort1 : Bool :=
  ⟪quickSort [3, 1, 4, 1, 5, 9, 2, 6]⟫ = [1, 1, 2, 3, 4, 5, 6, 9]

def testQuickSort2 : Bool :=
  ⟪quickSort [10, 9, 8, 7, 6, 5, 4, 3, 2, 1]⟫ = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

def testQuickSort3 : Bool :=
  ⟪quickSort ([] : List Nat)⟫ = []

def testQuickSort4 : Bool :=
  ⟪quickSort [1]⟫ = [1]

#eval testQuickSort1
#eval testQuickSort2
#eval testQuickSort3
#eval testQuickSort4

-- Basic complexity check (manual observation possible via #eval)
def checkComplexity (l : List Nat) : Nat := (quickSort l).time
#eval checkComplexity [3, 1, 2]
