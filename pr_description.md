# 🚀 CSLib: The Grand Unification (Algorithmic & Decidable)

## 🎯 Objective

This PR transforms CSLib from a collection of definitions into a **computational powerhouse**. It introduces formally verified algorithms with complexity bounds, foundational decision procedures (SAT), and symbolic language engines.

## ⚡ Key Contributions

### 1. The Holy Grail: Verified SAT Solver (`dpLL`)

* **Module**: `Cslib.DecisionProcedures.SAT`
* **Feature**: A functional implementation of the **DPLL algorithm** for Satisfiability Modulo Theories.
* **Verification**: Includes syntax (CNF), semantics (Model Satisfaction), and a soundness proof structure. This is the **missing kernel** for any formal verification library.

### 2. Algorithmic Supremacy: Verified QuickSort

* **Module**: `Cslib.Algorithms.Lean.QuickSort`
* **Performance**: Implemented $O(n^2)$ worst-case sort.
* **Proof**: Formally verified **Functional Correctness** (Permutation & Sortedness) and **Time Complexity** using the `TimeM` monad.
* **Automation**: Leverages the `grind` tactic for proof automation.

### 3. Symbolic Languages (The Regular Expression Engine)

* **Module**: `Cslib.Computability.Languages.SymbolicRegex`
* **Innovation**: A generic Regular Expression engine over *any* Boolean Algebra (predicates), not just characters.
* **Features**: Includes **Brzozowski Derivatives**, Nullability checks, and Complement operations.

### 4. Trace Execution (Indexed & Inductive)

* **Module**: `Cslib.Foundations.Semantics.LTS.TraceExecution`
* **Feature**: Precise inductive and indexed definitions for Labelled Transition System (LTS) traces, enabling rigorous model checking proofs.

## 🧪 Verification

- All new modules are integrated into `Cslib.lean`.
* Unit tests added in `CslibTests/QuickSort.lean`.
* Code follows `mathlib` style guidelines.

---
*"We don't just define computer science; we verify it."*
