/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
module

public import Cslib.Computability.Urm.Instr
public import Cslib.Computability.Urm.State
public import Cslib.Computability.Urm.Program
public import Cslib.Computability.Urm.Config
public import Cslib.Computability.Urm.Execution
public import Cslib.Computability.Urm.StraightLine
public import Cslib.Computability.Urm.StandardForm
public import Cslib.Computability.Urm.Computable

/-! # URM Basic Definitions - Hub File

This file re-exports all basic URM definitions for convenient imports.

## File Organization

The URM module is organized into the following files:

- `Instr.lean`: URM instruction type and operations
- `State.lean`: Register state operations
- `Program.lean`: URM programs and their properties
- `Config.lean`: Machine configuration
- `Execution.lean`: Step/Steps/Halts/eval definitions
- `StraightLine.lean`: Straight-line program execution theorems
- `StandardForm.lean`: Standard form program execution theorems
- `Computable.lean`: URM-computable functions

## Import Dependency Graph

```
Instr ─────────┐
               ├──→ Program ──┐
State ─────────┴──→ Config ───┴──→ Execution ──→ StraightLine ──→ StandardForm
                                       │
                                       └──→ Computable
```

## References

* [N.J. Cutland, *Computability: An Introduction to Recursive Function Theory*][Cutland1980]
* [J.C. Shepherdson and H.E. Sturgis,
  *Computability of Recursive Functions*][ShepherdsonSturgis1963]
-/
