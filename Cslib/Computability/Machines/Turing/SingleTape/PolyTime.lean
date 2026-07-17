/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
import Cslib.Computability.Machines.Turing.SingleTape.PolyTime.Id
import Cslib.Computability.Machines.Turing.SingleTape.PolyTime.Comp
import Cslib.Computability.Machines.Turing.SingleTape.PolyTime.Basic
import Cslib.Computability.Machines.Turing.SingleTape.PolyTime.TapeHelpers
import Cslib.Computability.Machines.Turing.SingleTape.PolyTime.TakeFirstBlock
import Cslib.Computability.Machines.Turing.SingleTape.PolyTime.UndelimitBlock
import Cslib.Computability.Machines.Turing.SingleTape.PolyTime.TagBlock
import Cslib.Computability.Machines.Turing.SingleTape.PolyTime.Prod

/-!
# Polynomial-time computable functions between encoded types

This is the aggregator for the `PolyTime` development: the predicate `IsComputableInPolyTime` on
functions between `BitstringEncoding` types, its generic closure properties, and the concrete
single-tape Turing machines witnessing computability of the operations on encoded pairs
(`takeFirstBlock`, `undelimitBlock`, `tagBlock`) and the symmetric monoidal structure maps.
-/
