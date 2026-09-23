/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Init
public import Mathlib.Data.Multiset.AddSub
public import Mathlib.Data.Multiset.Replicate

/-! # Grind support for multisets

Use `grind [multiset]` (or `grind only [multiset]`) to reason about multisets or their list
representations. Importing this module does not add rules to the default `grind` set.
-/

public section

namespace Cslib

attribute [multiset _=_] Multiset.cons_coe Multiset.coe_add Multiset.singleton_add
  Multiset.coe_eq_coe
attribute [multiset =] Multiset.insert_eq_cons Multiset.coe_replicate
attribute [multiset =] Multiset.cons_add Multiset.add_cons
attribute [multiset =] Multiset.mem_cons Multiset.mem_add
attribute [multiset =] Multiset.add_comm Multiset.add_assoc
attribute [multiset =] Multiset.add_right_inj Multiset.add_left_inj
attribute [multiset =] Multiset.zero_add Multiset.add_zero
attribute [multiset .] Multiset.le_add_left Multiset.le_add_right
attribute [multiset =] Multiset.replicate_succ

end Cslib
