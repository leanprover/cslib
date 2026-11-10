/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Init
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.SDiff
public import Mathlib.Data.Finset.Image

/-! # Membership annotations -/

public section

namespace Cslib

attribute [membership =] Finset.mem_singleton Finset.mem_union Finset.mem_inter Finset.mem_sdiff
  Finset.mem_insert Finset.mem_image
attribute [membership .] Finset.mem_of_subset Finset.mem_image_of_mem Finset.mem_insert_self
  Finset.mem_insert_of_mem Finset.mem_image_of_mem
attribute [membership .] Finset.notMem_empty

attribute [membership .] Set.mem_image_of_mem

end Cslib
