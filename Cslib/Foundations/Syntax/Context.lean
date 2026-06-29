/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Init

/-! Typeclasses for contexts, with heterogeneous and homogeneous variants. -/

@[expose] public section

namespace Cslib

/-- Class for types with a canonical notion of heterogeneous single-hole contexts. -/
class HasHContext (α β : Type*) where
  /-- The type of contexts. -/
  Context : Type*
  /-- Replaces the hole in the context with a value, resulting in a new value. -/
  fill (c : Context) (b : β) : α

@[inherit_doc] notation:max c "<[" t "]" => HasHContext.fill c t

/-- Class for types (`α`) that have a canonical notion of homogeneous single-hole contexts
(`Context`). -/
abbrev HasContext (α : Type*) := HasHContext α α

@[inherit_doc HasHContext.Context]
def HasContext.Context (α : Type*) [HasContext α] : Type* := HasHContext.Context α α

end Cslib
