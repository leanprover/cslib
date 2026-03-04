/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Init

@[expose] public section

namespace Cslib

/-- Class for types with a canonical notion of heterogeneous single-hole contexts. -/
class HasHContext (α : Type u) (β : Type v) where
  /-- The type of contexts. -/
  Context : Type*
  /-- Replaces the hole in the context with a value, resulting in a new value. -/
  fill (c : Context) (b : β) : α

@[inherit_doc] notation:max c "<[" t "]" => HasHContext.fill c t

/-- Class for types (`α`) that have a canonical notion of homogeneous single-hole contexts
(`Context`). -/
class HasContext (α : Type*) where
  /-- The type of contexts. -/
  Context : Type*
  /-- Replaces the hole in the context with a term. -/
  fill (c : Context) (a : α) : α

instance [inst : HasContext α] : HasHContext α α := ⟨inst.Context, inst.fill⟩

end Cslib
