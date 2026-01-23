/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Init

@[expose] public section

namespace Cslib

/-- Class for types (`Term`) that have a notion of (single-hole) contexts (`Context`). -/
class HasContext (Term : Sort*) where
  /-- The type of contexts. -/
  Context : Sort*
  /-- Replaces the hole in the context with a term. -/
  fill (c : Context) (t : Term) : Term

@[inherit_doc] notation:max c "[" t "]" => HasContext.fill c t

end Cslib
