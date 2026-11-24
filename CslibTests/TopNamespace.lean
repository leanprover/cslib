import Cslib.Foundations.Lint.Basic
import Batteries.Tactic.Lint.Frontend

/-! Tests for the `topNamespace` environment linter. -/

namespace CslibTests.TopNamespace

/-- A public declaration under a namespace. -/
def namespacedDef : Nat := 0

/-- A private declaration under a namespace. -/
private def namespacedPrivateDef : Nat := 0

end CslibTests.TopNamespace

/-- A declaration extending a namespace from upstream (core), as `_root_.Equivalence.foo` would. -/
theorem Equivalence.topNamespaceTestUpstream : True := trivial

/-- A declaration under a new top-level namespace that exists nowhere upstream. -/
def TopNamespaceTestNewRoot.foo : Nat := 0

/-- A declaration that is not under any namespace. -/
def topNamespaceTestNotNamespaced : Nat := 0

/--
A private declaration that is not under any namespace. Private declarations are skipped,
since they are not exported (and their internal name starts with `_private`).
-/
private def topNamespaceTestPrivateNotNamespaced : Nat := 0

/--
error: -- Found 2 errors in 6 declarations (plus 0 automatically generated ones) in the current file with 1 linters

/- The `topNamespace` linter reports:
TOP LEVEL DECLARATIONS:
This linter can be disabled with `@[nolint topNamespace]`. -/
#check TopNamespaceTestNewRoot.foo /- is not namespaced. -/
#check topNamespaceTestNotNamespaced /- is not namespaced. -/
-/
#guard_msgs in
#lint only topNamespace
