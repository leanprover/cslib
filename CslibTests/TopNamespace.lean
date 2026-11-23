import Cslib.Foundations.Lint.Basic
import Batteries.Tactic.Lint.Frontend

/-! Tests for the `topNamespace` environment linter. -/

namespace CslibTests.TopNamespace

/-- A public declaration under a namespace. -/
def namespacedDef : Nat := 0

/-- A private declaration under a namespace. -/
private def namespacedPrivateDef : Nat := 0

end CslibTests.TopNamespace

/-- A declaration that is not under any namespace. -/
def topNamespaceTestNotNamespaced : Nat := 0

/--
A private declaration that is not under any namespace. Private declarations are skipped,
since they are not exported (and their internal name starts with `_private`).
-/
private def topNamespaceTestPrivateNotNamespaced : Nat := 0

/--
error: -- Found 1 error in 4 declarations (plus 0 automatically generated ones) in the current file with 1 linters

/- The `topNamespace` linter reports:
TOP LEVEL DECLARATIONS:
This linter can be disabled with `@[nolint topNamespace]`. -/
#check topNamespaceTestNotNamespaced /- is not namespaced. -/
-/
#guard_msgs in
#lint only topNamespace
