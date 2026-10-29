import Cslib.Foundations.Syntax.HasSubstitution

namespace CslibTests
namespace HasSubstitution

/-- Regression test for leanprover/cslib#631.

Before the notation was guarded by `noWs`, the parser tried to read the instance
binder below as part of a substitution expression attached to `Type`.
-/
structure InstanceBinderAfterField where
  A : Type
  [inst : Inhabited A]

instance : Cslib.HasSubstitution Nat Nat Nat where
  subst t _ _ := t

example : (1[2 := 3]) = 1 := rfl

end HasSubstitution
end CslibTests
