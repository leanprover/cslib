/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

import Cslib

set_option linter.hashCommand false

namespace CslibTests

/-! Failing linters. Some (but not all!) may be too strict for practical use. -/

-- #lint- only explicitVarsOfIff in Cslib
-- #lint- only docBlame in Cslib
-- #lint- only docBlameThm in Cslib

/-! Passing linters. -/

#lint- only simpNF in Cslib
#lint- only simpComm in Cslib
#lint- only defLemma in Cslib
#lint- only nonClassInstance in Cslib
#lint- only impossibleInstance in Cslib
#lint- only unusedArguments in Cslib
#lint- only topNamespace in Cslib
#lint- only synTaut in Cslib
#lint- only checkType in Cslib
#lint- only simpVarHead in Cslib
#lint- only unusedHavesSuffices in Cslib
#lint- only dupNamespace in Cslib
#lint- only checkUnivs in Cslib

end CslibTests
