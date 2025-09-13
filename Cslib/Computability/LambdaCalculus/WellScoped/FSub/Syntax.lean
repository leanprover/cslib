/-
# System F<: syntax

This module aggregates all the syntactic components of System F<:.

## Components:
- `Core`: Basic types and expressions with their renaming operations
- `Context`: Typing contexts and variable lookup relations
- `Subst`: Substitution operations and their lifting under binders
-/

import Cslib.Computability.LambdaCalculus.WellScoped.FSub.Syntax.Core
import Cslib.Computability.LambdaCalculus.WellScoped.FSub.Syntax.Context
import Cslib.Computability.LambdaCalculus.WellScoped.FSub.Syntax.Subst
