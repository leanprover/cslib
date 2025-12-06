/-
# Type soundness of System F<:

This mechanizes type soundness for System F<: using intrinsically scoped de Bruijn indices
and context morphisms.

The formalization uses intrinsically scoped de Bruijn indices.
De Bruijn indices are indexed by signatures describing available binders in the type context.
Syntactic constructs are well-scoped by construction.

Context morphisms are mappings between type contexts that preserve types.
All theorems concerning context operations (weakening, narrowing, substitution)
are proven uniformly using these morphisms.

Two kinds of context morphisms exist:

Rebinding morphisms map each `x:T ∈ Γ` to a corresponding binder `f(x) : f(T) ∈ Δ`.
Typing is preserved under rebinding morphisms.

Retyping morphisms map each `x: T ∈ Γ` to a typing derivation `Δ ⊢ g(x) : g(T)`.
This is stronger than rebinding morphisms.
The proof builds on rebinding morphism preservation.

This infrastructure enables proofs for context manipulation operations including
weakening, narrowing, substitution, and any context operations expressible as context morphisms.
-/

-- This module defines the intrinsically scoped de Bruijn indices.
import Cslib.Computability.LambdaCalculus.WellScoped.FSub.Debruijn

-- The following modules define Syetem F<:.
import Cslib.Computability.LambdaCalculus.WellScoped.FSub.Syntax
import Cslib.Computability.LambdaCalculus.WellScoped.FSub.TypeSystem
import Cslib.Computability.LambdaCalculus.WellScoped.FSub.Reduce
import Cslib.Computability.LambdaCalculus.WellScoped.FSub.Eval

-- The following defines parallel substitution and proves its properties.
import Cslib.Computability.LambdaCalculus.WellScoped.FSub.Substitution.Core
import Cslib.Computability.LambdaCalculus.WellScoped.FSub.Substitution.Properties

-- The following modules define context morphisms and prove their theory.
import Cslib.Computability.LambdaCalculus.WellScoped.FSub.RebindTheory.Core
import Cslib.Computability.LambdaCalculus.WellScoped.FSub.RebindTheory.TypeSystem
import Cslib.Computability.LambdaCalculus.WellScoped.FSub.RetypeTheory.Core
import Cslib.Computability.LambdaCalculus.WellScoped.FSub.RetypeTheory.TypeSystem

-- Main type soundness results.
import Cslib.Computability.LambdaCalculus.WellScoped.FSub.TypeSoundness.Preservation
import Cslib.Computability.LambdaCalculus.WellScoped.FSub.TypeSoundness.Progress
