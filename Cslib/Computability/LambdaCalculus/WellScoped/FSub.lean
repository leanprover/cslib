/-
# Type soundness of System F<:

This is a mechanized type soundness proof of System F<: in what I call _well-scoped_ style.

The main idea is to:
- Use intrinsically scoped de Bruijn indices. Specifically, de Bruijn indices are indexed by a signature describing available binders in the type context. This way, syntactic constructs are well-scoped (and therefore well-formed) by construction.
- Use context morphisms, which are mappings between type contexts that preserve types. This way, all theorems concerning context operations (weakening, narrowing, substitution) can be proven in a uniform way.

There are two kinds of context morphisms where the latter depends on the former.
- The first is _rebinding morphisms_. A rebinding morphism `f` from `Γ` to `Δ` maps each `x:T ∈ Γ` to a corresponding binder `f(x) : f(T) ∈ Δ`. Then, we show that typing is preserved under such morphisms.
- The second is _retypeing morphisms_. A retypeing morphism `g` from `Γ` to `Δ` maps each `x: T ∈ Γ` into a typing derivation `Δ ⊢ g(x) : g(T)`. This is of course stronger than the first kind, and its proof relies on that of the first kind. We show that typing is preserved under this kind of morphisms too.

With this context morphism infrastructure, we can prove a variety of theorems regarding context manipulation, including weakening, narrowing, substitution, and any other context operations that can be formulated as a context morphism.
-/

-- This module defines the intrinsically scoped de Bruijn indices.
import Cslib.Computability.LambdaCalculus.WellScoped.FSub.Debruijn

-- The following modules define Syetem F<:.
import Cslib.Computability.LambdaCalculus.WellScoped.FSub.Syntax
import Cslib.Computability.LambdaCalculus.WellScoped.FSub.TypeSystem
import Cslib.Computability.LambdaCalculus.WellScoped.FSub.Reduce

-- The following modules define context morphisms and prove their theory.
import Cslib.Computability.LambdaCalculus.WellScoped.FSub.RebindTheory.Core
import Cslib.Computability.LambdaCalculus.WellScoped.FSub.RebindTheory.TypeSystem
import Cslib.Computability.LambdaCalculus.WellScoped.FSub.RetypeTheory.Core
import Cslib.Computability.LambdaCalculus.WellScoped.FSub.RetypeTheory.TypeSystem

-- Main type soundness results.
import Cslib.Computability.LambdaCalculus.WellScoped.FSub.TypeSoundness.Preservation
import Cslib.Computability.LambdaCalculus.WellScoped.FSub.TypeSoundness.Progress
