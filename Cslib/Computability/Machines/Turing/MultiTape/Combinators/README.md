# Complexity of functions

The primary bounds depend on the actual input, with separate encodings for the input and output
of a function. `ComputableInTimeAndSpace` hides the realizing machine and fixes the machine
alphabet to `Bool`; `ComputesFunInTimeAndSpace` exposes a realization over an arbitrary alphabet.
`ComputableInTimeAndSpaceOfLength` specializes bounds to the encoded input length.

`Comp` proves that if `f` and `g` are computable, then so is `g ∘ f`, with time
`tf a + (encB (f a)).length + 3 + 2 * tg (f a)` and space
`sf a + (encB (f a)).length + 2 + sg (f a)`. This pointwise theorem requires no monotonicity.
A separate corollary derives length-based bounds from an intermediate-length bound and
monotonicity of the second function's bounds.

The executable transformations and their `runFrom` proofs live in [Plumbing](../Plumbing).
