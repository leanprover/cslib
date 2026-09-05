# Machine transformations

These modules describe executable machines and their effects on configurations and `runFrom`.

- `Basic` changes a configuration's control state without changing its tapes.
- `Sequential` runs machines with the same work-tape count consecutively. The first halting
  transition hands its tapes, head positions, and accumulated output to the second machine.
- `ExtendTapes` places a machine's tapes along any injection. Time is unchanged; each unused tape
  contributes one visited cell to space. Arbitrary data on unused tapes is preserved.
- `OutputToWorkTape` redirects output to one fresh tape, including the symbol on a halting step.
- `InputFromWorkTape` simulates the native input on a work tape, preserving boundary clamping.
- `Rewind` shares one controller between native-input and work-tape rewinding. Work-tape rewind
  starts immediately after contiguous contents and finishes at their first cell, including when empty.
- `Composition` assembles output redirection, work-tape rewind, and input substitution with `seq`
  and tape injections, then proves operational and resource bounds.

These machines preserve the alphabet. Their run statements also specify the intermediate states
and tape contents needed when using them inside larger machines. Function-level complexity
statements belong in [Combinators](../Combinators); halting normal forms belong in
[NormalForms](../NormalForms).
