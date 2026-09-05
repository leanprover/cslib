# Machine transformations

These modules describe executable machines and their effects on configurations and `runFrom`.

- `Basic` changes a configuration's control state without changing its tapes.
- `Sequential` runs machines with the same work-tape count consecutively. The first halting
  transition hands its tapes, head positions, and accumulated output to the second machine.
- `ExtendTapes` places a machine's tapes along any injection. Time is unchanged; each unused tape
  contributes one visited cell to space. Arbitrary data on unused tapes is preserved.
